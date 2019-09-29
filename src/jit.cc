
#include <string>

#include "asmjit/asmjit.h"
#include "gflags/gflags.h"
#include "jit.h"
#include "utils.h"

using namespace asmjit::x86;

DECLARE_bool(optimize_regs);
DECLARE_bool(validate_frame);

static std::map<std::string, Gp> kRegisterMap = {
    {"x86_64::rax", rax}, {"x86_64::rbx", rbx}, {"x86_64::rcx", rcx},
    {"x86_64::rdx", rdx}, {"x86_64::rsp", rsp}, {"x86_64::rbp", rbp},
    {"x86_64::rsi", rsi}, {"x86_64::rdi", rdi}, {"x86_64::r8", r8},
    {"x86_64::r9", r9},   {"x86_64::r10", r10}, {"x86_64::r11", r11},
    {"x86_64::r12", r12}, {"x86_64::r13", r13}, {"x86_64::r14", r14},
    {"x86_64::r15", r15}};

struct TempRegisters {
  Gp tmp1;
  Gp tmp2;
  Gp tmp3;
  bool tmp1_saved;
  bool tmp2_saved;
  bool tmp3_saved;
  int sp_offset;

  TempRegisters()
      : tmp1(rdx), tmp2(rcx), tmp3(rax), tmp1_saved(true), tmp2_saved(true),
        tmp3_saved(true), sp_offset(0) {}
};

void SaveOrSkip(Assembler* a, TempRegisters* t, std::string reg_str, Gp* reg,
                bool* saved) {
  auto it = kRegisterMap.find(reg_str);
  if (it != kRegisterMap.end()) {
    *reg = it->second;
    *saved = false;
  } else {
    a->push(*reg);
    t->sp_offset += 8;
  }
}

inline void Save(Assembler* a, TempRegisters* t, Gp* reg) {
  a->push(*reg);
  t->sp_offset += 8;
}

TempRegisters SaveTempRegisters(Assembler* a,
                                std::set<std::string>& dead_registers) {
  TempRegisters t;
  if ((FLAGS_optimize_regs && dead_registers.empty()) || !FLAGS_optimize_regs) {
    Save(a, &t, &t.tmp1);
    Save(a, &t, &t.tmp2);
    Save(a, &t, &t.tmp3);
  } else {
    auto reg = dead_registers.begin();
    if (reg++ != dead_registers.end()) {
      SaveOrSkip(a, &t, *reg, &t.tmp1, &t.tmp1_saved);
    } else {
      Save(a, &t, &t.tmp1);
    }

    if (reg++ != dead_registers.end()) {
      SaveOrSkip(a, &t, *reg, &t.tmp2, &t.tmp2_saved);
    } else {
      Save(a, &t, &t.tmp2);
    }

    if (reg++ != dead_registers.end()) {
      SaveOrSkip(a, &t, *reg, &t.tmp3, &t.tmp3_saved);
    } else {
      Save(a, &t, &t.tmp3);
    }
  }

  return t;
}

void RestoreTempRegisters(Assembler* a, TempRegisters t) {
  if (t.tmp3_saved) {
    a->pop(t.tmp3);
  }

  if (t.tmp2_saved) {
    a->pop(t.tmp2);
  }

  if (t.tmp1_saved) {
    a->pop(t.tmp1);
  }
}

void SaveRa(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
            const Gp& ra_reg, const TempRegisters& t, Assembler* a) {
  // Assembly:
  //   lahf
  //   mov 0x10(%rsp),%rcx
  //   mov %gs:0x0, %rax
  //   addq $0x8, %gs:0x0
  //   mov %rcx, (%rax)
  //   sahf

  a->lahf();
  a->mov(ra_reg, ptr(rsp, t.sp_offset));
  a->mov(sp_reg, shadow_ptr);
  a->add(shadow_ptr, asmjit::imm(8));
  a->mov(ptr(sp_reg), ra_reg);
  a->sahf();
}

void SaveRaAndFrame(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                    const Gp& ra_reg, const TempRegisters& t, Assembler* a) {
  // Assembly:
  //
  //   lahf
  //   mov 0x10(%rsp),%rcx
  //   mov %gs:0x0, %rax
  //   addq $0x16, %gs:0x0
  //   mov %rcx, (%rax)
  //   leaq rcx, 0x10(%rsp)
  //   mov %rcx, 0x8(%rax)
  //   sahf

  a->lahf();
  a->mov(ra_reg, ptr(rsp, t.sp_offset));
  a->mov(sp_reg, shadow_ptr);
  a->add(shadow_ptr, asmjit::imm(16));
  a->mov(ptr(sp_reg), ra_reg);
  a->lea(ra_reg, ptr(rsp, 24));
  a->mov(ptr(sp_reg, 8), ra_reg);
  a->sahf();
}

std::string JitStackPush(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                         AssemblerHolder& ah) {
  Assembler* a = ah.GetAssembler();

  TempRegisters t = SaveTempRegisters(a, s->dead_at_entry);

  Gp sp_reg = t.tmp1;
  Gp ra_reg = t.tmp2;

  asmjit::x86::Mem shadow_ptr;
  shadow_ptr.setSize(8);
  shadow_ptr.setSegment(gs);
  shadow_ptr = shadow_ptr.cloneAdjusted(0);

  if (FLAGS_validate_frame) {
    SaveRaAndFrame(shadow_ptr, sp_reg, ra_reg, t, a);
  } else {
    SaveRa(shadow_ptr, sp_reg, ra_reg, t, a);
  }

  RestoreTempRegisters(a, t);

  return "";
}

void ValidateRa(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                const Gp& ra_reg, const TempRegisters& t, Assembler* a) {
  asmjit::Label error = a->newLabel();
  asmjit::Label success = a->newLabel();
  asmjit::Label loop = a->newLabel();

  // Assembly:
  //
  //   lahf
  //   mov %gs:0x0,%rax
  // loop:
  //   mov -0x8(%rax), %rcx
  //   subq $0x8, %gs:0x0
  //   cmp 0x10(%rsp), %rcx
  //   je success
  //   sub $0x8, %rax
  //   cmpl $0x0, (%rax)
  //   je error
  //   jmp loop
  // error:
  //   int3 | sigill
  // success:
  //   sahf
  //   pop ...
  //   retq

  a->lahf();
  a->mov(sp_reg, shadow_ptr);

  a->bind(loop);
  a->mov(ra_reg, ptr(sp_reg, -8));
  a->sub(shadow_ptr, asmjit::imm(8));
  a->cmp(ra_reg, ptr(rsp, t.sp_offset));
  a->je(success);

  a->sub(sp_reg, asmjit::imm(8));
  a->cmp(dword_ptr(sp_reg), 0);
  a->je(error);

  a->jmp(loop);

  a->bind(error);
  // Cause a SIGILL instead of SIGTRAP to ease debuggability with GDB.
  const char sigill = 0x62;
  a->embed(&sigill, sizeof(char));

  a->bind(success);
  a->sahf();
}

void ValidateRaAndFrame(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                        const Gp& ra_reg, const TempRegisters& t,
                        Assembler* a) {
  asmjit::Label error = a->newLabel();
  asmjit::Label success = a->newLabel();
  asmjit::Label loop = a->newLabel();
  asmjit::Label unwind = a->newLabel();

  // Assembly:
  //
  //   lahf
  //   mov %gs:0x0,%rax
  // loop:
  //   mov -0x10(%rax), %rcx
  //   subq $0x10, %gs:0x0
  //   cmp 0x10(%rsp), %rcx
  //   jne unwind
  //   leaq 0x10(%rsp), %rcx
  //   cmp -0x8(%rax), %rcx
  //   je success
  // unwind:
  //   sub $0x10, %rax
  //   cmpl $0x0, (%rax)
  //   je error
  //   jmp loop
  // error:
  //   int3 | sigill
  // success:
  //   shaf
  //   pop ...
  //   retq

  a->lahf();
  a->mov(sp_reg, shadow_ptr);

  a->bind(loop);
  a->mov(ra_reg, ptr(sp_reg, -16));
  a->sub(shadow_ptr, asmjit::imm(16));
  a->cmp(ra_reg, ptr(rsp, t.sp_offset));
  a->jne(unwind);
  a->lea(ra_reg, ptr(rsp, t.sp_offset));
  a->cmp(ra_reg, ptr(sp_reg, -8));
  a->je(success);

  a->bind(unwind);
  a->sub(sp_reg, asmjit::imm(16));
  a->cmp(dword_ptr(sp_reg), 0);
  a->je(error);
  a->jmp(loop);

  a->bind(error);
  // Cause a SIGILL instead of SIGTRAP to ease debuggability with GDB.
  const char sigill = 0x62;
  a->embed(&sigill, sizeof(char));

  a->bind(success);
  a->sahf();
}

std::string JitStackPop(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                        AssemblerHolder& ah) {
  Assembler* a = ah.GetAssembler();

  TempRegisters t;
  auto it = s->dead_at_exit.find(pt->addr());
  if (it != s->dead_at_exit.end()) {
    t = SaveTempRegisters(a, it->second);
  } else {
    std::set<std::string> dead;
    t = SaveTempRegisters(a, dead);
  }

  Gp sp_reg = t.tmp1;
  Gp ra_reg = t.tmp2;

  asmjit::x86::Mem shadow_ptr;
  shadow_ptr.setSize(8);
  shadow_ptr.setSegment(gs);
  shadow_ptr = shadow_ptr.cloneAdjusted(0);

  if (FLAGS_validate_frame) {
    ValidateRaAndFrame(shadow_ptr, sp_reg, ra_reg, t, a);
  } else {
    ValidateRa(shadow_ptr, sp_reg, ra_reg, t, a);
  }

  RestoreTempRegisters(a, t);

  return "";
}
