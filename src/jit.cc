#include <string>

#include "asmjit/asmjit.h"
#include "gflags/gflags.h"
#include "glog/logging.h"
#include "jit.h"
#include "utils.h"

#include "PatchCFG.h"

using namespace asmjit::x86;

DECLARE_bool(optimize_regs);
DECLARE_bool(validate_frame);
DECLARE_string(shadow_stack);
DECLARE_string(dry_run);

static std::map<std::string, Gp> kRegisterMap = {
    {"x86_64::rax", rax}, {"x86_64::rbx", rbx}, {"x86_64::rcx", rcx},
    {"x86_64::rdx", rdx}, /*{"x86_64::rsp", rsp},*/ {"x86_64::rbp", rbp},
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

  TempRegisters(std::set<std::string> exclude = {}, int height = 0)
      : tmp1_saved(true), tmp2_saved(true), tmp3_saved(true),
        sp_offset(height /* flag saving always takes 8 bytes */) {
    int count = 0;
    for (auto it : kRegisterMap) {
      auto rit = exclude.find(it.first);
      if (rit == exclude.end()) {
        switch (count) {
        case 0:
          tmp1 = it.second;
          break;
        case 1:
          tmp2 = it.second;
          break;
        case 2:
          tmp3 = it.second;
          break;
        }
        count++;
      }

      if (count == 2)
        break;
    }

    DCHECK(count == 2);
  }

  TempRegisters(MoveInstData * mid, int height) {
    sp_offset = mid->raOffset + height;
    tmp1_saved = false;
    tmp1 = kRegisterMap[mid->reg1];
    if (mid->saveCount == 2) {
      tmp2_saved = false;
      tmp2 = kRegisterMap[mid->reg2];
    } else {
      tmp2_saved = true;
      auto it = kRegisterMap.begin();
      if (it->first == mid->reg1) ++it;
      tmp2 = it->second;
    }
    tmp3_saved = true;
  }
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

TempRegisters UseSpecifiedRegisters(Assembler *a, MoveInstData* mid, int height = 0) {
    TempRegisters t(mid, height);
    if (t.tmp1_saved) Save(a, &t, &t.tmp1);
    if (t.tmp2_saved) Save(a, &t, &t.tmp2);
    return t;
}

TempRegisters SaveTempRegisters(Assembler* a,
                                std::set<std::string>& dead_registers,
                                std::set<std::string> exclude = {},
                                int height = 0) {
  TempRegisters t(exclude, height);
  if ((FLAGS_optimize_regs && dead_registers.empty()) || !FLAGS_optimize_regs) {
    Save(a, &t, &t.tmp1);
    Save(a, &t, &t.tmp2);
    // Save(a, &t, &t.tmp3);
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
    // a->pop(t.tmp3);
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
  //
  //   pushfq
  //   mov 0x16(%rsp),%rcx
  //   mov %gs:0x0, %rax
  //   addq $0x8, %gs:0x0
  //   mov %rcx, (%rax)
  //   popfq
  a->mov(ra_reg, ptr(rsp, t.sp_offset));
  a->mov(sp_reg, shadow_ptr);
  a->mov(ptr(sp_reg), ra_reg);
  a->lea(sp_reg, ptr(sp_reg, 8));
  a->mov(shadow_ptr, sp_reg);
}

void SaveRaAndFrame(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                    const Gp& ra_reg, const TempRegisters& t, Assembler* a) {
  // Assembly:
  //
  //   pushfq
  //   mov 0x16(%rsp),%rcx
  //   mov %gs:0x0, %rax
  //   addq $0x16, %gs:0x0
  //   mov %rcx, (%rax)
  //   leaq rcx, 0x10(%rsp)
  //   mov %rcx, 0x8(%rax)
  //   popfq
  a->pushfq();
  a->mov(ra_reg, ptr(rsp, t.sp_offset));
  a->mov(sp_reg, shadow_ptr);
  a->add(shadow_ptr, asmjit::imm(16));
  a->mov(ptr(sp_reg), ra_reg);
  a->lea(ra_reg, ptr(rsp, 24));
  a->mov(ptr(sp_reg, 8), ra_reg);
  a->popfq();
}

std::string JitStackPush(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                         AssemblerHolder& ah, bool useOriginalCode, int height, bool useOriginalCodeFixed) {
  if (FLAGS_dry_run == "empty") return "";
  Assembler* a = ah.GetAssembler();
  TempRegisters t;
  MoveInstData* mid = nullptr;
  if (useOriginalCode) {
      Address blockEntry = pt->block()->start();
      mid = s->getMoveInstDataAtEntry(blockEntry);
  } else if (useOriginalCodeFixed) {
      Address blockEntry = pt->edge()->trg()->start();
      mid = s->getMoveInstDataFixedAtEntry(blockEntry);
  }
  
  if (mid != nullptr) {
      t = UseSpecifiedRegisters(a, mid, height);
  } else if (s != nullptr) {
    t = SaveTempRegisters(a, s->dead_at_entry, {}, height);
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
  if (FLAGS_dry_run != "only-save") {
    if (FLAGS_validate_frame) {
      SaveRaAndFrame(shadow_ptr, sp_reg, ra_reg, t, a);
    } else {
      SaveRa(shadow_ptr, sp_reg, ra_reg, t, a);
    }
  }

  RestoreTempRegisters(a, t);

  return "";
}

void ValidateRa(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                const Gp& ra_reg, const TempRegisters& t, Assembler* a,
                bool save_flags = true) {
  asmjit::Label error = a->newLabel();
  asmjit::Label done = a->newLabel();
  asmjit::Label loop = a->newLabel();

  // Assembly:
  //
  //   [pushfq]
  //   mov %gs:0x0,%rax
  // loop:
  //   mov -0x8(%rax), %rcx
  //   subq $0x8, %gs:0x0
  //   cmp 0x16(%rsp), %rcx
  //   je done
  //   sub $0x8, %rax
  //   cmpl $0x0, (%rax)
  //   je error
  //   jmp loop
  // error:
  //   int3 | sigill
  // done:
  //   [popfq]

  a->mov(sp_reg, shadow_ptr);

  a->bind(loop);
  a->lea(sp_reg, ptr(sp_reg, -8));
  a->mov(ra_reg, ptr(sp_reg));
  a->mov(shadow_ptr, sp_reg);
  a->cmp(ra_reg, ptr(rsp, t.sp_offset));
  a->je(done);

  a->cmp(dword_ptr(sp_reg), 0);
  a->je(error);

  a->jmp(loop);

  a->bind(error);
  // Cause a SIGILL instead of SIGTRAP to ease debuggability with GDB.
  const char sigill = 0x62;
  a->embed(&sigill, sizeof(char));

  a->bind(done);
}

void ValidateRaAndFrame(const asmjit::x86::Mem& shadow_ptr, const Gp& sp_reg,
                        const Gp& ra_reg, const TempRegisters& t,
                        Assembler* a) {
  asmjit::Label error = a->newLabel();
  asmjit::Label done = a->newLabel();
  asmjit::Label loop = a->newLabel();
  asmjit::Label unwind = a->newLabel();

  // Assembly:
  //
  //   pushfq
  //   mov %gs:0x0,%rax
  // loop:
  //   mov -0x10(%rax), %rcx
  //   subq $0x10, %gs:0x0
  //   cmp 0x16(%rsp), %rcx
  //   jne unwind
  //   leaq 0x16(%rsp), %rcx
  //   cmp -0x8(%rax), %rcx
  //   je success
  // unwind:
  //   sub $0x10, %rax
  //   cmpl $0x0, (%rax)
  //   je error
  //   jmp loop
  // error:
  //   int3 | sigill
  // done:
  //   popfq
  //   pop ...
  //   retq
  a->pushfq();
  a->mov(sp_reg, shadow_ptr);

  a->bind(loop);
  a->mov(ra_reg, ptr(sp_reg, -16));
  a->sub(shadow_ptr, asmjit::imm(16));
  a->cmp(ra_reg, ptr(rsp, t.sp_offset));
  a->jne(unwind);
  a->lea(ra_reg, ptr(rsp, t.sp_offset));
  a->cmp(ra_reg, ptr(sp_reg, -8));
  a->je(done);

  a->bind(unwind);
  a->sub(sp_reg, asmjit::imm(16));
  a->cmp(dword_ptr(sp_reg), 0);
  a->je(error);
  a->jmp(loop);

  a->bind(error);
  // Cause a SIGILL instead of SIGTRAP to ease debuggability with GDB.
  const char sigill = 0x62;
  a->embed(&sigill, sizeof(char));

  a->bind(done);
  a->popfq();
}

std::string JitStackPop(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                        AssemblerHolder& ah, bool useOriginalCode, int, bool) {
  if (FLAGS_dry_run == "empty") return "";
  Assembler* a = ah.GetAssembler();

  TempRegisters t;
  MoveInstData* mid = nullptr;
  if (useOriginalCode) {
      Address blockEntry = pt->block()->start();
      mid = s->getMoveInstDataAtExit(blockEntry);
  }
  
  if (mid != nullptr) {
      t = UseSpecifiedRegisters(a, mid);
  } else if (s != nullptr) {
    auto it = s->dead_at_exit.find(pt->addr());
    if (it != s->dead_at_exit.end()) {
      t = SaveTempRegisters(a, it->second);
    } else {
      std::set<std::string> dead;
      t = SaveTempRegisters(a, dead);
    }
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
  if (FLAGS_dry_run != "only-save") {
    if (FLAGS_validate_frame) {
      ValidateRaAndFrame(shadow_ptr, sp_reg, ra_reg, t, a);
    } else {
      ValidateRa(shadow_ptr, sp_reg, ra_reg, t, a);
    }
  }

  RestoreTempRegisters(a, t);

  return "";
}

std::pair<std::string, Gp> GetUnusedRegister(FuncSummary* s) {
  DCHECK(s->unused_regs.size() > 0);
  auto it = s->unused_regs.cbegin();

  auto rit = kRegisterMap.find(*it);
  DCHECK(rit != kRegisterMap.end());

  return std::make_pair(*it, rit->second);
}

std::string JitRegisterPush(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                            AssemblerHolder& ah, bool, int height, bool) {
  if (FLAGS_dry_run == "empty") return "";
  auto pair = GetUnusedRegister(s);
  Gp reg = pair.second;

  // Assembly:
  //
  //   push %<unused_reg>
  //   pushfq
  //   mov 0x10(%rsp),%<unused_reg>
  //   popfq
  Assembler* a = ah.GetAssembler();
  //a->push(reg);
  //a->pushfq();
  asmjit::x86::Mem scratch;
  scratch.setSize(8);
  scratch.setSegment(gs);
  scratch = scratch.cloneAdjusted(8);

  a->mov(scratch, reg);
  if (FLAGS_dry_run != "only-save")
    a->mov(reg, ptr(rsp, height));
  //a->popfq();

  return "";
}

std::string JitRegisterPop(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                           AssemblerHolder& ah, bool, int, bool) {
  if (FLAGS_dry_run == "empty") return "";
  // Here we rely on the fact that stl::set iteration order is deterministic
  // across multiple invocations (i.e: we will get the same register that we got
  // during stack push using the iterator).
  auto pair = GetUnusedRegister(s);
  std::string reg_str = pair.first;
  Gp reg = pair.second;

  // Assembly:
  //
  //   pushfq
  //   cmp %<unused_reg>, 0x10(%rsp)
  //   je success
  //   push %rcx                        ; begin stack unwinding
  //   push %rax
  //   mov %gs:0x0,%rax
  // loop:
  //   mov -0x8(%rax), %rcx
  //   subq $0x8, %gs:0x0
  //   cmp 0x20(%rsp), %rcx
  //   je done
  //   sub $0x8, %rax
  //   cmpl $0x0, (%rax)
  //   je error
  //   jmp loop
  // error:
  //   int3 | sigill
  // done:
  //   pop %rax
  //   pop %rcx                         ; end stack unwinding
  // success:
  //   popfq
  //   pop %<unused_reg>
  Assembler* a = ah.GetAssembler();
  if (FLAGS_dry_run != "only-save") {
    asmjit::Label success = a->newLabel();

    a->cmp(reg, ptr(rsp));
    a->je(success);

    // Fall through for stack unwind scenario.
    std::set<std::string> dead;
    TempRegisters t = SaveTempRegisters(a, dead, {reg_str});

    Gp sp_reg = t.tmp1;
    Gp ra_reg = t.tmp2;

    asmjit::x86::Mem shadow_ptr;
    shadow_ptr.setSize(8);
    shadow_ptr.setSegment(gs);
    shadow_ptr = shadow_ptr.cloneAdjusted(0);
    ValidateRa(shadow_ptr, sp_reg, ra_reg, t, a, false /* save_flags */);
    RestoreTempRegisters(a, t);

    a->bind(success);
  }
  asmjit::x86::Mem scratch;
  scratch.setSize(8);
  scratch.setSegment(gs);
  scratch = scratch.cloneAdjusted(8);
  a->mov(reg, scratch);
  return "";
}

std::string JitCallEmulatePush(Dyninst::PatchAPI::Point* pt, FuncSummary* s,
                               AssemblerHolder& ah, int height, bool useOriginalCodeFixed) {
  if (FLAGS_dry_run == "empty") return "";
  Assembler* a = ah.GetAssembler();
  TempRegisters t;
  MoveInstData* mid = nullptr;
  if (useOriginalCodeFixed) {
      Address blockEntry = pt->edge()->trg()->start();
      mid = s->getMoveInstDataFixedAtEntry(blockEntry);
  }    
  if (mid != nullptr && mid->saveCount > 0) {
    a->lea(kRegisterMap[mid->reg1], ptr(rip));
    t = UseSpecifiedRegisters(a, mid, height);
  } else {
    assert(!"save a GPR to shadow region");
    std::set<std::string> dead;
    t = SaveTempRegisters(a, dead);
  }

  Gp sp_reg = t.tmp1;
  Gp ra_reg = t.tmp2;

  asmjit::x86::Mem shadow_ptr;
  shadow_ptr.setSize(8);
  shadow_ptr.setSegment(gs);
  shadow_ptr = shadow_ptr.cloneAdjusted(0);
  if (FLAGS_dry_run != "only-save") {
    if (FLAGS_validate_frame) {
      SaveRaAndFrame(shadow_ptr, sp_reg, ra_reg, t, a);
    } else {
      SaveRa(shadow_ptr, sp_reg, ra_reg, t, a);
    }
  }

  RestoreTempRegisters(a, t);

  return "";
}


                            