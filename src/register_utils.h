
#ifndef LITECFI_REGISTER_UTILS_H_
#define LITECFI_REGISTER_UTILS_H_

#include "asmjit/asmjit.h"
#include "register_usage.h"

struct AvxRegister {
  // AVX portion
  asmjit::X86Xmm xmm;
  // AVX2 portion
  asmjit::X86Ymm ymm;
  // AVX512 portion
  asmjit::X86Zmm zmm;
};

AvxRegister GetNextUnusedAvx2Register(RegisterUsageInfo& info);
AvxRegister GetNextUnusedAvx512Register(RegisterUsageInfo& info);

std::vector<uint8_t> GetUnusedAvx2QuadWords(const RegisterUsageInfo& info);

std::vector<uint16_t> GetUnusedAvx512QuadWords(const RegisterUsageInfo& info);

#endif  // LITECFI_REGISTER_UTILS_H_