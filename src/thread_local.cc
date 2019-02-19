
#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

#ifdef __cplusplus
extern "C" {
#endif

static thread_local uint64_t* overflow_stack = nullptr;

static thread_local uint64_t* spill_stack = nullptr;

static thread_local uint64_t* ctx_save_stack = nullptr;

static void setup_memory(uint64_t** mem_ptr, long size) {
  // Add space for two guard pages at the beginning and the end of the stack
  int page_size = getpagesize();
  size += page_size * 2;

  *mem_ptr = (uint64_t*)mmap(0, size, PROT_READ | PROT_WRITE,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

  // Protect guard pages
  mprotect(*mem_ptr, page_size, PROT_NONE);
  mprotect(*mem_ptr + size - page_size, page_size, PROT_NONE);

  // Skip past the guard page at the beginning
  *mem_ptr += page_size;
}

void litecfi_mem_initialize() {
  long stack_size = pow(2, 16);  // Stack size = 2^16

  setup_memory(&overflow_stack, stack_size);
  setup_memory(&spill_stack, stack_size);
  setup_memory(&ctx_save_stack, stack_size);
}

// TODO(chamibuddhika) Implement this
void litecfi_overflow_stack_push(uint64_t value) {}

// TODO(chamibuddhika) Implement this
uint64_t litecfi_overflow_stack_pop() { return 0; }

#define OUT_OF_BOUNDS()           \
  default:                        \
    printf("Invalid register\n"); \
    assert(false);

// clang-format off
#define PUSH_AVX2(spill_stack, index, ymm_spill) \
  case index: {                                   \
    asm(ymm_spill                                 \
        "addq $256, %0;\n\t"                      \
        : "=m"(spill_stack)                       \
        : "a"(spill_stack)                        \
        :);                                       \
  }

#define POP_AVX2(spill_stack, index, ymm_restore) \
  case index: {                                       \
    asm(ymm_restore                                   \
        "subq $256, %0;\n\t"                          \
        : "=m"(spill_stack)                           \
        : "a"(spill_stack)                            \
        :);                                           \
  }

#define PEEK_AVX2(spill_stack, index, offset, ymm_peek) \
  case index: {                                         \
    asm("imul $256, %0;\n\t"                            \
        "movq %1, %%rdx;\n\t"                           \
        "sub %0, %%edx;\n\t"                           \
        ymm_peek                                        \
        :                                               \
        : "b"(offset), "a"(spill_stack)                 \
        : "rdx");                                       \
  }
// clang-format on

#define REGISTER_PUSH(index, sp)                    \
  switch (index) {                                  \
    PUSH_AVX2(sp, 0, "vmovdqu %%ymm0, (%1);\n\t")   \
    PUSH_AVX2(sp, 1, "vmovdqu %%ymm1, (%1);\n\t")   \
    PUSH_AVX2(sp, 2, "vmovdqu %%ymm2, (%1);\n\t")   \
    PUSH_AVX2(sp, 3, "vmovdqu %%ymm3, (%1);\n\t")   \
    PUSH_AVX2(sp, 4, "vmovdqu %%ymm4, (%1);\n\t")   \
    PUSH_AVX2(sp, 5, "vmovdqu %%ymm5, (%1);\n\t")   \
    PUSH_AVX2(sp, 6, "vmovdqu %%ymm6, (%1);\n\t")   \
    PUSH_AVX2(sp, 7, "vmovdqu %%ymm7, (%1);\n\t")   \
    PUSH_AVX2(sp, 8, "vmovdqu %%ymm8, (%1);\n\t")   \
    PUSH_AVX2(sp, 9, "vmovdqu %%ymm9, (%1);\n\t")   \
    PUSH_AVX2(sp, 10, "vmovdqu %%ymm10, (%1);\n\t") \
    PUSH_AVX2(sp, 11, "vmovdqu %%ymm11, (%1);\n\t") \
    PUSH_AVX2(sp, 12, "vmovdqu %%ymm12, (%1);\n\t") \
    PUSH_AVX2(sp, 13, "vmovdqu %%ymm13, (%1);\n\t") \
    PUSH_AVX2(sp, 14, "vmovdqu %%ymm14, (%1);\n\t") \
    PUSH_AVX2(sp, 15, "vmovdqu %%ymm15, (%1);\n\t") \
    OUT_OF_BOUNDS()                                 \
  }

#define REGISTER_POP(index, sp)                    \
  switch (index) {                                 \
    POP_AVX2(sp, 0, "vmovdqu (%1), %%ymm0;\n\t")   \
    POP_AVX2(sp, 1, "vmovdqu (%1), %%ymm1;\n\t")   \
    POP_AVX2(sp, 2, "vmovdqu (%1), %%ymm2;\n\t")   \
    POP_AVX2(sp, 3, "vmovdqu (%1), %%ymm3;\n\t")   \
    POP_AVX2(sp, 4, "vmovdqu (%1), %%ymm4;\n\t")   \
    POP_AVX2(sp, 5, "vmovdqu (%1), %%ymm5;\n\t")   \
    POP_AVX2(sp, 6, "vmovdqu (%1), %%ymm6;\n\t")   \
    POP_AVX2(sp, 7, "vmovdqu (%1), %%ymm7;\n\t")   \
    POP_AVX2(sp, 8, "vmovdqu (%1), %%ymm8;\n\t")   \
    POP_AVX2(sp, 9, "vmovdqu (%1), %%ymm9;\n\t")   \
    POP_AVX2(sp, 10, "vmovdqu (%1), %%ymm10;\n\t") \
    POP_AVX2(sp, 11, "vmovdqu (%1), %%ymm11;\n\t") \
    POP_AVX2(sp, 12, "vmovdqu (%1), %%ymm12;\n\t") \
    POP_AVX2(sp, 13, "vmovdqu (%1), %%ymm13;\n\t") \
    POP_AVX2(sp, 14, "vmovdqu (%1), %%ymm14;\n\t") \
    POP_AVX2(sp, 15, "vmovdqu (%1), %%ymm15;\n\t") \
    OUT_OF_BOUNDS()                                \
  }

#define REGISTER_PEEK(index, sp, offset)                       \
  switch (index) {                                             \
    PEEK_AVX2(sp, 0, offset, "vmovdqu (%%rdx), %%ymm0;\n\t")   \
    PEEK_AVX2(sp, 1, offset, "vmovdqu (%%rdx), %%ymm1;\n\t")   \
    PEEK_AVX2(sp, 2, offset, "vmovdqu (%%rdx), %%ymm2;\n\t")   \
    PEEK_AVX2(sp, 3, offset, "vmovdqu (%%rdx), %%ymm3;\n\t")   \
    PEEK_AVX2(sp, 4, offset, "vmovdqu (%%rdx), %%ymm4;\n\t")   \
    PEEK_AVX2(sp, 5, offset, "vmovdqu (%%rdx), %%ymm5;\n\t")   \
    PEEK_AVX2(sp, 6, offset, "vmovdqu (%%rdx), %%ymm6;\n\t")   \
    PEEK_AVX2(sp, 7, offset, "vmovdqu (%%rdx), %%ymm7;\n\t")   \
    PEEK_AVX2(sp, 8, offset, "vmovdqu (%%rdx), %%ymm8;\n\t")   \
    PEEK_AVX2(sp, 9, offset, "vmovdqu (%%rdx), %%ymm9;\n\t")   \
    PEEK_AVX2(sp, 10, offset, "vmovdqu (%%rdx), %%ymm10;\n\t") \
    PEEK_AVX2(sp, 11, offset, "vmovdqu (%%rdx), %%ymm11;\n\t") \
    PEEK_AVX2(sp, 12, offset, "vmovdqu (%%rdx), %%ymm12;\n\t") \
    PEEK_AVX2(sp, 13, offset, "vmovdqu (%%rdx), %%ymm13;\n\t") \
    PEEK_AVX2(sp, 14, offset, "vmovdqu (%%rdx), %%ymm14;\n\t") \
    PEEK_AVX2(sp, 15, offset, "vmovdqu (%%rdx), %%ymm15;\n\t") \
    OUT_OF_BOUNDS()                                            \
  }

#define ONE_REG_PUSH_FN(fn, sp) \
  void fn##_1(int reg1) { REGISTER_PUSH(reg1, sp) }

#define TWO_REG_PUSH_FN(fn, sp)     \
  void fn##_2(int reg1, int reg2) { \
    REGISTER_PUSH(reg1, sp)         \
    REGISTER_PUSH(reg2, sp)         \
  }

#define THREE_REG_PUSH_FN(fn, sp)             \
  void fn##_3(int reg1, int reg2, int reg3) { \
    REGISTER_PUSH(reg1, sp)                   \
    REGISTER_PUSH(reg2, sp)                   \
    REGISTER_PUSH(reg3, sp)                   \
  }

#define FOUR_REG_PUSH_FN(fn, sp)                        \
  void fn##_4(int reg1, int reg2, int reg3, int reg4) { \
    REGISTER_PUSH(reg1, sp)                             \
    REGISTER_PUSH(reg2, sp)                             \
    REGISTER_PUSH(reg3, sp)                             \
    REGISTER_PUSH(reg4, sp)                             \
  }

#define FIVE_REG_PUSH_FN(fn, sp)                                  \
  void fn##_5(int reg1, int reg2, int reg3, int reg4, int reg5) { \
    REGISTER_PUSH(reg1, sp)                                       \
    REGISTER_PUSH(reg2, sp)                                       \
    REGISTER_PUSH(reg3, sp)                                       \
    REGISTER_PUSH(reg4, sp)                                       \
    REGISTER_PUSH(reg5, sp)                                       \
  }

#define SIX_REG_PUSH_FN(fn, sp)                                             \
  void fn##_6(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6) { \
    REGISTER_PUSH(reg1, sp)                                                 \
    REGISTER_PUSH(reg2, sp)                                                 \
    REGISTER_PUSH(reg3, sp)                                                 \
    REGISTER_PUSH(reg4, sp)                                                 \
    REGISTER_PUSH(reg5, sp)                                                 \
    REGISTER_PUSH(reg6, sp)                                                 \
  }

#define SEVEN_REG_PUSH_FN(fn, sp)                                         \
  void fn##_7(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7) {                                                 \
    REGISTER_PUSH(reg1, sp)                                               \
    REGISTER_PUSH(reg2, sp)                                               \
    REGISTER_PUSH(reg3, sp)                                               \
    REGISTER_PUSH(reg4, sp)                                               \
    REGISTER_PUSH(reg5, sp)                                               \
    REGISTER_PUSH(reg6, sp)                                               \
    REGISTER_PUSH(reg7, sp)                                               \
  }

#define EIGHT_REG_PUSH_FN(fn, sp)                                         \
  void fn##_8(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7, int reg8) {                                       \
    REGISTER_PUSH(reg1, sp)                                               \
    REGISTER_PUSH(reg2, sp)                                               \
    REGISTER_PUSH(reg3, sp)                                               \
    REGISTER_PUSH(reg4, sp)                                               \
    REGISTER_PUSH(reg5, sp)                                               \
    REGISTER_PUSH(reg6, sp)                                               \
    REGISTER_PUSH(reg7, sp)                                               \
    REGISTER_PUSH(reg8, sp)                                               \
  }

#define ONE_REG_POP_FN(fn, sp) \
  void fn##_1(int reg1) { REGISTER_POP(reg1, sp) }

#define TWO_REG_POP_FN(fn, sp)      \
  void fn##_2(int reg1, int reg2) { \
    REGISTER_POP(reg1, sp)          \
    REGISTER_POP(reg2, sp)          \
  }

#define THREE_REG_POP_FN(fn, sp)              \
  void fn##_3(int reg1, int reg2, int reg3) { \
    REGISTER_POP(reg1, sp)                    \
    REGISTER_POP(reg2, sp)                    \
    REGISTER_POP(reg3, sp)                    \
  }

#define FOUR_REG_POP_FN(fn, sp)                         \
  void fn##_4(int reg1, int reg2, int reg3, int reg4) { \
    REGISTER_POP(reg1, sp)                              \
    REGISTER_POP(reg2, sp)                              \
    REGISTER_POP(reg3, sp)                              \
    REGISTER_POP(reg4, sp)                              \
  }

#define FIVE_REG_POP_FN(fn, sp)                                   \
  void fn##_5(int reg1, int reg2, int reg3, int reg4, int reg5) { \
    REGISTER_POP(reg1, sp)                                        \
    REGISTER_POP(reg2, sp)                                        \
    REGISTER_POP(reg3, sp)                                        \
    REGISTER_POP(reg4, sp)                                        \
    REGISTER_POP(reg5, sp)                                        \
  }

#define SIX_REG_POP_FN(fn, sp)                                              \
  void fn##_6(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6) { \
    REGISTER_POP(reg1, sp)                                                  \
    REGISTER_POP(reg2, sp)                                                  \
    REGISTER_POP(reg3, sp)                                                  \
    REGISTER_POP(reg4, sp)                                                  \
    REGISTER_POP(reg5, sp)                                                  \
    REGISTER_POP(reg6, sp)                                                  \
  }

#define SEVEN_REG_POP_FN(fn, sp)                                          \
  void fn##_7(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7) {                                                 \
    REGISTER_POP(reg1, sp)                                                \
    REGISTER_POP(reg2, sp)                                                \
    REGISTER_POP(reg3, sp)                                                \
    REGISTER_POP(reg4, sp)                                                \
    REGISTER_POP(reg5, sp)                                                \
    REGISTER_POP(reg6, sp)                                                \
    REGISTER_POP(reg7, sp)                                                \
  }

#define EIGHT_REG_POP_FN(fn, sp)                                          \
  void fn##_8(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7, int reg8) {                                       \
    REGISTER_POP(reg1, sp)                                                \
    REGISTER_POP(reg2, sp)                                                \
    REGISTER_POP(reg3, sp)                                                \
    REGISTER_POP(reg4, sp)                                                \
    REGISTER_POP(reg5, sp)                                                \
    REGISTER_POP(reg6, sp)                                                \
    REGISTER_POP(reg7, sp)                                                \
    REGISTER_POP(reg8, sp)                                                \
  }

#define ONE_REG_PEEK_FN(fn, sp) \
  void fn##_1(int reg1, int offset) { REGISTER_PEEK(reg1, sp, offset) }

#define TWO_REG_PEEK_FN(fn, sp)                 \
  void fn##_2(int reg1, int reg2, int offset) { \
    REGISTER_PEEK(reg1, sp, offset)             \
    REGISTER_PEEK(reg2, sp, offset)             \
  }

#define THREE_REG_PEEK_FN(fn, sp)                         \
  void fn##_3(int reg1, int reg2, int reg3, int offset) { \
    REGISTER_PEEK(reg1, sp, offset)                       \
    REGISTER_PEEK(reg2, sp, offset)                       \
    REGISTER_PEEK(reg3, sp, offset)                       \
  }

#define FOUR_REG_PEEK_FN(fn, sp)                                    \
  void fn##_4(int reg1, int reg2, int reg3, int reg4, int offset) { \
    REGISTER_PEEK(reg1, sp, offset)                                 \
    REGISTER_PEEK(reg2, sp, offset)                                 \
    REGISTER_PEEK(reg3, sp, offset)                                 \
    REGISTER_PEEK(reg4, sp, offset)                                 \
  }

#define FIVE_REG_PEEK_FN(fn, sp)                                              \
  void fn##_5(int reg1, int reg2, int reg3, int reg4, int reg5, int offset) { \
    REGISTER_PEEK(reg1, sp, offset)                                           \
    REGISTER_PEEK(reg2, sp, offset)                                           \
    REGISTER_PEEK(reg3, sp, offset)                                           \
    REGISTER_PEEK(reg4, sp, offset)                                           \
    REGISTER_PEEK(reg5, sp, offset)                                           \
  }

#define SIX_REG_PEEK_FN(fn, sp)                                           \
  void fn##_6(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int offset) {                                               \
    REGISTER_PEEK(reg1, sp, offset)                                       \
    REGISTER_PEEK(reg2, sp, offset)                                       \
    REGISTER_PEEK(reg3, sp, offset)                                       \
    REGISTER_PEEK(reg4, sp, offset)                                       \
    REGISTER_PEEK(reg5, sp, offset)                                       \
    REGISTER_PEEK(reg6, sp, offset)                                       \
  }

#define SEVEN_REG_PEEK_FN(fn, sp)                                         \
  void fn##_7(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7, int offset) {                                     \
    REGISTER_PEEK(reg1, sp, offset)                                       \
    REGISTER_PEEK(reg2, sp, offset)                                       \
    REGISTER_PEEK(reg3, sp, offset)                                       \
    REGISTER_PEEK(reg4, sp, offset)                                       \
    REGISTER_PEEK(reg5, sp, offset)                                       \
    REGISTER_PEEK(reg6, sp, offset)                                       \
    REGISTER_PEEK(reg7, sp, offset)                                       \
  }

#define EIGHT_REG_PEEK_FN(fn, sp)                                         \
  void fn##_8(int reg1, int reg2, int reg3, int reg4, int reg5, int reg6, \
              int reg7, int reg8, int offset) {                           \
    REGISTER_PEEK(reg1, sp, offset)                                       \
    REGISTER_PEEK(reg2, sp, offset)                                       \
    REGISTER_PEEK(reg3, sp, offset)                                       \
    REGISTER_PEEK(reg4, sp, offset)                                       \
    REGISTER_PEEK(reg5, sp, offset)                                       \
    REGISTER_PEEK(reg6, sp, offset)                                       \
    REGISTER_PEEK(reg7, sp, offset)                                       \
    REGISTER_PEEK(reg8, sp, offset)                                       \
  }

// Register spill functions
ONE_REG_PUSH_FN(litecfi_register_spill, spill_stack);
TWO_REG_PUSH_FN(litecfi_register_spill, spill_stack);
THREE_REG_PUSH_FN(litecfi_register_spill, spill_stack);
FOUR_REG_PUSH_FN(litecfi_register_spill, spill_stack);
FIVE_REG_PUSH_FN(litecfi_register_spill, spill_stack);
SIX_REG_PUSH_FN(litecfi_register_spill, spill_stack);
SEVEN_REG_PUSH_FN(litecfi_register_spill, spill_stack);
EIGHT_REG_PUSH_FN(litecfi_register_spill, spill_stack);

// Register restore functions
ONE_REG_POP_FN(litecfi_register_restore, spill_stack);
TWO_REG_POP_FN(litecfi_register_restore, spill_stack);
THREE_REG_POP_FN(litecfi_register_restore, spill_stack);
FOUR_REG_POP_FN(litecfi_register_restore, spill_stack);
FIVE_REG_POP_FN(litecfi_register_restore, spill_stack);
SIX_REG_POP_FN(litecfi_register_restore, spill_stack);
SEVEN_REG_POP_FN(litecfi_register_restore, spill_stack);
EIGHT_REG_POP_FN(litecfi_register_restore, spill_stack);

// Register peek functions
ONE_REG_PEEK_FN(litecfi_register_peek, spill_stack);
TWO_REG_PEEK_FN(litecfi_register_peek, spill_stack);
THREE_REG_PEEK_FN(litecfi_register_peek, spill_stack);
FOUR_REG_PEEK_FN(litecfi_register_peek, spill_stack);
FIVE_REG_PEEK_FN(litecfi_register_peek, spill_stack);
SIX_REG_PEEK_FN(litecfi_register_peek, spill_stack);
SEVEN_REG_PEEK_FN(litecfi_register_peek, spill_stack);
EIGHT_REG_PEEK_FN(litecfi_register_peek, spill_stack);

// Register context save functions
ONE_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
TWO_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
THREE_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
FOUR_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
FIVE_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
SIX_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
SEVEN_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);
EIGHT_REG_PUSH_FN(litecfi_ctx_save, ctx_save_stack);

// Register context restore functions
ONE_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
TWO_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
THREE_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
FOUR_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
FIVE_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
SIX_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
SEVEN_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);
EIGHT_REG_POP_FN(litecfi_ctx_restore, ctx_save_stack);

// Register context peek functions
ONE_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
TWO_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
THREE_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
FOUR_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
FIVE_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
SIX_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
SEVEN_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);
EIGHT_REG_PEEK_FN(litecfi_ctx_peek, ctx_save_stack);

#ifdef __cplusplus
}
#endif
