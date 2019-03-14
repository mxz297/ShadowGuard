#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
// Test Name : spill_and_overflow_test
//
// Description :
//
// Tests hardening an application causing a register stack overflow along with a
// conflicting AVX2 register spill

void baz(int depth) {
  if (depth == 0) {
    return;
  }

  int *buffer = (int*) malloc(sizeof(int) * depth);
  int i = 0;
  for (i = 0; i < depth; ++i) buffer[i] = depth * i;

  // Use up some avx2 registers
  asm("pxor %%xmm15, %%xmm15;\n\t"
      "pxor %%xmm13, %%xmm13;\n\t"
      "pxor %%xmm12, %%xmm12;\n\t"
      :
      :
      :);
  fprintf(stderr, "baz before depth %d\n", depth);
  baz(--depth);
  fprintf(stderr, "baz after depth %d\n", depth);

  // Use up some avx2 registers
  asm("pxor %%xmm15, %%xmm15;\n\t"
      "pxor %%xmm13, %%xmm13;\n\t"
      "pxor %%xmm12, %%xmm12;\n\t"
      :
      :
      :);

  free(buffer);
  return;
}

int main() { 
    baz(30); 
    fprintf(stderr, "back to main\n");
}
