# REQUIRES: x86

# RUN: llvm-mc -filetype=obj -triple=x86_64 %s -o %t.o
# RUN: ld.lld --gc-sections --riscv-function-sections-split-debug-relocs \
# RUN:   %t.o -o %t
# RUN: llvm-objdump -s -j .debug_info %t | FileCheck %s

# CHECK:      Contents of section .debug_info:
# CHECK-NEXT:  0000 00000000 00000000

.globl _start
_start:
  ret

.section .text.unused,"ax",@progbits
.type unused_x86,@function
unused_x86:
  ret
.size unused_x86, .-unused_x86

.section .debug_info,"",@progbits
  .quad unused_x86
