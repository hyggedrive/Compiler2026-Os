# REQUIRES: riscv

# RUN: llvm-mc -filetype=obj -triple=riscv32 %s -o %t.o
# RUN: ld.lld --gc-sections --riscv-function-sections-split-debug-relocs \
# RUN:   --print-riscv-function-sections-split %t.o -o %t.default \
# RUN:   2>&1 | FileCheck %s --check-prefix=PRINT
# RUN: llvm-objdump -s -j .debug_info %t.default \
# RUN:   | FileCheck %s --check-prefix=RV32-DEFAULT
# RUN: llvm-nm -a %t.default | FileCheck %s --check-prefix=NM \
# RUN:   --implicit-check-not=dead_label --implicit-check-not=unused_rv32
# RUN: ld.lld --gc-sections --riscv-function-sections-split-debug-relocs \
# RUN:   -z dead-reloc-in-nonalloc=.debug_info=0x12345678 \
# RUN:   %t.o -o %t.explicit
# RUN: llvm-objdump -s -j .debug_info %t.explicit \
# RUN:   | FileCheck %s --check-prefix=RV32-EXPLICIT
# RUN: ld.lld --gc-sections --riscv-function-sections-split-debug-relocs \
# RUN:   -z 'dead-reloc-in-nonalloc=.debug_*=0x87654321' \
# RUN:   %t.o -o %t.glob
# RUN: llvm-objdump -s -j .debug_info %t.glob \
# RUN:   | FileCheck %s --check-prefix=RV32-GLOB
# RUN: ld.lld --gc-sections %t.o -o %t.no-split-debug
# RUN: llvm-objdump -s -j .debug_info %t.no-split-debug \
# RUN:   | FileCheck %s --check-prefix=RV32-NO-SPLIT-DEBUG

# PRINT: riscv-function-sections-split: phase1a: split parent: {{.*}}:(.text.split)
# PRINT: riscv-function-sections-split: phase2a: parent: {{.*}}:(.text.split) live children 1 dead children 1

# RV32-DEFAULT:      Contents of section .debug_info:
# RV32-DEFAULT-NEXT:  0000 ffffffff ffffffff

# RV32-EXPLICIT:      Contents of section .debug_info:
# RV32-EXPLICIT-NEXT:  0000 78563412 78563412

# RV32-GLOB:      Contents of section .debug_info:
# RV32-GLOB-NEXT:  0000 21436587 21436587

# RV32-NO-SPLIT-DEBUG:      Contents of section .debug_info:
# RV32-NO-SPLIT-DEBUG-NEXT:  0000 {{[0-9a-f]+}} 00000000

# NM: T _start

.globl _start
.section .text.start,"ax",@progbits
.type _start,@function
_start:
  call live0
  ret
.size _start, .-_start

.section .text.split,"ax",@progbits
.type live0,@function
live0:
  ret
.size live0, .-live0
.type dead0,@function
dead0:
.globl dead_label
.hidden dead_label
.type dead_label,@notype
dead_label:
  ret
.size dead0, .-dead0

.section .text.unused,"ax",@progbits
.globl unused_rv32
.hidden unused_rv32
.type unused_rv32,@function
unused_rv32:
  ret
.size unused_rv32, .-unused_rv32

.section .debug_info,"",@progbits
  .word dead_label
  .word unused_rv32
