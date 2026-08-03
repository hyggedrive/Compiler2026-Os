# REQUIRES: riscv

# RUN: rm -rf %t && split-file %s %t && cd %t

## R_RISCV_JAL is relaxed only when paired with R_RISCV_RELAX.
# RUN: llvm-mc -filetype=obj -triple=riscv32 -mattr=+c,+relax rv32.s -o rv32.o
# RUN: llvm-readelf -r rv32.o | FileCheck %s --check-prefix=RELOC
# RUN: ld.lld -T lds rv32.o -o rv32
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases rv32 | FileCheck %s --check-prefix=RV32

## C.J is available in RV64C, but C.JAL is not.
# RUN: llvm-mc -filetype=obj -triple=riscv64 -mattr=+c,+relax rv64.s -o rv64.o
# RUN: ld.lld -T lds rv64.o -o rv64
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases rv64 | FileCheck %s --check-prefix=RV64

## Without C, keep 32-bit JAL.
# RUN: llvm-mc -filetype=obj -triple=riscv32 -mattr=+relax noc.s -o noc.o
# RUN: ld.lld -T lds noc.o -o noc
# RUN: llvm-objdump -d --no-show-raw-insn -M no-aliases noc | FileCheck %s --check-prefix=NOC

## Without R_RISCV_RELAX, keep 32-bit JAL.
# RUN: llvm-mc -filetype=obj -triple=riscv32 -mattr=+c,+relax norelax.s -o norelax.o
# RUN: llvm-readelf -r norelax.o | FileCheck %s --check-prefix=NORELAX-RELOC
# RUN: ld.lld -T lds norelax.o -o norelax
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases norelax | FileCheck %s --check-prefix=NORELAX

## The opt-in option allows JAL relaxation without R_RISCV_RELAX.
# RUN: ld.lld -T lds --riscv-relax-jal-rvc norelax.o -o norelax.opt
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases norelax.opt | FileCheck %s --check-prefix=NORELAX-OPT

## The negative option wins and --no-relax keeps global priority.
# RUN: ld.lld -T lds --riscv-relax-jal-rvc --no-riscv-relax-jal-rvc norelax.o -o norelax.off
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases norelax.off | FileCheck %s --check-prefix=NORELAX
# RUN: ld.lld -T lds --riscv-relax-jal-rvc --no-relax norelax.o -o norelax.global-off
# RUN: llvm-objdump -td --no-show-raw-insn -M no-aliases norelax.global-off | FileCheck %s --check-prefix=NORELAX

## Positive and negative range boundaries.
# RUN: llvm-mc -filetype=obj -triple=riscv32 -mattr=+c,+relax range.s -o range.o
# RUN: ld.lld -T lds range.o -o range
# RUN: llvm-objdump -d --no-show-raw-insn -M no-aliases range | FileCheck %s --check-prefix=RANGE

# RELOC:      R_RISCV_JAL
# RELOC-NEXT: R_RISCV_RELAX

# RV32:      00010000 g       .text {{0*}}00000000 _start
# RV32:      00010002 l       .text {{0*}}00000000 after_cj
# RV32:      00010008 l       .text {{0*}}00000000 after_cjal
# RV32-LABEL: <_start>:
# RV32-NEXT:  c.j     {{.*}} <target_cj>
# RV32-NEXT:  addi    zero, zero, 0
# RV32-NEXT:  c.jal   {{.*}} <target_cjal>
# RV32-NEXT:  addi    zero, zero, 0
# RV32-NEXT:  jal     t0, {{.*}} <target_rd>

# RV64-LABEL: <_start>:
# RV64-NEXT:  c.j     {{.*}} <target_cj>
# RV64-NEXT:  addi    zero, zero, 0
# RV64-NEXT:  jal     ra, {{.*}} <target_cjal>

# NOC-LABEL: <_start>:
# NOC-NEXT:  jal      zero, {{.*}} <target_cj>

# NORELAX-RELOC:      R_RISCV_JAL
# NORELAX-RELOC-NOT:  R_RISCV_RELAX
# NORELAX:      00010000 g       .text {{0*}}00000000 _start
# NORELAX:      00010004 l       .text {{0*}}00000000 after_norelax_cj
# NORELAX:      0001000c l       .text {{0*}}00000000 after_norelax_cjal
# NORELAX-LABEL: <_start>:
# NORELAX-NEXT:  jal      zero, {{.*}} <target_cj>
# NORELAX-NEXT:  addi     zero, zero, 0
# NORELAX-NEXT:  jal      ra, {{.*}} <target_cjal>

# NORELAX-OPT:      00010000 g       .text {{0*}}00000000 _start
# NORELAX-OPT:      00010002 l       .text {{0*}}00000000 after_norelax_cj
# NORELAX-OPT:      00010008 l       .text {{0*}}00000000 after_norelax_cjal
# NORELAX-OPT-LABEL: <_start>:
# NORELAX-OPT-NEXT:  c.j      {{.*}} <target_cj>
# NORELAX-OPT-NEXT:  addi     zero, zero, 0
# NORELAX-OPT-NEXT:  c.jal    {{.*}} <target_cjal>

# RANGE-LABEL: <pos_min>:
# RANGE-NEXT:  c.j     {{.*}} <pos_target>
# RANGE:      <pos_oob>:
# RANGE-NEXT:  jal     zero, {{.*}} <pos_oob_target>
# RANGE:      <neg_min>:
# RANGE-NEXT:  c.j     {{.*}} <neg_target>
# RANGE:      <neg_oob>:
# RANGE-NEXT:  jal     zero, {{.*}} <neg_oob_target>

#--- lds
SECTIONS { .text 0x10000 : { *(.text) } }

#--- rv32.s
.globl _start
_start:
  .option push
  .option norvc
  jal zero, target_cj
  .option pop
after_cj:
  .word 0x00000013
  .option push
  .option norvc
  jal ra, target_cjal
  .option pop
after_cjal:
  .word 0x00000013
  .option push
  .option norvc
  jal t0, target_rd
  .option pop
target_cj:
  ret
target_cjal:
  ret
target_rd:
  ret

#--- rv64.s
.globl _start
_start:
  .option push
  .option norvc
  jal zero, target_cj
  .option pop
  .word 0x00000013
  .option push
  .option norvc
  jal ra, target_cjal
  .option pop
target_cj:
  ret
target_cjal:
  ret

#--- noc.s
.globl _start
_start:
  jal zero, target_cj
target_cj:
  ret

#--- norelax.s
.globl _start
_start:
  .option push
  .option norelax
  .option norvc
  jal zero, target_cj
  .option pop
after_norelax_cj:
  .word 0x00000013
  .option push
  .option norelax
  .option norvc
  jal ra, target_cjal
  .option pop
after_norelax_cjal:
  .word 0x00000013
target_cj:
  ret
target_cjal:
  ret

#--- range.s
.globl _start
_start:
pos_min:
  .option push
  .option norvc
  jal zero, pos_target
  .option pop
  .space 2042
pos_target:
  nop

pos_oob:
  .option push
  .option norvc
  jal zero, pos_oob_target
  .option pop
  .space 2044
pos_oob_target:
  nop

neg_target:
  nop
  .space 2046
neg_min:
  .option push
  .option norvc
  jal zero, neg_target
  .option pop

neg_oob_target:
  nop
  .space 2048
neg_oob:
  .option push
  .option norvc
  jal zero, neg_oob_target
  .option pop
