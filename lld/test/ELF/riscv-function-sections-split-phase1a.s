# REQUIRES: riscv

# RUN: rm -rf %t && split-file %s %t
# RUN: llvm-mc -filetype=obj -triple=riscv32-unknown-elf %t/main.s -o %t/main.o
# RUN: llvm-mc -filetype=obj -triple=riscv32-unknown-elf %t/got.s -o %t/got.o
# RUN: ld.lld --gc-sections %t/main.o -o %t/off
# RUN: ld.lld --gc-sections --riscv-function-sections-split %t/main.o -o %t/on
# RUN: cmp %t/off %t/on
# RUN: ld.lld --gc-sections --print-riscv-function-sections-split \
# RUN:   %t/main.o -o %t/print-only 2>&1 | count 0
# RUN: cmp %t/off %t/print-only
# RUN: llvm-nm %t/on | FileCheck %s --check-prefix=NM \
# RUN:   --implicit-check-not=dead0 --implicit-check-not=dead1
# RUN: llvm-readelf -sW %t/off > %t/off.sym
# RUN: llvm-readelf -sW %t/on > %t/on.sym
# RUN: cmp %t/off.sym %t/on.sym
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split \
# RUN:   %t/main.o -o %t/icf
# RUN: llvm-nm %t/icf | FileCheck %s --check-prefix=ICF
# RUN: llvm-nm -n %t/icf | sed -n 's/^\([0-9a-f]*\) T ident0$/\1/p' > %t/ident0
# RUN: llvm-nm -n %t/icf | sed -n 's/^\([0-9a-f]*\) T ident1$/\1/p' > %t/ident1
# RUN: not cmp %t/ident0 %t/ident1
# RUN: ld.lld --emit-relocs --gc-sections %t/main.o -o %t/emit.off
# RUN: ld.lld --emit-relocs --gc-sections --riscv-function-sections-split \
# RUN:   %t/main.o -o %t/emit.on
# RUN: cmp %t/emit.off %t/emit.on
# RUN: ld.lld --emit-relocs --gc-sections --riscv-function-sections-split \
# RUN:   --print-riscv-function-sections-split %t/main.o -o %t/emit.print 2>&1 \
# RUN:   | FileCheck %s --check-prefix=EMIT
# RUN: ld.lld -shared %t/got.o -o %t/shared.off
# RUN: ld.lld -shared --riscv-function-sections-split %t/got.o -o %t/shared.on
# RUN: llvm-readelf -S -r %t/shared.off > %t/shared.off.readelf
# RUN: llvm-readelf -S -r %t/shared.on > %t/shared.on.readelf
# RUN: cmp %t/shared.off.readelf %t/shared.on.readelf
# RUN: FileCheck %s --check-prefix=GOT-RELOC < %t/shared.on.readelf
# RUN: llvm-objdump -dr %t/shared.off | sed '1d' > %t/shared.off.objdump
# RUN: llvm-objdump -dr %t/shared.on | sed '1d' > %t/shared.on.objdump
# RUN: cmp %t/shared.off.objdump %t/shared.on.objdump
# RUN: ld.lld -shared --riscv-function-sections-split \
# RUN:   --print-riscv-function-sections-split %t/got.o -o %t/shared.print 2>&1 \
# RUN:   | FileCheck %s --check-prefix=GOT
# RUN: ld.lld --gc-sections --riscv-function-sections-split \
# RUN:   --print-riscv-function-sections-split %t/main.o -o %t/print 2>&1 \
# RUN:   | FileCheck %s

# RUN: llvm-mc -filetype=obj -triple=riscv64-unknown-elf %t/main.s -o %t/rv64.o
# RUN: ld.lld --riscv-function-sections-split \
# RUN:   --print-riscv-function-sections-split %t/rv64.o -o %t/rv64 2>&1 \
# RUN:   | count 0

# NM-DAG: T live0
# NM-DAG: T live1
# NM-DAG: T ident0
# NM-DAG: T ident1

# ICF-DAG: T ident0
# ICF-DAG: T ident1

# EMIT: riscv-function-sections-split: phase1a: split parent count: 0
# EMIT: riscv-function-sections-split: phase1a: parent fallback count: 5

# GOT:      riscv-function-sections-split: phase1a: split parent: {{.*}}:(.text.got) size 16 children 2 relocs {{[0-9]+}}
# GOT-NEXT: riscv-function-sections-split: phase1a: child range: [0,12)
# GOT-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: {{.*}}0{{.*}}4
# GOT-NEXT: riscv-function-sections-split: phase1a: child range: [12,16)
# GOT-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: none

# GOT-RELOC: .got
# GOT-RELOC: R_RISCV_32
# GOT-RELOC: extvar

# CHECK:      riscv-function-sections-split: parent section: .text.unsafe_jalr
# CHECK:      riscv-function-sections-split: block reasons: computed-jump,function-fallthrough
# CHECK:      riscv-function-sections-split: parent section: .text.fallthrough
# CHECK:      riscv-function-sections-split: block reasons: function-fallthrough
# CHECK:      riscv-function-sections-split: parent section: .text.debug_target
# CHECK:      riscv-function-sections-split: block reasons: incoming-debug-relocation

# CHECK: riscv-function-sections-split: phase1a: split parent count: 5
# CHECK: riscv-function-sections-split: phase1a: skipped safe single-function parent count: 2
# CHECK: riscv-function-sections-split: phase1a: created child count: 10
# CHECK: riscv-function-sections-split: phase1a: parent fallback count: 0

# CHECK:      riscv-function-sections-split: phase1a: split parent: {{.*}}:(.text.live) size 12 children 2 relocs 0
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [0,4)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: none
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [4,12)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: none

# CHECK:      riscv-function-sections-split: phase1a: split parent: {{.*}}:(.text.reloc) size 16 children 2 relocs {{[0-9]+}}
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [0,12)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: 0{{(,0)?}}
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [12,16)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: none

# CHECK:      riscv-function-sections-split: phase1a: split parent: {{.*}}:(.text.local) size 16 children 2 relocs {{[0-9]+}}
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [0,12)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: {{.*}}0{{.*}}4
# CHECK-NEXT: riscv-function-sections-split: phase1a: child range: [12,16)
# CHECK-NEXT: riscv-function-sections-split: phase1a: child relocation offsets: none

#--- main.s
.globl _start
.section .text.start,"ax",@progbits
.type _start,@function
_start:
  call live0
  call single0
  call ident0
  call rel0
  call local0
  ret
.size _start, .-_start

.section .text.live,"ax",@progbits
.globl live0
.type live0,@function
live0:
  ret
.size live0, .-live0
.globl live1
.type live1,@function
live1:
  addi a0, a0, 1
  ret
.size live1, .-live1

.section .text.dead,"ax",@progbits
.type dead0,@function
dead0:
  ret
.size dead0, .-dead0
.type dead1,@function
dead1:
  ret
.size dead1, .-dead1

.section .text.single,"ax",@progbits
.globl single0
.type single0,@function
single0:
  ret
.size single0, .-single0

.section .text.ident,"ax",@progbits
.globl ident0
.type ident0,@function
ident0:
  ret
.size ident0, .-ident0
.globl ident1
.type ident1,@function
ident1:
  ret
.size ident1, .-ident1

.section .text.reloc,"ax",@progbits
.globl rel0
.type rel0,@function
rel0:
  call rel1
  ret
.size rel0, .-rel0
.globl rel1
.type rel1,@function
rel1:
  ret
.size rel1, .-rel1

.section .text.local,"ax",@progbits
.globl local0
.type local0,@function
local0:
.Lpcrel_hi0:
  auipc a0, %pcrel_hi(local0)
  addi a0, a0, %pcrel_lo(.Lpcrel_hi0)
  ret
.size local0, .-local0
.type local1,@function
local1:
  ret
.size local1, .-local1

.section .text.unsafe_jalr,"ax",@progbits
.type unsafe_jalr0,@function
unsafe_jalr0:
  jalr zero, 0(a0)
.size unsafe_jalr0, .-unsafe_jalr0
.type unsafe_jalr1,@function
unsafe_jalr1:
  ret
.size unsafe_jalr1, .-unsafe_jalr1

.section .text.fallthrough,"ax",@progbits
.type fallthrough0,@function
fallthrough0:
  addi a0, a0, 1
.size fallthrough0, .-fallthrough0
.type fallthrough1,@function
fallthrough1:
  ret
.size fallthrough1, .-fallthrough1

.section .text.debug_target,"ax",@progbits
.type debug_target0,@function
debug_target0:
  ret
.size debug_target0, .-debug_target0
.type debug_target1,@function
debug_target1:
  ret
.size debug_target1, .-debug_target1

.section .debug_zgq_test,"",@progbits
  .word debug_target0

#--- got.s
.section .text.got,"ax",@progbits
.globl got0
.type got0,@function
got0:
.Lgot_hi0:
  auipc a0, %got_pcrel_hi(extvar)
  lw a0, %pcrel_lo(.Lgot_hi0)(a0)
  ret
.size got0, .-got0
.type got1,@function
got1:
  ret
.size got1, .-got1
