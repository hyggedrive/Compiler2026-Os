# REQUIRES: riscv

# RUN: llvm-mc -filetype=obj -triple=riscv32 %s -o %t.o

## The option is off by default, so split children keep their splitter-imposed
## keepUnique bit and standard ICF does not fold them.
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split-gc \
# RUN:   --print-icf-sections %t.o -o %t.off 2>&1 | count 0

## Enabling split ICF only removes the splitter-imposed keepUnique bit. The
## existing Safe ICF implementation performs the actual fold.
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split-icf \
# RUN:   --print-icf-sections %t.o -o %t.on 2>&1 \
# RUN:   | FileCheck %s --check-prefix=ICF
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split-icf \
# RUN:   --print-riscv-function-sections-split %t.o -o %t.print 2>&1 \
# RUN:   | FileCheck %s --check-prefix=SPLIT

## --keep-unique is still honored by findKeepUniqueSections().
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split-icf \
# RUN:   --keep-unique=keep0 --print-icf-sections %t.o -o %t.keep 2>&1 \
# RUN:   | FileCheck %s --check-prefix=KEEP

## The negative option overrides the positive option.
# RUN: ld.lld --gc-sections --icf=safe --riscv-function-sections-split-icf \
# RUN:   --no-riscv-function-sections-split-icf --print-icf-sections \
# RUN:   %t.o -o %t.no 2>&1 | count 0

# ICF-DAG: selected section {{.*}}:(.text.icf)
# ICF-DAG:   removing identical section {{.*}}:(.text.icf)
# ICF-NOT: removing identical section {{.*}}:(.text.mismatch)
# ICF-NOT: removing identical section {{.*}}:(.text.fallback)

# KEEP-DAG: selected section {{.*}}:(.text.icf)
# KEEP-DAG:   removing identical section {{.*}}:(.text.icf)
# KEEP-NOT: removing identical section {{.*}}:(.text.keep)

# SPLIT: riscv-function-sections-split: parent section: .text.fallback
# SPLIT: riscv-function-sections-split: block reasons: computed-jump,function-fallthrough

.globl _start
.section .text.start,"ax",@progbits
.type _start,@function
_start:
  call ident0
  call ident1
  call mismatch0
  call mismatch1
  call keep0
  call keep1
  call fallback0
  ret
.size _start, .-_start

.section .text.icf,"ax",@progbits
.hidden ident0
.globl ident0
.type ident0,@function
ident0:
  ret
.size ident0, .-ident0
.hidden ident1
.globl ident1
.type ident1,@function
ident1:
  ret
.size ident1, .-ident1

.section .text.mismatch,"ax",@progbits
.hidden mismatch0
.globl mismatch0
.type mismatch0,@function
mismatch0:
  call helper0
  ret
.size mismatch0, .-mismatch0
.hidden mismatch1
.globl mismatch1
.type mismatch1,@function
mismatch1:
  call helper1
  ret
.size mismatch1, .-mismatch1

.section .text.keep,"ax",@progbits
.hidden keep0
.globl keep0
.type keep0,@function
keep0:
  nop
  ret
.size keep0, .-keep0
.hidden keep1
.globl keep1
.type keep1,@function
keep1:
  nop
  ret
.size keep1, .-keep1

.section .text.fallback,"ax",@progbits
.type fallback0,@function
fallback0:
  jalr a0
.size fallback0, .-fallback0
.type fallback1,@function
fallback1:
  ret
.size fallback1, .-fallback1

.section .text.helper0,"ax",@progbits
.type helper0,@function
helper0:
  li a0, 1
  ret
.size helper0, .-helper0

.section .text.helper1,"ax",@progbits
.type helper1,@function
helper1:
  li a0, 2
  ret
.size helper1, .-helper1

.addrsig
