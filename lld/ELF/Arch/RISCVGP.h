//===- RISCVGP.h -----------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLD_ELF_ARCH_RISCVGP_H
#define LLD_ELF_ARCH_RISCVGP_H

#include <cstdint>

namespace lld {
namespace elf {

class Ctx;
class InputSectionBase;

void collectRISCVGPSectionBenefits(Ctx &ctx);
uint64_t getRISCVGPSectionBenefit(const InputSectionBase *sec);
void optimizeRISCVGP(Ctx &ctx);

} // namespace elf
} // namespace lld

#endif
