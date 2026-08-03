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

// Collect the estimated code bytes saved when each writable data input
// section is placed in the GP-addressable window.
void collectRISCVGPSectionBenefits(Ctx &ctx);
uint64_t getRISCVGPSectionBenefit(const InputSectionBase *sec);

// Select __global_pointer$ after input-section ordering and address assignment.
void optimizeRISCVGP(Ctx &ctx);

} // namespace elf
} // namespace lld

#endif
