// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "svdpi.h"

#include VM_PREFIX_INCLUDE_DPI

int dpii_unit(const unit_t* i, unit_t* o) {
    o->a = i->a + 1;
    for (int k = 0; k < 2; ++k) o->b[k] = i->b[k] + 1;
    return i->a + i->b[0] + i->b[1];
}
