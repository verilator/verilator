// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <cstdio>
#include <cstdlib>
#include <svdpi.h>

extern "C" void exported();

extern "C" int ctask() {
    const svScope scope = svGetScope();
    exported();
    if (svGetScope() != scope) {
        std::fprintf(stderr, "DPI scope changed from %s to %s after exported task\n",
                     svGetNameFromScope(scope), svGetNameFromScope(svGetScope()));
        std::abort();
    }
    exported();
    return 0;
}

extern "C" void perturb() {}
