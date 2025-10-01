// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <iostream>
#include <svdpi.h>

extern "C" short instrument_var(int id, const svLogic* x) {
    switch (id) {
    case 0: return 0;
    case 1:
        // Stuck at 1 Fault Injection
        return 1;
    case 2:
        // Inverter/Bit flip Fault injection (provisional)
        return !x;
    default: return *x;
    }
}
