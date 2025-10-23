// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <svdpi.h>

extern "C" int instrument_var(int id, int trigger, const svLogic* x) {
    switch (id) {
    case 0:
        if ((VL_TIME_Q() >= 10 && VL_TIME_Q() < 20) || VL_TIME_Q() >= 85) {
            return 0;
        } else {
            return *x;
        }
        //return 0;
    case 1:
        if ((VL_TIME_Q() < 3) || (VL_TIME_Q() >= 32 && VL_TIME_Q() < 69)) {
            return 1;
        } else {
            return *x;
        }
    default: return *x;
    }
}
