// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <svdpi.h>

extern "C" char instrument_var(int insID, svBit trigger, const svLogicVecVal* out) {
    const int x = out->aval & 0xff;
    switch (insID) {
    case 0:
        if ((VL_TIME_Q() >= 10 && VL_TIME_Q() < 20) || VL_TIME_Q() >= 85) {
            return 0;
        } else {
            return x;
        }
    case 1:
        if ((VL_TIME_Q() < 3) || (VL_TIME_Q() >= 32 && VL_TIME_Q() < 69)) {
            return 1;
        } else {
            return x;
        }
    default: return x;
    }
}
