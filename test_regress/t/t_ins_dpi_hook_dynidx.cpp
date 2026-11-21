// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hooks on arrays read through non-constant indices
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_rf(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    const bool active = VL_TIME_Q() >= 20 && VL_TIME_Q() < 40;
    const unsigned mask = insID == 1 ? 0x5aU : 0x3cU;  // rf[5] / rf[6]
    return static_cast<char>((value[0].aval ^ (active ? mask : 0U)) & 0xffU);
}

extern "C" int cb_wm(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    const bool active = VL_TIME_Q() >= 20 && VL_TIME_Q() < 40;
    return static_cast<int>(value[0].aval ^ (active ? 0x5a3c9612U : 0U));
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    topp->DPIHOOK_CASE_ID[0] = 1;
    topp->DPIHOOK_PATH[0][0] = "u";
    topp->DPIHOOK_PATH[0][1] = "rf[5]";
    topp->DPIHOOK_CASE_ID[1] = 2;
    topp->DPIHOOK_PATH[1][0] = "u";
    topp->DPIHOOK_PATH[1][1] = "wm";
    topp->DPIHOOK_CASE_ID[2] = 3;
    topp->DPIHOOK_PATH[2][0] = "u";
    topp->DPIHOOK_PATH[2][1] = "rf[6]";

    while (!contextp->gotFinish()) {
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
