// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hooks on output ports with sequential and task drivers
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>

extern "C" char cb_out(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    static const unsigned masks[] = {0x00, 0x5a, 0x3c, 0x96, 0xa5};
    const bool active = VL_TIME_Q() >= 20 && VL_TIME_Q() < 40;
    const unsigned mask = (active && insID >= 1 && insID <= 4) ? masks[insID] : 0U;
    return static_cast<char>((value[0].aval ^ mask) & 0xffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const char* const ports[] = {"q_reg", "q_self", "q_arst", "q_task"};
    for (int i = 0; i < 4; ++i) {
        topp->DPIHOOK_CASE_ID[i] = i + 1;
        topp->DPIHOOK_PATH[i][0] = "u";
        topp->DPIHOOK_PATH[i][1] = ports[i];
    }

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
