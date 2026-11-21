// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Targets of one width but different declared types sharing a callback
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

static bool active() { return VL_TIME_Q() >= 20 && VL_TIME_Q() < 40; }

extern "C" char cb_8(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    const unsigned mask = insID == 1 ? 0x5aU : insID == 2 ? 0x3cU : 0x96U;
    return static_cast<char>((value[0].aval ^ (active() ? mask : 0U)) & 0xffU);
}

extern "C" int cb_int(int insID, svBit trigger, int value) {
    (void)trigger;
    const int mask = insID == 4 ? 0x5a5 : 0x3c3;
    return active() ? (value ^ mask) : value;
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::string> insts = {"u_v", "u_s", "u_e", "u_i", "u_ie"};
    for (size_t k = 0; k < insts.size(); ++k) {
        topp->DPIHOOK_CASE_ID[k] = static_cast<int>(k) + 1;
        topp->DPIHOOK_PATH[k][0] = insts[k];
        topp->DPIHOOK_PATH[k][1] = "t";
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
