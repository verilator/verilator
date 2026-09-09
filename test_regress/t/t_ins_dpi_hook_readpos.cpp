// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook targets of the top module and their read positions
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_readpos(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    (void)insID;
    const unsigned v = value[0].aval & 0xffU;
    // Window edges sit on negative clock edges, away from every sampling point
    if (VL_TIME_Q() >= 20 && VL_TIME_Q() < 40) return 0xEE;
    return static_cast<int>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths = {{"t"}, {"v"}};
    const std::vector<int> ids = {1, 0};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = ids[i];
        for (size_t j = 0; j < paths[i].size(); ++j) topp->DPIHOOK_PATH[i][j] = paths[i][j];
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
