// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook targets inside aggregates, read through hierarchical references
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

static bool inWindow() { return VL_TIME_Q() >= 20 && VL_TIME_Q() < 40; }

extern "C" int cb_mem(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    return static_cast<int>(value[0].aval ^ (inWindow() ? 0x5a3c9612U : 0U));
}

extern "C" char cb_sb(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    return static_cast<char>((value[0].aval ^ (inWindow() ? 0xa5U : 0U)) & 0xffU);
}

extern "C" short cb_p(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    return static_cast<short>((value[0].aval ^ (inWindow() ? 0xc33cU : 0U)) & 0xffffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths = {{"u", "mem"}, {"u", "s.b"}, {"u", "p"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = static_cast<int>(i) + 1;
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
