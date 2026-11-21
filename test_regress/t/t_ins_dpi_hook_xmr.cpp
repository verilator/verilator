// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook read through a cross-module reference
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_xmr(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    if (VL_TIME_Q() >= 20) return static_cast<char>(0xee);
    return static_cast<char>(value[0].aval & 0xffU);
}

extern "C" char cb_xmrpath(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 0) return static_cast<char>(0xaa);
    if (insID == 1) return static_cast<char>(0xbb);
    return static_cast<char>(value[0].aval & 0xffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"m", "u", "sig"}, {"s", "mem[2]"}, {"s", "st.a"}};
    const std::vector<int> ids = {2, 0, 1};
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
