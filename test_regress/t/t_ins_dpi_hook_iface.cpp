// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook interface-signal test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_iface(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffU;
    if (insID != 0 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 50) v ^= 0x0fU;
    return static_cast<char>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"m", "b", "data"}, {"s1", "data"}, {"arr[0]", "data"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = static_cast<int>(i) + 1;
        for (size_t j = 0; j < paths[i].size(); ++j) topp->DPIHOOK_PATH[i][j] = paths[i][j];
    }

    while (!contextp->gotFinish()) {
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());
    }
    topp->final();
    return 0;
}
