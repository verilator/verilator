// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook on instances, structs and interfaces in generate loops
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_gencell(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffU;
    if (insID == 1 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 50) v ^= 0x0fU;
    return static_cast<char>(v);
}

extern "C" short cb_gp(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    const bool active = VL_TIME_Q() >= 20 && VL_TIME_Q() < 40;
    return static_cast<short>((value[0].aval ^ (active ? 0xc33cU : 0U)) & 0xffffU);
}

extern "C" char cb_geniface(int insID, svBit trigger, const svLogicVecVal* value) {
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

    const std::vector<std::vector<std::string>> paths = {
        {"lane[0].u", "mid"}, {"lagg[1].gp"}, {"lif[0].bi", "data"}, {"lif[1].barr[1]", "data"}};
    const std::vector<int> ids = {1, 2, 0, 1};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = ids[i];
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
