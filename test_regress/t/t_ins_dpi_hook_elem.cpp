// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook element-target test main
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" int cb_array(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval;
    if (insID == 1 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 60) {
        v = (v & ~(0xffU << 16)) | (0xEEU << 16);
    }
    return static_cast<int>(v);
}

extern "C" char cb_elem(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    const bool active = VL_TIME_Q() >= 20 && VL_TIME_Q() < 40;
    const unsigned mask = insID == 1 ? 0x5aU : 0x3cU;
    return static_cast<char>((value[0].aval ^ (active ? mask : 0U)) & 0xffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"mem"}, {"s", "mem[2]"}, {"m[5]"}, {"d[6]"}};
    const std::vector<int> ids = {1, 0, 1, 2};
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
