// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook on targets in and next to conditional generate blocks
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

static bool active(uint64_t from) { return VL_TIME_Q() >= from && VL_TIME_Q() < from + 20; }

extern "C" char cb_genif(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffU;
    if (insID == 1 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 50) v = 0xEEU;
    return static_cast<char>(v);
}

extern "C" char cb_impl(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffU;
    if (insID == 1 && active(20)) v ^= 0x0fU;
    if (insID == 2 && active(30)) v ^= 0xf0U;
    return static_cast<char>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"g_en.cnt"}, {"cnt"}, {"genblk5.u", "r"}, {"genblk6.nb.w"}};
    const std::vector<int> ids = {1, 1, 1, 2};
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
