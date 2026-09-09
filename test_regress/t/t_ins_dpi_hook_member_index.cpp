// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook leaves addressed by an element and a member step
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

static bool active(uint64_t from) { return VL_TIME_Q() >= from && VL_TIME_Q() < from + 20; }

extern "C" char cb_nib(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 1 && active(20)) return 0xf;
    return static_cast<char>(value[0].aval & 0xfU);
}

extern "C" char cb_byte(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 2 && active(30)) return static_cast<char>(0xee);
    if (insID == 3 && active(40)) return 0x10;
    return static_cast<char>(value[0].aval & 0xffU);
}

extern "C" char cb_packedstruct(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 4) return static_cast<char>(0xaa);
    return static_cast<char>(value[0].aval & 0xffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"na[1].a"}, {"s.arr[1]"}, {"cs.d"}, {"pu.hi"}};
    for (size_t k = 0; k < paths.size(); ++k) {
        topp->DPIHOOK_CASE_ID[k] = static_cast<int>(k) + 1;
        for (size_t j = 0; j < paths[k].size(); ++j) topp->DPIHOOK_PATH[k][j] = paths[k][j];
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
