// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook on leaves next to a clock leaf
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

extern "C" svBit cb_bit(int insID, svBit trigger, svLogic value) {
    (void)trigger;
    if (insID == 1 && active(20)) return 1;
    return value & 1;
}

extern "C" char cb_pb(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 2 && active(30)) return 0x7f;
    return static_cast<char>(value[0].aval & 0x7fU);
}

extern "C" char cb_x(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 3 && active(40)) return static_cast<char>(0xaa);
    if (insID == 4 && active(50)) return static_cast<char>(0xbb);
    return static_cast<char>(value[0].aval & 0xffU);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"clks[1]"}, {"p.b"}, {"s2.in.x"}, {"s3.arr[1].x"}};
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
