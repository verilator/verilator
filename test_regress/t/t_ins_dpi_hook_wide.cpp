// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook targets wider than 32 bits
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" void cb_wide(svLogicVecVal* result, int insID, svBit trigger,
                        const svLogicVecVal* value) {
    (void)trigger;
    for (int i = 0; i < 4; ++i) {
        result[i].aval = value[i].aval;
        result[i].bval = value[i].bval;
    }
    if (insID == 1 && VL_TIME_Q() >= 10 && VL_TIME_Q() < 20) {
        result[0].aval = 0xdeadbeefU;
        result[1].aval = result[2].aval = result[3].aval = 0;
        result[0].bval = result[1].bval = result[2].bval = result[3].bval = 0;
    }
    if (insID == 2 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 30) {
        result[0].aval = 0xfeedfaceU;
        result[1].aval = result[2].aval = result[3].aval = 0;
        result[0].bval = result[1].bval = result[2].bval = result[3].bval = 0;
    }
}

static bool active(uint64_t from) { return VL_TIME_Q() >= from && VL_TIME_Q() < from + 20; }

extern "C" long long cb_quad48(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 1 && active(20)) return 0xdeadbeefcafeLL;
    return static_cast<long long>(value[0].aval)
           | (static_cast<long long>(value[1].aval & 0xffffU) << 32);
}

extern "C" long long cb_quad64(int insID, svBit trigger, long long value) {
    (void)trigger;
    if (insID == 2 && active(30)) return 0x7eadbeefcafef00dLL;
    return value;
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"s0", "v"}, {"s0", "v2"}, {"s0", "v48"}, {"s0", "v64"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = static_cast<int>(i % 2) + 1;
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
