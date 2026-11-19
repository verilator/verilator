// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook insertion test main
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include "svdpi.h"

#include <cstdio>
#include <string>
#include <vector>

extern "C" char cb(int insID, svBit trigger, const svLogicVecVal* value) {
    const char v = static_cast<char>(value->aval & 0xff);
    switch (insID) {
    case 1: return static_cast<char>(v ^ 0x80);
    case 2: return 0x11;
    case 3: return 0x22;
    case 4: return (VL_TIME_Q() >= 30 && VL_TIME_Q() < 40) ? 0x44 : v;
    default: return v;
    }
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"mreg"}, {"di", "data"}, {"oi", "inner", "data"}, {"lane[1].gi", "data"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->__Vdpihook_id[i] = static_cast<int>(i + 1);
        for (size_t j = 0; j < paths[i].size(); ++j) topp->__Vdpihook_path[i][j] = paths[i][j];
    }

    // The clock stops at time 25; afterwards only the trigger re-evaluates the hooks
    for (; contextp->time() < 50; contextp->timeInc(1)) {
        if (contextp->time() < 25 && contextp->time() % 5 == 0) topp->clk = !topp->clk;
        topp->__Vdpihook_trigger = !topp->__Vdpihook_trigger;
        topp->eval();
        if (contextp->time() % 5 == 4)
            printf("[%d] mod=%02x if=%02x nested=%02x gen=%02x\n",
                   static_cast<int>(contextp->time()), topp->o_mod, topp->o_if, topp->o_nested,
                   topp->o_gen);
    }
    topp->final();
    return 0;
}
