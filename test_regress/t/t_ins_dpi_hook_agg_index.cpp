// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook reads through non-constant indices and one with a side effect
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

extern "C" long long cb_m2(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    uint64_t v = static_cast<uint64_t>(value[0].aval)
                 | (static_cast<uint64_t>(value[1].aval & 0xffffU) << 32);
    if (insID == 1 && active(20)) v ^= 0x808080808080ULL;
    return static_cast<long long>(v);
}

extern "C" short cb_mx(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffffU;
    if (insID == 2 && active(30)) v = (0xabU << 8) | (v & 0xffU);
    return static_cast<short>(v);
}

extern "C" char cb_rf(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    if (insID == 3 && active(40)) return static_cast<char>(0xcc);
    return static_cast<char>(value[0].aval & 0xffU);
}

extern "C" int cb_nested(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval;
    if (insID == 4 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 60) v = (v & ~0xffU) | 0xEEU;
    return static_cast<int>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths = {{"m2"}, {"mx"}, {"rf[2]"}, {"aos"}};
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
