// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook on unpacked struct members and whole structs
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_member(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    const unsigned v = value[0].aval & 0xffU;
    if (insID == 1 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 50) return 0xAA;
    return static_cast<int>(v);
}

extern "C" char cb_a(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    (void)insID;
    const unsigned v = value[0].aval & 0xffU;
    if (VL_TIME_Q() >= 20 && VL_TIME_Q() < 45) return 0xAA;
    return static_cast<int>(v);
}

extern "C" short cb_b(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    (void)insID;
    const unsigned v = value[0].aval & 0xffffU;
    if (VL_TIME_Q() >= 35 && VL_TIME_Q() < 65) return 0xBBBB;
    return static_cast<int>(v);
}

extern "C" int cb_struct(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    const unsigned v = value[0].aval & 0xffffffU;
    if (insID == 4 && VL_TIME_Q() >= 20 && VL_TIME_Q() < 50) {
        return static_cast<int>((0xAAU << 16) | (v & 0xffffU));
    }
    return static_cast<int>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths = {{"um.a"}, {"u2.a"}, {"u2.b"}, {"us"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->DPIHOOK_CASE_ID[i] = static_cast<int>(i) + 1;
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
