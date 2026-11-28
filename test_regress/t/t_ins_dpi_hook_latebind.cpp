// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook slot bound after the first eval() is diagnosed
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <svdpi.h>

extern "C" char cb_latebind(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)insID;
    (void)trigger;
    (void)value;
    return static_cast<char>(0xee);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    // Deliberately leave every slot unbound across the first eval()

    int evals = 0;
    while (!contextp->gotFinish() && evals < 20) {
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());
        ++evals;
    }

    // The hook sampled __Vdpihook_path at time zero, so the binding is too late and binds nothing.
    // The model has no way to act on it, but final() reports the mistake.
    topp->__Vdpihook_id[0] = 0;
    topp->__Vdpihook_path[0][0] = "a";
    topp->__Vdpihook_path[0][1] = "u";
    topp->__Vdpihook_path[0][2] = "sig";

    while (!contextp->gotFinish()) {
        topp->__Vdpihook_trigger = !topp->__Vdpihook_trigger;
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->timeInc(1);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
