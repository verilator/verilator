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

// The high nibble shows which slot hooked the signal
extern "C" char cb(int insID, svBit trigger, const svLogicVecVal* value) {
    return static_cast<char>((insID << 4) | (value->aval & 0xf));
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::string> paths = {"mem[2]", "mem_2", "g[0].x", "x_g_0"};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->__Vdpihook_id[i] = static_cast<int>(i + 1);
        topp->__Vdpihook_path[i][0] = paths[i];
    }

    for (int cyc = 0; cyc < 4; ++cyc) {
        topp->clk = 1;
        topp->eval();
        topp->clk = 0;
        topp->eval();
        printf("[%d] elem=%02x var=%02x gen=%02x scoped=%02x design=%02x\n", cyc, topp->o_elem,
               topp->o_var, topp->o_gen, topp->o_scoped, topp->o_design);
    }
    topp->final();
    return 0;
}
