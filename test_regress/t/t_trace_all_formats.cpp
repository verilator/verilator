// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_fst_c.h>
#include <verilated_saif_c.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->traceEverOn(true);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top"}};

    // All formats at the same time, each dumped after the same evaluations
    const std::unique_ptr<VerilatedVcdC> vcdp{new VerilatedVcdC};
    const std::unique_ptr<VerilatedFstC> fstp{new VerilatedFstC};
    const std::unique_ptr<VerilatedSaifC> saifp{new VerilatedSaifC};
    topp->trace(vcdp.get(), 99);
    topp->trace(fstp.get(), 99);
    topp->trace(saifp.get(), 99);
    vcdp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
    fstp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.fst");
    saifp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.saif");
    const auto dump = [&]() {
        vcdp->dump(contextp->time());
        fstp->dump(contextp->time());
        saifp->dump(contextp->time());
    };

    // Same stimulus as the main the test driver generates, for the same traces
    topp->eval();
    dump();
    topp->clk = false;
    contextp->timeInc(10);
    while (contextp->time() < 1100 && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        dump();
        contextp->timeInc(5);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    vcdp->close();
    fstp->close();
    saifp->close();
    return 0;
}
