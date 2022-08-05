// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

#include "verilatedos.h"

#include "verilated.h"

#include <memory>
#if VM_TRACE
#include "verilated_vcd_c.h"
#endif

#include VM_PREFIX_INCLUDE
#include VM_PREFIX_ROOT_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    srand48(5);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{"top"}};

    topp->clk = false;
    topp->rst = true;
    topp->eval();
#if VM_TRACE
    contextp->traceEverOn(true);
    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};
    topp->trace(tfp.get(), 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
    tfp->dump(contextp->time());
#endif
    contextp->timeInc(5);

    topp->clk = true;
    topp->eval();
    topp->rst = false;
    topp->eval();
#if VM_TRACE
    tfp->dump(contextp->time());
#endif
    contextp->timeInc(5);

    while (contextp->time() < 1000 && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();

        if (topp->clk) {
            bool needsSecondEval = false;

            if (topp->cyc == 13) {
                topp->rootp->t__DOT__var_1__VforceEn = 1;
                topp->rootp->t__DOT__var_1__VforceVal = 1;
                needsSecondEval = true;
            }
            if (topp->cyc == 15) {
                topp->rootp->t__DOT__var_1__VforceVal = 0;
                needsSecondEval = true;
            }
            if (topp->cyc == 18) {
                topp->rootp->t__DOT__var_1__VforceEn = 0;
                needsSecondEval = true;
            }

            if (topp->cyc == 14) {
                topp->rootp->t__DOT__var_8__VforceEn = 0xff;
                topp->rootp->t__DOT__var_8__VforceVal = 0xf5;
                needsSecondEval = true;
            }
            if (topp->cyc == 16) {
                topp->rootp->t__DOT__var_8__VforceVal = 0x5f;
                needsSecondEval = true;
            }
            if (topp->cyc == 19) {
                topp->rootp->t__DOT__var_8__VforceEn = 0;
                needsSecondEval = true;
            }

            if (topp->cyc == 20) {
                topp->rootp->t__DOT__var_1__VforceEn = 1;
                topp->rootp->t__DOT__var_8__VforceEn = 0xff;
                topp->rootp->t__DOT__var_1__VforceVal = 1;
                topp->rootp->t__DOT__var_8__VforceVal = 0x5a;
                needsSecondEval = true;
            }
            if (topp->cyc == 22) {
                topp->rootp->t__DOT__var_1__VforceVal = 0;
                topp->rootp->t__DOT__var_8__VforceVal = 0xa5;
                needsSecondEval = true;
            }
            if (topp->cyc == 24) {
                topp->rootp->t__DOT__var_1__VforceEn = 0;
                topp->rootp->t__DOT__var_8__VforceEn = 0;
                needsSecondEval = true;
            }

            if (needsSecondEval) topp->eval();
        }
#if VM_TRACE
        tfp->dump(contextp->time());
#endif
        contextp->timeInc(5);
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }

    topp->final();
#if VM_TRACE
    tfp->close();
#endif

    return 0;
}
