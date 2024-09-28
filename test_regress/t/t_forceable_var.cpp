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
    VerilatedContext context;
    context.debug(0);
    context.commandArgs(argc, argv);
    srand48(5);

    VM_PREFIX top{"top"};

    top.clk = false;
    top.rst = true;
    top.eval();
#if VM_TRACE
    context.traceEverOn(true);
    VerilatedVcdC tf;
    top.trace(&tf, 99);
    tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
    tf.dump(context.time());
#endif
    context.timeInc(5);

    top.clk = true;
    top.eval();
    top.rst = false;
    top.eval();
#if VM_TRACE
    tf.dump(context.time());
#endif
    context.timeInc(5);

    while (context.time() < 1000 && !context.gotFinish()) {
        top.clk = !top.clk;
        top.eval();

        if (top.clk) {
            bool needsSecondEval = false;

            if (top.cyc == 13) {
                top.rootp->t__DOT__var_1__VforceEn = 1;
                top.rootp->t__DOT__var_1__VforceVal = 1;
                needsSecondEval = true;
            }
            if (top.cyc == 15) {
                top.rootp->t__DOT__var_1__VforceVal = 0;
                needsSecondEval = true;
            }
            if (top.cyc == 18) {
                top.rootp->t__DOT__var_1__VforceEn = 0;
                needsSecondEval = true;
            }

            if (top.cyc == 14) {
                top.rootp->t__DOT__var_8__VforceEn = 0xff;
                top.rootp->t__DOT__var_8__VforceVal = 0xf5;
                needsSecondEval = true;
            }
            if (top.cyc == 16) {
                top.rootp->t__DOT__var_8__VforceVal = 0x5f;
                needsSecondEval = true;
            }
            if (top.cyc == 19) {
                top.rootp->t__DOT__var_8__VforceEn = 0;
                needsSecondEval = true;
            }

            if (top.cyc == 20) {
                top.rootp->t__DOT__var_1__VforceEn = 1;
                top.rootp->t__DOT__var_8__VforceEn = 0xff;
                top.rootp->t__DOT__var_1__VforceVal = 1;
                top.rootp->t__DOT__var_8__VforceVal = 0x5a;
                needsSecondEval = true;
            }
            if (top.cyc == 22) {
                top.rootp->t__DOT__var_1__VforceVal = 0;
                top.rootp->t__DOT__var_8__VforceVal = 0xa5;
                needsSecondEval = true;
            }
            if (top.cyc == 24) {
                top.rootp->t__DOT__var_1__VforceEn = 0;
                top.rootp->t__DOT__var_8__VforceEn = 0;
                needsSecondEval = true;
            }

            if (needsSecondEval) top.eval();
        }
#if VM_TRACE
        tf.dump(context.time());
#endif
        context.timeInc(5);
    }

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }

    top.final();
#if VM_TRACE
    tf.close();
#endif

    return 0;
}
