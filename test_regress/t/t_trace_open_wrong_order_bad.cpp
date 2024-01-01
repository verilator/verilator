// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Yu-Sheng Lin.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    VerilatedContext ctx;
    VerilatedVcdC tfp;
    Vt_trace_open_wrong_order_bad dut;
    ctx.traceEverOn(true);
    tfp.open(VL_STRINGIFY(TEST_OBJ_DIR) "/dump.vcd");  // Error! shall put to the next line!
    dut.trace(&tfp, 99);  // Error!
    tfp.dump(0);
    tfp.close();
    return 0;
}
