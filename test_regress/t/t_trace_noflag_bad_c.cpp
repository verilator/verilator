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
    VerilatedContext context;
    context.traceEverOn(true);
    VerilatedVcdC tf;
    VM_PREFIX top{&context};
    top.trace(&tf, 99);  // Error!
    tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/dump.vcd");  // Error! shall put to the next line!
    tf.dump(0);
    tf.close();
    return 0;
}
