// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Yu-Sheng Lin.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include "Vt_trace_noflag_bad.h"

int main(int argc, char** argv) {
    std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->traceEverOn(true);
    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get()}};
    topp->trace(tfp.get(), 99);  // Error!
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/dump.vcd");  // Error! shall put to the next line!
    tfp->dump(0);
    tfp->close();
    return 0;
}
