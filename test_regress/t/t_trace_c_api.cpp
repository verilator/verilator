// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE

extern void vcdTestMain(const char* filenamep);

int main(int argc, char** argv, char** env) {
    const char* filenamep = VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd";
    printf("Writing %s\n", filenamep);
    vcdTestMain(filenamep);
    printf("*-* All Finished *-*\n");
    return 0;
}
