// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VM_PREFIX_INCLUDE

int main(int argc, char* argv[]) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);

    VM_PREFIX* topp = new VM_PREFIX;
    CData small_in1 = 0;
    CData small_in2 = 1;
    IData big_in = 0xffffffff;

    topp->in1(small_in1);
    topp->in2(small_in2);
    topp->in3(big_in);
    topp->in4(big_in);

    topp->eval();

    assert(topp->out1() == 0);
    assert(topp->out2() == 0xffffffff);
    assert(topp->out3().at(0) == 1);
    
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}