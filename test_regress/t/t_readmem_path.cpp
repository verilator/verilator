// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

#include <verilated.h>
#include <verilated_syms.h>
#include <verilated_vcd_c.h>
#include <map>
#include <string>

#include "Vt_readmem_path.h"

using namespace std;

int main(int argc, char **argv, char **env) {
    Vt_readmem_path *top = new Vt_readmem_path("top");
    Verilated::setVerilogIODir("t");

    top->eval();
    top->final();
    VL_PRINTF ("*-* All Finished *-*\n");
    return 0;
}
