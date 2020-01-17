// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "Vt_var_overwidth_bad.h"
#include "verilated.h"

//======================================================================

double main_time;

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

    main_time = 0;

    topp->clk = 0;
    topp->eval();
    main_time += 10;

    topp->clk = 0x2;  // ILLEGAL
    topp->eval();
    topp->final();

    VL_DO_DANGLING(delete topp, topp);
    exit(0L);
}
