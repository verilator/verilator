// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_param_public.h"
#include "Vt_param_public_p.h"
#include "Vt_param_public_t.h"

double sc_time_stamp() { return 0; }

int main(int argc, char* argv[]) {
    Vt_param_public* topp = new Vt_param_public;

    Verilated::debug(0);

    // Make sure public tag worked
    if (static_cast<int>(Vt_param_public_t::TOP_PARAM) != 30) {
        vl_fatal(__FILE__, __LINE__, "dut", "bad value");
    }
    if (static_cast<int>(Vt_param_public_p::INPACK) != 0) {}

    for (int i = 0; i < 10; i++) {  //
        topp->eval();
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}
