// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_dpi_vams.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_vams__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

#ifdef NEED_EXTERNS
extern "C" {
extern void dpii_call(double in, double* outp);
}
#endif

void dpii_call(double in, double* outp) { *outp = in + 0.1; }
//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = nullptr;

int main(int argc, char* argv[]) {
    topp = new VM_PREFIX;

    Verilated::debug(0);

    topp->in = 1.1;
    topp->eval();
    if (topp->out != 1.2) {
        VL_PRINTF("*-* All Finished *-*\n");
        topp->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results\n");
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    return 0;
}
