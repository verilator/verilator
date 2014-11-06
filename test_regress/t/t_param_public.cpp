// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

#include <verilated.h>
#include "Vt_param_public.h"

#include "Vt_param_public_p.h"

int main (int argc, char *argv[]) {
    Vt_param_public *topp = new Vt_param_public;

    Verilated::debug(0);

    // Make sure public tag worked
    if (Vt_param_public_p::INPACK) {}

    for (int i = 0; i < 10; i++) {
	topp->eval();
    }
}
