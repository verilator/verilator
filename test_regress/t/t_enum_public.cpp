// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include "Vt_enum_public.h"

#include "Vt_enum_public_p3.h"
#include "Vt_enum_public_p62.h"

int main(int argc, char* argv[]) {
    Vt_enum_public* topp = new Vt_enum_public;

    Verilated::debug(0);

    // Make sure public tag worked
    if (Vt_enum_public_p3::ZERO == Vt_enum_public_p3::ONE) {}
    if (Vt_enum_public_p62::ZERO == Vt_enum_public_p62::ALLONE) {}

    for (int i = 0; i < 10; i++) {
        topp->eval();
    }
}
