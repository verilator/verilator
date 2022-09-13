// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test C++ main
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Robert Newgard
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_enum_public_vlt.h"
#include "Vt_enum_public_vlt___024root.h"
#include "Vt_enum_public_vlt_t_pkg.h"

double sc_time_stamp() { return 0; }

int main(int argc, char* argv[]) {
    Vt_enum_public_vlt* topp = new Vt_enum_public_vlt;

    Verilated::debug(0);

    // Check public -enum attributes in verilator_config
    if (Vt_enum_public_vlt_t_pkg::t_enum_1::ENUM_1_0 == Vt_enum_public_vlt_t_pkg::t_enum_1::ENUM_1_1) {}
    if (Vt_enum_public_vlt_t_pkg::t_enum_2::ENUM_2_0 == Vt_enum_public_vlt_t_pkg::t_enum_2::ENUM_2_1) {}
    if (Vt_enum_public_vlt___024root::t__DOT__t_enum_3::ENUM_3_0 == Vt_enum_public_vlt___024root::t__DOT__t_enum_3::ENUM_3_1) {}

    for (int i = 0; i < 10; i++) {  //
        topp->eval();
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}
