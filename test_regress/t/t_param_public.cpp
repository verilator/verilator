// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2006 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_param_public.h"
#include "Vt_param_public_p.h"
#include "Vt_param_public_t.h"

// C++ wrappers use public parameters in constant expressions, including aggregate elements.
static_assert(Vt_param_public_t::TOP_PARAM == 30, "Overridden module parameter");
static_assert(Vt_param_public_p::INPACK == 6, "Package parameter");
static_assert(Vt_param_public_t::REAL_PARAM == 1.25, "Real parameter");
static_assert(Vt_param_public_t::WIDE_PARAM.m_storage[1] == 0x9abcdef0, "Wide parameter");
static_assert(Vt_param_public_t::ARRAY_PARAM[1] == 5, "Unpacked array parameter");

double sc_time_stamp() { return 0; }

int main(int argc, char* argv[]) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);

    VM_PREFIX* topp = new VM_PREFIX;

    // Taking the address also requires an out-of-line definition in C++14.
    const IData* volatile paramp = &Vt_param_public_t::TOP_PARAM;
    if (*paramp != 30) { vl_fatal(__FILE__, __LINE__, "dut", "bad value"); }
    if (static_cast<int>(Vt_param_public_p::INPACK) != 0) {}

    for (int i = 0; i < 10; i++) {  //
        topp->eval();
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}
