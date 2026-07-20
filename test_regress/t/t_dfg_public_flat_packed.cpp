// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "TestCheck.h"
#include "Vt_dfg_public_flat_packed.h"
#include "Vt_dfg_public_flat_packed___024root.h"

#include <iostream>

int errors = 0;

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_dfg_public_flat_packed top{&context};

    top.a = 0;
    top.b = 1;
    top.eval();
    TEST_CHECK_EQ(top.result, 6);
    TEST_CHECK_EQ(top.rootp->t__DOT__result, 6);

    top.rootp->t__DOT__result = 1;
    top.eval();
    TEST_CHECK_EQ(top.result, 6);
    TEST_CHECK_EQ(top.rootp->t__DOT__result, 6);

    top.rootp->t__DOT__partial = 2;
    top.eval();
    TEST_CHECK_EQ(top.partial_out, 2);
    TEST_CHECK_EQ(top.rootp->t__DOT__partial, 2);

    top.rootp->t__DOT__partial = 0;
    top.eval();
    TEST_CHECK_EQ(top.partial_out, 4);
    TEST_CHECK_EQ(top.rootp->t__DOT__partial, 4);

    std::cout << "*-* All Finished *-*\n";
    return errors;
}
