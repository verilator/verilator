// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Evaluate two models on the same DPI call stack
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "Va.h"
#include "Vb.h"

static Vb* bp;
extern "C" void b_ex();
extern "C" int b_imp() {
    b_ex();
    return 0;
}
extern "C" int step_b() {
    bp->eval();
    return 1;
}
int main() {
    VerilatedContext ctx;
    Vb b{&ctx, "b"};
    bp = &b;
    Va a{&ctx, "a"};
    a.eval();
    a.final();
    b.final();
    return 0;
}
