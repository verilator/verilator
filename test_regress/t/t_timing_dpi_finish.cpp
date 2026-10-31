// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE_DPI

#include <cstdio>

extern "C" int imp() {
    ex();
    bump();
    return 0;
}
