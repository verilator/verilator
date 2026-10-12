// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <cstdio>
#include <cstdlib>
#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void pong(int n);

int ping(int n) {
    printf("Called ping(%d)\n", n);
    if (n == 0) return 0;
    pong(n);
    return 0;
}

#ifdef __cplusplus
}
#endif
