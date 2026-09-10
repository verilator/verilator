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

extern void dpi_export(unsigned int i);

static long long int SIZE = 1 << 14;

static int rec(int n) {
    int big_array[SIZE];
    int cn = n;
    big_array[0] = cn;
    for (int i = 1; i < SIZE; i++) { big_array[i] = big_array[i - 1] + cn++; }
    if (n < 1) return n;
    return rec(n - 1) + big_array[SIZE - 1];
}

int dpi_import(unsigned int len) {
    char big_array[SIZE];
    printf("dpi_import: len=%d\n", len);
    printf("rec(%d) = %d\n", len, rec(len));
    return 0;
}

#ifdef __cplusplus
}
#endif
