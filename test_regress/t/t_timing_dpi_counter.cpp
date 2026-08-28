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

extern void v_export(unsigned int i);
extern void v_export_void(unsigned int i);

int dpi_import(unsigned int len) {
    printf("dpi_import: len=%d\n", len);
    for (int i = 0; i < len; i++) {
        printf("callling v_export: i=%d\n", i);
        v_export(i);
    }
    v_export_void(42);
    return 0;
}

#ifdef __cplusplus
}
#endif
