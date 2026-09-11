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

extern void dpi_export_task(void);
extern int dpi_export_function(void);

int dpi_import_function1(void) {
    printf("Calling dpi_export_function()\n");
    (void)dpi_export_function();
    printf("Calling dpi_export_task()\n");
    dpi_export_task();
    return 0;
}

int dpi_import_function2(void) {
    printf("Returning to dpi_export_function()\n");
    return 0;
}

#ifdef __cplusplus
}
#endif
