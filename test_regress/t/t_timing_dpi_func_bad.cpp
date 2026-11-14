// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include <cstdio>
#include <cstdlib>
#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void dpi_export_task(void);
extern void dpi_export_func(void);

int dpi_import_calls_func() {
    printf("Calling dpi_export_func\n");
    dpi_export_func();
    return 0;
}

int dpi_import_calls_task() {
    printf("Calling dpi_export_task\n");
    dpi_export_task();
    return 0;
}

#ifdef __cplusplus
}
#endif
