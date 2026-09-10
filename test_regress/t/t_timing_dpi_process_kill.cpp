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

extern void v_export(void);

int dpi_import(void) {
    v_export();
    return 0;
}

#ifdef __cplusplus
}
#endif
