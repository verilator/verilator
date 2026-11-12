// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

#include "TestThreads.h"

#include <cstdio>
#include <cstdlib>
#include <svdpi.h>

#ifdef __cplusplus
extern "C" {
#endif

extern void dpi_export();

static int completed = 0;

int dpi_import() {
    dpi_export();
    // Second call tests whether the killed process alters the state after being killed.
    dpi_export();
    ++completed;
    return svIsDisabledState();
}

int c_completed() { return completed; }

int live_threads() { return testLiveThreads(); }

#ifdef __cplusplus
}
#endif
