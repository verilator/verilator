// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

//======================================================================

#include VM_PREFIX_INCLUDE_DPI

#ifdef NEED_EXTERNS
extern "C" {
extern int dpix_task(void);
}
#endif

//======================================================================

int dpix_run_tests(void) {
    dpix_task();  // Wrong scope
    return 0;
}
