// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2010 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

//======================================================================

#include "Vt_dpi_export_scope_flat__Dpi.h"

#ifdef NEED_EXTERNS
extern "C" {
extern void dpix_task();
}
#endif

//======================================================================

void dpix_run_tests() {
    dpix_task();  // Wrong scope
}
