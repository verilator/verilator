// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: $finish propagation through DPI re-entry
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************

#if defined(VERILATOR)
#include "Vt_finish_call_propagation__Dpi.h"
#else
extern "C" int sv_finish_export();
#endif

extern "C" int dpi_reenter_finish() { return sv_finish_export(); }

extern "C" int dpi_pure_value(int value) { return value + 1; }
