// DESCRIPTION: Verilator: DPI stub for t_dpi_inline_new
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Include the Verilator-generated DPI header so the C prototype matches
// the SystemVerilog import expectations.
#include "Vt_dpi_inline_new__Dpi.h"

#ifdef __cplusplus
extern "C" {
#endif

// Stub implementation for _pyhdl_if_PyTuple_GetItem used by pyhdl_if package.
// Returns a null pointer; the SystemVerilog test only checks that the call
// compiles and links.
void* _pyhdl_if_PyTuple_GetItem(void* p0, unsigned long long idx) {
    (void)p0;
    (void)idx;
    return 0;
}

#ifdef __cplusplus
}
#endif
