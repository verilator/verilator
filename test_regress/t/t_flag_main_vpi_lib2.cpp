// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Second VPI test library for t_flag_main_vpi_multi
//
// A second, independent VPI library loaded alongside t_flag_main_vpi.cpp via a
// repeated +verilator+vpi+ argument, to verify multiple libraries are loaded.
// Its startup routine prints a marker proving it was loaded; it does not drive
// or finish the simulation (the first library does that).
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

static void lib2_startup() { vpi_printf(const_cast<char*>("second VPI library loaded\n")); }

// IEEE 1800 section 37: vlog_startup_routines[] -- null-terminated array of startup functions
extern "C" {
void (*vlog_startup_routines[])() = {lib2_startup, nullptr};
}
