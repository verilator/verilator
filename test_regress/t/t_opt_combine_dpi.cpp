// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include "svdpi.h"

#include VM_PREFIX_INCLUDE_DPI

static int s_count = 0;  // Number of calls to dpii_f

void dpii_f() { ++s_count; }
int dpii_count() { return s_count; }
