// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: VPI test library lacking vlog_startup_routines
//
// Loaded via +verilator+vpi+<path> with no :<bootstrap> entry, to exercise
// the loader's error path when a library defines neither a named bootstrap
// nor the vlog_startup_routines[] array.
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "vpi_user.h"

// Intentionally no vlog_startup_routines and no bootstrap; just some symbol so
// the shared object is non-empty and loads successfully.
extern "C" void t_flag_main_vpi_noarray_present() {}
