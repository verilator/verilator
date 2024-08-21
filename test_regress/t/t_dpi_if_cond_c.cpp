// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2024 by Antmicro. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>
#include <cstring>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_if_cond__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(NC)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

#ifdef NEED_EXTERNS
extern "C" {
// If get ncsim: *F,NOFDPI: Function {foo} not found in default libdpi.
// Then probably forgot to list a function here.

extern int dpii_increment(int* counter);
}
#endif

int dpii_increment(int* counter) {
    ++(*counter);
    return 0;
}
