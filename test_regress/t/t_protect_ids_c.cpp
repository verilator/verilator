// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>
#include <cstring>

//======================================================================

// clang-format off
#if defined(VERILATOR)
# ifdef T_PROTECT_IDS_KEY
#  include "Vt_protect_ids_key__Dpi.h"
# else
#  include "Vt_protect_ids__Dpi.h"
# endif
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
# error "Not supported"
#endif
// clang-format on

//======================================================================

int dpii_a_func(int i) {
    int o = dpix_a_func(i);
    return o;
}

int dpii_a_task(int i, int* op) {
    (void)dpix_a_task(i, op);
    return 0;
}
