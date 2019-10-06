// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include <cstdio>
#include <cstring>
#include "svdpi.h"

//======================================================================

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

//======================================================================

int dpii_a_func(int i) {
    int o = dpix_a_func(i);
    return o;
}

int dpii_a_task(int i, int* op) {
    int o = 0;
    (void)dpix_a_task(i, op);
    return 0;
}
