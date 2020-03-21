// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include <cstdio>
#include <cstring>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_imp_gen__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(CADENCE)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {
    extern void dpi_genvarTest();
}
#endif

//======================================================================

// Called from our Verilog code to run the tests
void dpi_genvarTest() {
    const char* scopeName = svGetNameFromScope(svGetScope());
    printf("scope name : %s\n", scopeName);
}
