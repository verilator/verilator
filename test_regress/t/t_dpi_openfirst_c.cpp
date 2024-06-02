// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include "Vt_dpi_openfirst__Dpi.h"
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

extern int dpii_failure();
extern void dpii_open_i(const svOpenArrayHandle i, const svOpenArrayHandle o);
}
#endif

//======================================================================

int errors = 0;
int dpii_failure() { return errors; }

//======================================================================

void dpii_open_i(const svOpenArrayHandle i, const svOpenArrayHandle o) {
    // Illegal in VCS:
    // TEST_CHECK_HEX_EQ(svLeft(i, 0), 2);
    // TEST_CHECK_HEX_EQ(svRight(i, 0), 0);
    // TEST_CHECK_HEX_EQ(svLow(i, 0), 0);
    // TEST_CHECK_HEX_EQ(svHigh(i, 0), 2);
    //
    TEST_CHECK_HEX_EQ(svDimensions(i), 1);
    TEST_CHECK_HEX_EQ(svLeft(i, 1), 2);
    TEST_CHECK_HEX_EQ(svRight(i, 1), 0);
    TEST_CHECK_HEX_EQ(svLow(i, 1), 0);
    TEST_CHECK_HEX_EQ(svHigh(i, 1), 2);
    // TEST_CHECK_HEX_EQ(svIncrement(i, 1), 0);
    TEST_CHECK_HEX_EQ(svSize(i, 1), 3);
    for (int a = 0; a < 3; ++a) {
        svBitVecVal vec[1];
        svGetBitArrElemVecVal(vec, i, a);
        vec[0] = ~vec[0];
        svPutBitArrElemVecVal(o, vec, a);
    }
}
