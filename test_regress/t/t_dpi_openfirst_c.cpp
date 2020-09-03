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

#include <cstdio>
#include <cstring>
#include <iostream>
#include "svdpi.h"

//======================================================================

#if defined(VERILATOR)
# include "Vt_dpi_openfirst__Dpi.h"
#elif defined(VCS)
# include "../vc_hdrs.h"
#elif defined(NC)
# define NEED_EXTERNS
#else
# error "Unknown simulator for DPI test"
#endif

#ifdef NEED_EXTERNS
extern "C" {
    // If get ncsim: *F,NOFDPI: Function {foo} not found in default libdpi.
    // Then probably forgot to list a function here.

    extern int dpii_failure();
    extern void dpii_open_i(const svOpenArrayHandle i, const svOpenArrayHandle o);
}
#endif

//======================================================================

int failure = 0;
int dpii_failure() { return failure; }

#define CHECK_RESULT_HEX(got, exp) \
    do { \
        if ((got) != (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP=" << (exp) << std::endl; \
            failure = __LINE__; \
        } \
    } while (0)

//======================================================================

void dpii_open_i(const svOpenArrayHandle i, const svOpenArrayHandle o) {
    // Illegal in VCS:
    // CHECK_RESULT_HEX(svLeft(i, 0), 2);
    // CHECK_RESULT_HEX(svRight(i, 0), 0);
    // CHECK_RESULT_HEX(svLow(i, 0), 0);
    // CHECK_RESULT_HEX(svHigh(i, 0), 2);
    //
    CHECK_RESULT_HEX(svDimensions(i), 1);
    CHECK_RESULT_HEX(svLeft(i, 1), 2);
    CHECK_RESULT_HEX(svRight(i, 1), 0);
    CHECK_RESULT_HEX(svLow(i, 1), 0);
    CHECK_RESULT_HEX(svHigh(i, 1), 2);
    // CHECK_RESULT_HEX(svIncrement(i, 1), 0);
    CHECK_RESULT_HEX(svSize(i, 1), 3);
    for (int a = 0; a < 3; ++a) {
        svBitVecVal vec[1];
        svGetBitArrElemVecVal(vec, i, a);
        vec[0] = ~vec[0];
        svPutBitArrElemVecVal(o, vec, a);
    }
}
