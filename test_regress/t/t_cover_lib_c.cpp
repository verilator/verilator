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

#include "verilated_cov.h"

#include VM_PREFIX_INCLUDE

double sc_time_stamp() { return 0; }

//======================================================================

int failure = 0;

#define CHECK_RESULT_HEX(got, exp) \
    do { \
        if ((got) != (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP=" << (exp) << std::endl; \
            failure = __LINE__; \
        } \
    } while (0)

//======================================================================

const char* name() { return "main"; }

int main() {
    vluint32_t covers[1];
    vluint64_t coverw[2];

    VL_COVER_INSERT(&covers[0], "comment", "kept_one");
    VL_COVER_INSERT(&coverw[0], "comment", "kept_two");
    VL_COVER_INSERT(&coverw[1], "comment", "lost_three");

    covers[0] = 100;
    coverw[0] = 210;
    coverw[1] = 220;

    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage1.dat");
    VerilatedCov::clearNonMatch("kept_");
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage2.dat");
    VerilatedCov::zero();
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage3.dat");
    VerilatedCov::clear();
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage4.dat");

    printf("*-* All Finished *-*\n");
    exit(failure ? 10 : 0);
}
