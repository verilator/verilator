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

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", __FILE__, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        ++failure; \
    }

//======================================================================

double sc_time_stamp() { return 0; }

int failure = 0;

//======================================================================

const char* name() { return "main"; }

int main() {
    vluint32_t covers[1];
    vluint64_t coverw[2];

    VerilatedCovContext* covContextp = Verilated::defaultContextp()->coveragep();

    VL_COVER_INSERT(covContextp, &covers[0], "comment", "kept_one");
    VL_COVER_INSERT(covContextp, &coverw[0], "comment", "kept_two");
    VL_COVER_INSERT(covContextp, &coverw[1], "comment", "lost_three");

    covers[0] = 100;
    coverw[0] = 210;
    coverw[1] = 220;

#ifdef T_COVER_LIB
    CHECK_RESULT_CSTR(covContextp->defaultFilename(), "coverage.dat");
    covContextp->write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage1.dat");
    covContextp->clearNonMatch("kept_");
    covContextp->write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage2.dat");
    covContextp->zero();
    covContextp->write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage3.dat");
    covContextp->clear();
    covContextp->write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage4.dat");
#elif defined(T_COVER_LIB_LEGACY)
    CHECK_RESULT_CSTR(VerilatedCov::defaultFilename(), "coverage.dat");
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage1.dat");
    VerilatedCov::clearNonMatch("kept_");
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage2.dat");
    VerilatedCov::zero();
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage3.dat");
    VerilatedCov::clear();
    VerilatedCov::write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage4.dat");
#else
#error
#endif

    printf("*-* All Finished *-*\n");
    return (failure ? 10 : 0);
}
