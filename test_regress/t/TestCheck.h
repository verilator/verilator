// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef TEST_CHECK_H_
#define TEST_CHECK_H_

extern int errors;

#ifdef TEST_VERBOSE
static bool verbose = true;
#else
static bool verbose = false;
#endif

//======================================================================

// Use cout to avoid issues with %d/%lx etc
#define TEST_CHECK(got, exp, test) \
    if (!(test)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        ++errors; \
    }
#define TEST_CHECK_EQ(got, exp) TEST_CHECK(got, exp, ((got) == (exp)));

#define TEST_VERBOSE_PRINTF(format, ...) \
    do { \
        if (verbose) printf(format, ##__VA_ARGS__); \
    } while (0)

#endif  // Guard
