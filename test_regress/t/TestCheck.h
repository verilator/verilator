// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2013-2022 by Wilson Snyder. This program is free software; you can
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
static const bool verbose = true;
#else
static const bool verbose = false;
#endif

//======================================================================

// Use cout to avoid issues with %d/%lx etc
#define TEST_CHECK(got, exp, test) \
    do { \
        if (!(test)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ \
                      << ": GOT = " << (got) << "   EXP = " << (exp) << std::endl; \
            ++errors; \
        } \
    } while (0)

#define TEST_CHECK_EQ(got, exp) TEST_CHECK(got, exp, ((got) == (exp)));
#define TEST_CHECK_NE(got, exp) TEST_CHECK(got, exp, ((got) != (exp)));
#define TEST_CHECK_CSTR(got, exp) TEST_CHECK(got, exp, 0 == strcmp((got), (exp)));

#define TEST_CHECK_HEX_EQ(got, exp) \
    do { \
        if ((got) != (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP=" << (exp) << std::endl; \
            ++errors; \
        } \
    } while (0)

#define TEST_CHECK_HEX_NE(got, exp) \
    do { \
        if ((got) == (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP!=" << (exp) << std::endl; \
            ++errors; \
        } \
    } while (0)

#define TEST_CHECK_Z(got) \
    do { \
        if ((got)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT!= NULL   EXP=NULL" << std::endl; \
            ++errors; \
        } \
    } while (0)

#define TEST_CHECK_NZ(got) \
    do { \
        if (!(got)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT= NULL   EXP!=NULL" << std::endl; \
            ++errors; \
        } \
    } while (0)

//======================================================================

#define TEST_VERBOSE_PRINTF(format, ...) \
    do { \
        if (verbose) printf(format, ##__VA_ARGS__); \
    } while (0)

#endif  // Guard
