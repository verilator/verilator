// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"

#include <cstdio>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

// clang-format off
#if defined(VERILATOR)
# include VM_PREFIX_INCLUDE_DPI
#elif defined(VCS)
# include "../vc_hdrs.h"
#else
# error "Unknown simulator for DPI test"
#endif
// clang-format on

int errors = 0;
int dpii_failure() { return errors; }

// Dimension 0 is the packed dimension; the packed data is passed in the standard C layout
void dpii_action(const svOpenArrayHandle res, const svOpenArrayHandle arg0, int arg1) {
    TEST_CHECK_EQ(svSize(arg0, 0), arg1);
    TEST_CHECK_EQ(svSize(res, 0), arg1);
    TEST_CHECK_EQ(svDimensions(arg0), 0);
    const unsigned char* const argp = static_cast<const unsigned char*>(svGetArrayPtr(arg0));
    unsigned char* const resp = static_cast<unsigned char*>(svGetArrayPtr(res));
    const int bytes = svSizeOfArray(arg0);
    TEST_CHECK_EQ(bytes, svSizeOfArray(res));
    for (int i = 0; i < bytes; ++i) resp[i] = ~argp[i];
    // Unused upper bits of the final byte must remain zero
    if (arg1 % 8) resp[(arg1 - 1) / 8] &= (1U << (arg1 % 8)) - 1;
}

int dpii_width(const svOpenArrayHandle arg0, int dim) { return svSize(arg0, dim); }

int dpii_size(const svOpenArrayHandle arg0, int dim) { return svSize(arg0, dim); }
