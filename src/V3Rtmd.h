// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Build the run time model descriptors (RTMD)
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3RTMD_H_
#define VERILATOR_V3RTMD_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3Rtmd final {
public:
    // Build the descriptors
    static void buildAll(AstNetlist* nodep) VL_MT_DISABLED;
    // Finish the descriptors once scoped: untrace the signals of instances not traced, or
    // excluded by control directives, clear the references no longer needed, and reference
    // constants from the constant pool. Must run after V3Scope.
    static void scopedAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
