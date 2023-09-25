// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Makefile
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3EMITMK_H_
#define VERILATOR_V3EMITMK_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3ThreadSafety.h"

class V3HierBlockPlan;

//============================================================================

class V3EmitMk final {
public:
    // Number of source files after which to use parallel compiles
    static const size_t PARALLEL_FILE_CNT_THRESHOLD = 128;

    static void emitmk() VL_MT_DISABLED;
    static void emitHierVerilation(const V3HierBlockPlan* planp) VL_MT_DISABLED;
};

#endif  // Guard
