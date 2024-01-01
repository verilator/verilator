// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Pre C-Emit stage changes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3UNROLL_H_
#define VERILATOR_V3UNROLL_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3ThreadSafety.h"

//============================================================================
/// Unroller with saved state, so caller can determine when pushDelete's are executed.

class UnrollVisitor;

class UnrollStateful final {
    // MEMBERS
    UnrollVisitor* const m_unrollerp;
    VL_UNCOPYABLE(UnrollStateful);

public:
    // CONSTRUCTORS
    UnrollStateful() VL_MT_DISABLED;
    ~UnrollStateful() VL_MT_DISABLED;
    // METHODS
    void unrollGen(AstNodeFor* nodep, const string& beginName) VL_MT_DISABLED;
    void unrollAll(AstNetlist* nodep) VL_MT_DISABLED;
};

//============================================================================

class V3Unroll final {
public:
    static void unrollAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
