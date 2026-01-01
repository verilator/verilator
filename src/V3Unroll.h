// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Loop unroller
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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

//============================================================================
// Generate loop unroller

class UnrollGenVisitor;

class GenForUnroller final {
    // MEMBERS
    UnrollGenVisitor* const m_unrollerp;

public:
    // CONSTRUCTOR
    GenForUnroller() VL_MT_DISABLED;
    ~GenForUnroller() VL_MT_DISABLED;
    // METHODS
    void unroll(AstGenFor* nodep, const std::string& beginName) VL_MT_DISABLED;
};

//============================================================================
// Loop statement unroller

class V3Unroll final {
public:
    static void unrollAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
