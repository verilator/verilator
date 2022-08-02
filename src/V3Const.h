// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Propagate constants across AST
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3CONST_H_
#define VERILATOR_V3CONST_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;
class AstNode;

//============================================================================

class V3Const final {
public:
    static AstNode* constifyParamsEdit(AstNode* nodep);
    static AstNode* constifyGenerateParamsEdit(AstNode* nodep);
    // Only do constant pushing, without removing dead logic
    static void constifyAllLive(AstNetlist* nodep);
    // Everything that's possible
    static void constifyAll(AstNetlist* nodep);
    // Also, warn
    static void constifyAllLint(AstNetlist* nodep);
    // C++ datatypes
    static void constifyCpp(AstNetlist* nodep);
    // Only the current node and lower
    // Return new node that may have replaced nodep
    static AstNode* constifyEditCpp(AstNode* nodep);
    // Only the current node and lower
    // Return new node that may have replaced nodep
    static AstNode* constifyEdit(AstNode* nodep);
    // Only the current node and lower, with special SenTree optimization
    // Return new node that may have replaced nodep
    static AstNode* constifyExpensiveEdit(AstNode* nodep);
};

#endif  // Guard
