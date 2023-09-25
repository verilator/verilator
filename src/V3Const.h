// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Propagate constants across AST
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

#ifndef VERILATOR_V3CONST_H_
#define VERILATOR_V3CONST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3ThreadSafety.h"

//============================================================================

class V3Const final {
public:
    static AstNode* constifyParamsEdit(AstNode* nodep) VL_MT_DISABLED;
    static AstNodeExpr* constifyParamsEdit(AstNodeExpr* exprp) VL_MT_DISABLED {
        return VN_AS(constifyParamsEdit(static_cast<AstNode*>(exprp)), NodeExpr);
    }
    static AstNode* constifyParamsNoWarnEdit(AstNode* nodep) VL_MT_DISABLED;
    static AstNodeExpr* constifyParamsNoWarnEdit(AstNodeExpr* exprp) VL_MT_DISABLED {
        return VN_AS(constifyParamsNoWarnEdit(static_cast<AstNode*>(exprp)), NodeExpr);
    }
    static AstNode* constifyGenerateParamsEdit(AstNode* nodep) VL_MT_DISABLED;
    // Only do constant pushing, without removing dead logic
    static void constifyAllLive(AstNetlist* nodep) VL_MT_DISABLED;
    // Everything that's possible
    static void constifyAll(AstNetlist* nodep) VL_MT_DISABLED;
    // Also, warn
    static void constifyAllLint(AstNetlist* nodep) VL_MT_DISABLED;
    // C++ datatypes
    static void constifyCpp(AstNetlist* nodep) VL_MT_DISABLED;
    // Only the current node and lower
    // Return new node that may have replaced nodep
    static AstNode* constifyEditCpp(AstNode* nodep) VL_MT_DISABLED;
    static AstNodeExpr* constifyEditCpp(AstNodeExpr* exprp) VL_MT_DISABLED {
        return VN_AS(constifyEditCpp(static_cast<AstNode*>(exprp)), NodeExpr);
    }
    // Only the current node and lower
    // Return new node that may have replaced nodep
    static AstNode* constifyEdit(AstNode* nodep) VL_MT_DISABLED;
    static AstNodeExpr* constifyEdit(AstNodeExpr* exprp) VL_MT_DISABLED {
        return VN_AS(constifyEdit(static_cast<AstNode*>(exprp)), NodeExpr);
    }
    // Only the current node and lower, with special SenTree optimization
    // Return new node that may have replaced nodep
    static AstNode* constifyExpensiveEdit(AstNode* nodep) VL_MT_DISABLED;
};

#endif  // Guard
