// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Assertion expansion
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ASSERT_H_
#define VERILATOR_V3ASSERT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

//============================================================================

class V3AssertCommon final {
public:
    static void collectDefaultDisable(AstNetlist* nodep) VL_MT_DISABLED;
    static void lowerSequenceEvents(AstNetlist* nodep) VL_MT_DISABLED;
    static string assertCtlGetCall(const char* query, VAssertType type,
                                   VAssertDirectiveType directiveType) VL_MT_DISABLED;
    // Check an SVA value is within the implementation limit, else report it on nodep
    static bool checkSvaValueLimit(AstNode* nodep, const AstConst* constp,
                                   const char* what) VL_MT_DISABLED;
    // Fold the bounds of a cycle delay in a sequence, and check they are non-negative
    // elaboration-time constants (IEEE 1800-2023 16.7). If not, report it on errp, and replace
    // them with constants, so later steps do not fail after the error.
    static void checkSvaCycleDelay(AstDelay* nodep, AstNode* errp) VL_MT_DISABLED;
    // True if the expression references a formal argument of a sequence or property
    static bool refsSvaFormal(const AstNode* nodep) VL_MT_DISABLED;
    // Check the cycle delays of a sequence or property instance, after its formal arguments are
    // replaced with the actual arguments (IEEE 1800-2023 16.8), reporting errors on instp
    static void checkSvaInstanceDelays(AstNode* nodep, AstNode* instp) VL_MT_DISABLED;
};

class V3Assert final {
public:
    static void assertAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
