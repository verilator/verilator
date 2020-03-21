// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Estimate instruction count to run the logic
//                         we would generate for any given AST subtree.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3INSTRCOUNT_H_
#define _V3INSTRCOUNT_H_ 1

#include "config_build.h"
#include "verilatedos.h"

class AstNode;

class V3InstrCount {
public:
    // Return the estimate count of instructions we'd incur while running
    // code in and under nodep.
    //
    // This is a rough estimate; we don't know what path we'll take through
    // conditionals in nodep, so we assume we take the longest path.
    //
    // If nodep is an AstActive, returns 0.
    // If nodep contains nested AstActives, raises an error.
    //
    // If assertNoDups is true, marks user5 on each AstNode scanned.  Then
    // if we see the same node twice (across more than one call to count,
    // potentially) raises an error.
    // Optional osp is stream to dump critical path to.
    static uint32_t count(AstNode* nodep, bool assertNoDups, std::ostream* osp = NULL);
};

#endif  // guard
