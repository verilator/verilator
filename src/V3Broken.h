// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
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

#ifndef VERILATOR_V3BROKEN_H_
#define VERILATOR_V3BROKEN_H_

#include "config_build.h"
#include "verilatedos.h"

//============================================================================

// Forward declare so we can include this in V3Ast.h
class AstNetlist;
class AstNode;

class V3Broken final {
public:
    static void brokenAll(AstNetlist* nodep);
    static bool isLinkable(const AstNode* nodep);
    static void addNewed(const AstNode* nodep);
    static void deleted(const AstNode* nodep);
    // Called on error to say may be inside visitor,
    // Disables checks that may misfire if not called at stable point between visitors
    static void allowMidvisitorCheck(bool flag);
    static void selfTest();
};

#endif  // Guard
