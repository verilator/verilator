// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
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

#ifndef _V3BROKEN_H_
#define _V3BROKEN_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Broken {
public:
    static void brokenAll(AstNetlist* nodep);
    static void addNewed(AstNode* nodep);
    static void deleted(AstNode* nodep);
    static bool isAllocated(AstNode* nodep);
};

#endif  // Guard
