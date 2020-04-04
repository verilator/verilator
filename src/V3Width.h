// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Node attributes/ expression widths
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

#ifndef _V3WIDTH_H_
#define _V3WIDTH_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Width {
public:
    static int debug();
    static void width(AstNetlist* nodep);
    static AstNode* widthParamsEdit(AstNode* nodep);
    static AstNode* widthGenerateParamsEdit(AstNode* nodep);
    // Final step... Mark all widths as equal
    static void widthCommit(AstNetlist* nodep);

    // For use only in WidthVisitor
    // Replace AstSelBit, etc with AstSel/AstArraySel
    // Returns replacement node if nodep was deleted, or null if none.
    static AstNode* widthSelNoIterEdit(AstNode* nodep);
};

#endif  // Guard
