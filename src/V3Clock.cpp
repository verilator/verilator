// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Post scheduling transformations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Clock's Transformations:
//
//  This pass is historic and does some arbitray post scheduling rewrites
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Clock.h"

#include "V3Const.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor final : public VNVisitor {
    // VISITORS
    void visit(AstSenTree* nodep) override {
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);  // No longer needed
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ClockVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    ~ClockVisitor() override = default;
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ClockVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clock", 0, dumpTreeEitherLevel() >= 3);
}
