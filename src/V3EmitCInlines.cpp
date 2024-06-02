// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "V3PchAstMT.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class EmitCInlines final : EmitCBaseVisitorConst {
    // STATE

    // METHODS

    // VISITORS
    void visit(AstCNew* nodep) override {
        if (v3Global.opt.savable())
            v3warn(E_UNSUPPORTED, "Unsupported: --savable with dynamic new");
        iterateChildrenConst(nodep);
    }
    void visit(AstDumpCtl* nodep) override {
        if (v3Global.opt.trace()) v3Global.needTraceDumper(true);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeDistBiop* nodep) override {
        v3Global.setUsesProbDist();
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeDistTriop* nodep) override {
        v3Global.setUsesProbDist();
        iterateChildrenConst(nodep);
    }

    //---------------------------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit EmitCInlines(AstNetlist* nodep) { iterateConst(nodep); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { EmitCInlines{v3Global.rootp()}; }
}
