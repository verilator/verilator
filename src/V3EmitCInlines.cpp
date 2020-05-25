// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

#include <cmath>
#include <cstdarg>
#include <map>
#include <vector>

//######################################################################

class EmitCInlines : EmitCBaseVisitor {
    // STATE

    // METHODS
    void checkHeavy(AstNode* nodep) {
        if (nodep->isHeavy()) v3Global.needHeavy(true);
    }

    // VISITORS
    virtual void visit(AstClass* nodep) VL_OVERRIDE {
        checkHeavy(nodep);
        v3Global.needC11(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstCNew* nodep) VL_OVERRIDE {
        checkHeavy(nodep);
        if (v3Global.opt.savable()) v3error("Unsupported: --savable with dynamic new");
        iterateChildren(nodep);
    }
    virtual void visit(AstDumpCtl* nodep) VL_OVERRIDE {
        checkHeavy(nodep);
        if (v3Global.opt.trace()) v3Global.needTraceDumper(true);
        iterateChildren(nodep);
    }

    //---------------------------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        checkHeavy(nodep);
        iterateChildren(nodep);
    }

public:
    explicit EmitCInlines(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCInlines(v3Global.rootp());
}
