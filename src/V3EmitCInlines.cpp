// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <map>

//######################################################################

class EmitCInlines final : EmitCBaseVisitor {
    // STATE

    // METHODS

    // VISITORS
    virtual void visit(AstCNew* nodep) override {
        if (v3Global.opt.savable())
            v3warn(E_UNSUPPORTED, "Unsupported: --savable with dynamic new");
        iterateChildren(nodep);
    }
    virtual void visit(AstDumpCtl* nodep) override {
        if (v3Global.opt.trace()) v3Global.needTraceDumper(true);
        iterateChildren(nodep);
    }

    //---------------------------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit EmitCInlines(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCInlines(v3Global.rootp());
}
