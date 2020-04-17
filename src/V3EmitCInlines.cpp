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
    void emitInt();

    // VISITORS
    virtual void visit(AstBasicDType* nodep) VL_OVERRIDE {
        if (nodep->keyword() == AstBasicDTypeKwd::STRING) {
            // Request #include <string> via verilated_heavy.h when we create symbol file
            v3Global.needHeavy(true);
        }
    }
    virtual void visit(AstAssocArrayDType* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstClass* nodep) VL_OVERRIDE {
        v3Global.needC11(true);
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstDynArrayDType* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstQueueDType* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeReadWriteMem* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstValuePlusArgs* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstCNew* nodep) VL_OVERRIDE {
        if (v3Global.opt.savable()) v3error("Unsupported: --savable with dynamic new");
        iterateChildren(nodep);
    }
    virtual void visit(AstAtoN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstDumpCtl* nodep) VL_OVERRIDE {
        if (v3Global.opt.trace()) v3Global.needTraceDumper(true);
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstPutcN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstGetcN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstGetcRefN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstSubstrN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }
    virtual void visit(AstCompareNN* nodep) VL_OVERRIDE {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }

    //---------------------------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    explicit EmitCInlines(AstNetlist* nodep) {
        iterate(nodep);
        if (v3Global.needHInlines()) emitInt();
    }
};

void EmitCInlines::emitInt() {
    string filename = v3Global.opt.makeDir() + "/" + topClassName() + "__Inlines.h";
    newCFile(filename, false /*slow*/, false /*source*/);
    V3OutCFile hf(filename);
    m_ofp = &hf;

    ofp()->putsHeader();
    ofp()->putsGuard();
    puts("\n");

    puts("#include \"verilated.h\"\n");

    puts("\n//======================\n\n");

    // Placeholder - v3Global.needHInlines(true) currently not used

    puts("//======================\n\n");
    ofp()->putsEndGuard();
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitCInlines(v3Global.rootp());
}
