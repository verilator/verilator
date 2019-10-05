// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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
    virtual void visit(AstBasicDType* nodep) {
        if (nodep->keyword() == AstBasicDTypeKwd::STRING) {
            // Request #include <string> via verilated_heavy.h when we create symbol file
            v3Global.needHeavy(true);
        }
    }
    virtual void visit(AstValuePlusArgs* nodep) {
        v3Global.needHeavy(true);
        iterateChildren(nodep);
    }

    // Default
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
    //---------------------------------------
    // ACCESSORS
public:
    explicit EmitCInlines(AstNetlist* nodep) {
        iterate(nodep);
        if (v3Global.needHInlines()) {
            emitInt();
        }
    }
};

void EmitCInlines::emitInt() {
    string filename = v3Global.opt.makeDir()+"/"+topClassName()+"__Inlines.h";
    newCFile(filename, false/*slow*/, false/*source*/);
    V3OutCFile hf (filename);
    m_ofp = &hf;

    ofp()->putsHeader();
    puts("#ifndef _"+topClassName()+"__Inlines_H_\n");
    puts("#define _"+topClassName()+"__Inlines_H_\n");
    puts("\n");

    puts("#include \"verilated.h\"\n");

    puts("\n//======================\n\n");

    // Placeholder - v3Global.needHInlines(true) currently not used

    puts("//======================\n\n");
    puts("#endif  // guard\n");
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitCInlines syms (v3Global.rootp());
}
