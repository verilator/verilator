// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2018 by Wilson Snyder.  This program is free software; you can
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
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <map>
#include <vector>

#include "V3Global.h"
#include "V3EmitC.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

//######################################################################

class EmitCInlines : EmitCBaseVisitor {
    // STATE

    // METHODS
    void emitInt();

    // VISITORS
    virtual void visit(AstBasicDType* nodep) {
	if (nodep->keyword() == AstBasicDTypeKwd::STRING) {
	    v3Global.needHeavy(true);  // #include <string> via verilated_heavy.h when we create symbol file
	}
    }

    // NOPs
    virtual void visit(AstNodeStmt*) {}
    // Default
    virtual void visit(AstNode* nodep) {
	nodep->iterateChildren(*this);
    }
    //---------------------------------------
    // ACCESSORS
public:
    explicit EmitCInlines(AstNetlist* nodep) {
	nodep->accept(*this);
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
    puts("#endif // guard\n");
}

//######################################################################
// EmitC class functions

void V3EmitC::emitcInlines() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitCInlines syms (v3Global.rootp());
}
