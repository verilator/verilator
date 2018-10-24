// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit pybind11 binding code
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

#include "V3Global.h"
#include "V3String.h"
#include "V3EmitPy.h"
#include "V3File.h"
#include "V3EmitCBase.h"

#include <memory>

static void emitPy(AstNodeModule* modp) {
    string filename = v3Global.opt.makeDir()+"/"+ v3Global.opt.prefix() + "_py.h";
    EmitCBaseVisitor::newCFile(filename, false, false);
    vl_unique_ptr<V3OutCFile> ofp(new V3OutCFile(filename));
    
    ofp->putsHeader();

    ofp->puts("// DESCRIPTION: Verilator output: Primary design python wrappers\n\n");

    // Always have this first; gcc has short circuiting if #ifdef is first in a file
    ofp->puts("#ifndef _" + v3Global.opt.prefix() + "_PY_H_\n");
    ofp->puts("#define _" + v3Global.opt.prefix() + "_PY_H_\n");
    ofp->puts("\n");

    ofp->puts("#include \"" + v3Global.opt.prefix() + ".h\"\n");
	ofp->puts("#include \"verilated_py.h\"\n");
    ofp->puts("\n");
    ofp->puts("namespace vl_py {\n");

    ofp->puts("inline auto declare_" + v3Global.opt.prefix() + "(pybind11::module& m) {\n");
	ofp->puts("return VL_PY_MODULE(m, "+v3Global.opt.prefix()+")\n");

    for (AstNode* nodep=modp->stmtsp(); nodep; nodep = nodep->nextp()) {
        const AstVar* varp = VN_CAST(nodep, Var);
        //Export top level ports
        if (varp && varp->isIO()) {
            ofp->puts("\tVL_PY_PORT("+v3Global.opt.prefix()+", "+nodep->name()+")\n");
        }
        //Export non const parameters
        if (varp && varp->isParam() && !VN_IS(varp->valuep(), Const)) {
            ofp->puts("\tVL_PY_PARAM("+v3Global.opt.prefix()+","+nodep->name()+")\n");
        }
        //Export public functions
        const AstCFunc* funcp = VN_CAST(nodep, CFunc);
        if (funcp && !funcp->skipDecl() && !funcp->dpiImport() && funcp->funcPublic()) {
            if (funcp->ifdef()!="") ofp->puts("#ifdef "+funcp->ifdef()+"\n");
            ofp->puts((funcp->isStatic().trueU() ? "\tVL_PY_FUNC_STATIC(" : "\tVL_PY_FUNC("));
            ofp->puts(v3Global.opt.prefix()+", " + funcp->name() + ")\n");
            if (funcp->ifdef()!="") ofp->puts("#endif // "+funcp->ifdef()+"\n");
        }
    }

    ofp->puts("\tVL_PY_FUNC("+v3Global.opt.prefix()+", eval)\n");
    ofp->puts("\tVL_PY_FUNC("+v3Global.opt.prefix()+", final)\n");

    if (v3Global.opt.trace()) {
        ofp->puts("\tVL_PY_FUNC_TRACE("+v3Global.opt.prefix()+")\n");
    }
    
    if (v3Global.opt.inhibitSim()) {
	    ofp->puts("\tVL_PY_FUNC("+v3Global.opt.prefix()+", inhibitSim)\n");
	}

    ofp->puts("\t;\n}\n\n} // namespace vl_py\n\n");

    // finish up h-file
    ofp->puts("#endif // guard\n");
}

//######################################################################
// EmitC class functions

void V3EmitPy::emitpy() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Process each module in turn
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=VN_CAST(nodep->nextp(), NodeModule)) {
        if (nodep->isTop()) {
            emitPy(nodep);
        }
    }
}
