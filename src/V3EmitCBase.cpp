// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit C++ for tree
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3EmitCBase.h"

//######################################################################
// EmitCBaseVisitor implementation

string EmitCBaseVisitor::funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp) {
    modp = modp ? modp : VN_CAST(nodep->user4p(), NodeModule);
    string name;
    if (nodep->isConstructor()) {
        name += prefixNameProtect(modp);
    } else if (nodep->isDestructor()) {
        name += "~";
        name += prefixNameProtect(modp);
    } else {
        if (nodep->isLoose()) {
            name += prefixNameProtect(modp);
            name += "__";
        }
        name += nodep->nameProtect();
    }
    return name;
}

AstCFile* EmitCBaseVisitor::newCFile(const string& filename, bool slow, bool source) {
    AstCFile* cfilep = new AstCFile(v3Global.rootp()->fileline(), filename);
    cfilep->slow(slow);
    cfilep->source(source);
    v3Global.rootp()->addFilesp(cfilep);
    return cfilep;
}

string EmitCBaseVisitor::cFuncArgs(const AstCFunc* nodep) {
    // Return argument list for given C function
    string args;
    if (nodep->isLoose() && !nodep->isStatic()) {
        if (nodep->isConst().trueKnown()) args += "const ";
        AstNodeModule* modp = VN_CAST(nodep->user4p(), NodeModule);
        args += prefixNameProtect(modp);
        args += "* vlSelf";
    }
    if (!nodep->argTypes().empty()) {
        if (!args.empty()) args += ", ";
        args += nodep->argTypes();
    }
    // Might be a user function with argument list.
    for (const AstNode* stmtp = nodep->argsp(); stmtp; stmtp = stmtp->nextp()) {
        if (const AstVar* portp = VN_CAST_CONST(stmtp, Var)) {
            if (portp->isIO() && !portp->isFuncReturn()) {
                if (args != "") args += ", ";
                if (nodep->dpiImportPrototype() || nodep->dpiExportDispatcher()) {
                    args += portp->dpiArgType(true, false);
                } else if (nodep->funcPublic()) {
                    args += portp->cPubArgType(true, false);
                } else {
                    args += portp->vlArgType(true, false, true);
                }
            }
        }
    }
    return args;
}

void EmitCBaseVisitor::emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp,
                                       bool withScope) {
    if (!funcp->isConstructor() && !funcp->isDestructor()) {
        puts(funcp->rtnTypeVoid());
        puts(" ");
    }
    if (withScope && funcp->isProperMethod()) puts(prefixNameProtect(modp) + "::");
    puts(funcNameProtect(funcp, modp));
    puts("(" + cFuncArgs(funcp) + ")");
    if (funcp->isConst().trueKnown() && funcp->isProperMethod()) puts(" const");
}

void EmitCBaseVisitor::emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp,
                                     bool cLinkage) {
    ensureNewLine();
    if (!funcp->ifdef().empty()) puts("#ifdef " + funcp->ifdef() + "\n");
    if (cLinkage) puts("extern \"C\" ");
    if (funcp->isStatic() && funcp->isProperMethod()) puts("static ");
    if (funcp->isVirtual()) {
        UASSERT_OBJ(funcp->isProperMethod(), funcp, "Virtual function is not a proper method");
        puts("virtual ");
    }
    emitCFuncHeader(funcp, modp, /* withScope: */ false);
    if (funcp->slow()) puts(" VL_ATTR_COLD");
    puts(";\n");
    if (!funcp->ifdef().empty()) puts("#endif  // " + funcp->ifdef() + "\n");
}
