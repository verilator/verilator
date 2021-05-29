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

#ifndef VERILATOR_V3EMITCBASE_H_
#define VERILATOR_V3EMITCBASE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3File.h"
#include "V3Ast.h"

#include <cstdarg>
#include <cmath>

//######################################################################
// Base Visitor class -- holds output file pointer

class EmitCBaseVisitor VL_NOT_FINAL : public AstNVisitor {
public:
    // STATE
    V3OutCFile* m_ofp = nullptr;
    bool m_trackText = false;  // Always track AstText nodes
    // METHODS
    V3OutCFile* ofp() const { return m_ofp; }
    void puts(const string& str) { ofp()->puts(str); }
    void putbs(const string& str) { ofp()->putbs(str); }
    void putsDecoration(const string& str) {
        if (v3Global.opt.decoration()) puts(str);
    }
    void putsQuoted(const string& str) { ofp()->putsQuoted(str); }
    void ensureNewLine() { ofp()->ensureNewLine(); }
    bool optSystemC() { return v3Global.opt.systemC(); }
    static string protect(const string& name) { return VIdProtect::protectIf(name, true); }
    static string protectIf(const string& name, bool doIt) {
        return VIdProtect::protectIf(name, doIt);
    }
    static string protectWordsIf(const string& name, bool doIt) {
        return VIdProtect::protectWordsIf(name, doIt);
    }
    static string ifNoProtect(const string& in) { return v3Global.opt.protectIds() ? "" : in; }
    static string symClassName() { return v3Global.opt.prefix() + "_" + protect("_Syms"); }
    static string symClassVar() { return symClassName() + "* __restrict vlSymsp"; }
    static string symClassAssign() {
        return symClassName() + "* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;\n";
    }
    static string funcNameProtect(const AstCFunc* nodep) {
        AstNodeModule* modp = VN_CAST(nodep->user4p(), NodeModule);
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
    static string prefixNameProtect(const AstNode* nodep) {  // C++ name with prefix
        const AstNodeModule* modp = VN_CAST_CONST(nodep, NodeModule);
        if (modp && modp->isTop()) {
            return topClassName();
        } else {
            return v3Global.opt.modPrefix() + "_" + protect(nodep->name());
        }
    }
    static string topClassName() {  // Return name of top wrapper module
        return v3Global.opt.prefix();
    }
    static AstCFile* newCFile(const string& filename, bool slow, bool source) {
        AstCFile* cfilep = new AstCFile(v3Global.rootp()->fileline(), filename);
        cfilep->slow(slow);
        cfilep->source(source);
        v3Global.rootp()->addFilesp(cfilep);
        return cfilep;
    }
    string cFuncArgs(const AstCFunc* nodep) {
        // Return argument list for given C function
        string args;
        if (nodep->isLoose() && nodep->isStatic().falseUnknown()) {
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
                    if (nodep->dpiImport() || nodep->dpiExportWrapper()) {
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

    void emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp, bool withScope) {
        if (!funcp->isConstructor() && !funcp->isDestructor()) {
            puts(funcp->rtnTypeVoid());
            puts(" ");
        }
        if (withScope && funcp->isProperMethod()) puts(prefixNameProtect(modp) + "::");
        puts(funcNameProtect(funcp));
        puts("(" + cFuncArgs(funcp) + ")");
        if (funcp->isConst().trueKnown() && funcp->isProperMethod()) puts(" const");
    }

    void emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp) {
        ensureNewLine();
        if (!funcp->ifdef().empty()) puts("#ifdef " + funcp->ifdef() + "\n");
        if (funcp->isStatic().trueUnknown() && funcp->isProperMethod()) puts("static ");
        if (funcp->isVirtual()) {
            UASSERT_OBJ(funcp->isProperMethod(), funcp, "Virtual function is not a proper method");
            puts("virtual ");
        }
        emitCFuncHeader(funcp, modp, /* withScope: */ false);
        if (funcp->slow()) puts(" VL_ATTR_COLD");
        puts(";\n");
        if (!funcp->ifdef().empty()) puts("#endif  // " + funcp->ifdef() + "\n");
    }

    // CONSTRUCTORS
    EmitCBaseVisitor() = default;
    virtual ~EmitCBaseVisitor() override = default;
};

//######################################################################
// Count operations under the given node, as a visitor of each AstNode

class EmitCBaseCounterVisitor final : public AstNVisitor {
private:
    // MEMBERS
    int m_count = 0;  // Number of statements
    // VISITORS
    virtual void visit(AstNode* nodep) override {
        m_count++;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit EmitCBaseCounterVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~EmitCBaseCounterVisitor() override = default;
    int count() const { return m_count; }
};

#endif  // guard
