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

#ifndef VERILATOR_V3EMITCBASE_H_
#define VERILATOR_V3EMITCBASE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"

#include <cmath>
#include <cstdarg>

//######################################################################
// Set user4p in all CFunc and Var to point to the containing AstNodeModule

class EmitCParentModule final {
    // NODE STATE
    //   AstFunc::user4p()      AstNodeModule* Parent module pointer
    //   AstVar::user4p()       AstNodeModule* Parent module pointer
    const VNUser4InUse user4InUse;

public:
    EmitCParentModule();
    VL_UNCOPYABLE(EmitCParentModule);

    static const AstNodeModule* get(const AstNode* nodep) {
        return VN_AS(nodep->user4p(), NodeModule);
    }
};

//######################################################################
// Base Visitor class -- holds output file pointer

class EmitCBaseVisitor VL_NOT_FINAL : public VNVisitor {
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
    static string voidSelfAssign(const AstNodeModule* modp) {
        const string className = prefixNameProtect(modp);
        return className + "* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<" + className
               + "*>(voidSelf);\n";
    }
    static string symClassName() { return v3Global.opt.prefix() + "_" + protect("_Syms"); }
    static string symClassVar() { return symClassName() + "* __restrict vlSymsp"; }
    static string symClassAssign() {
        return symClassName() + "* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;\n";
    }
    static string funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp = nullptr);
    static string prefixNameProtect(const AstNode* nodep) {  // C++ name with prefix
        return v3Global.opt.modPrefix() + "_" + protect(nodep->name());
    }
    static string topClassName() {  // Return name of top wrapper module
        return v3Global.opt.prefix();
    }

    static bool isConstPoolMod(const AstNode* modp) {
        return modp == v3Global.rootp()->constPoolp()->modp();
    }

    static bool isAnonOk(const AstVar* varp) {
        return v3Global.opt.compLimitMembers() != 0  // Enabled
               && !varp->isStatic()  // Not a static variable
               && !varp->isSc()  // Aggregates can't be anon
               && (varp->basicp() && !varp->basicp()->isOpaque());  // Aggregates can't be anon
    }

    static AstCFile* newCFile(const string& filename, bool slow, bool source);
    string cFuncArgs(const AstCFunc* nodep);
    void emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp, bool withScope);
    void emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp, bool cLinkage = false);
    void emitVarDecl(const AstVar* nodep, bool asRef = false);
    void emitModCUse(const AstNodeModule* modp, VUseType useType);
    void emitTextSection(const AstNodeModule* modp, VNType type);

    // CONSTRUCTORS
    EmitCBaseVisitor() = default;
    virtual ~EmitCBaseVisitor() override = default;
};

#endif  // guard
