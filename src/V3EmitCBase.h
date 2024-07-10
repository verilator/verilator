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

#ifndef VERILATOR_V3EMITCBASE_H_
#define VERILATOR_V3EMITCBASE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3ThreadSafety.h"

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

    static const AstNodeModule* get(const AstNode* nodep) VL_MT_STABLE {
        return VN_AS(nodep->user4p(), NodeModule);
    }
};

//######################################################################
// Base Visitor class -- holds output file pointer

class EmitCBase VL_NOT_FINAL {
public:
    static string voidSelfAssign(const AstNodeModule* modp) {
        const string className = prefixNameProtect(modp);
        return className + "* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<" + className
               + "*>(voidSelf);\n";
    }
    static string pchClassName() VL_MT_STABLE { return v3Global.opt.prefix() + "__pch"; }
    static string symClassName() VL_MT_STABLE {
        return v3Global.opt.prefix() + "_" + VIdProtect::protect("_Syms");
    }
    static string symClassVar() { return symClassName() + "* __restrict vlSymsp"; }
    static string symClassAssign() {
        return symClassName() + "* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;\n";
    }
    static string topClassName() VL_MT_SAFE {  // Return name of top wrapper module
        return v3Global.opt.prefix();
    }
    static string prefixNameProtect(const AstNode* nodep) VL_MT_STABLE {  // C++ name with prefix
        return v3Global.opt.modPrefix() + "_" + VIdProtect::protect(nodep->name());
    }
    static bool isAnonOk(const AstVar* varp) {
        AstNodeDType* const dtp = varp->dtypep()->skipRefp();
        return v3Global.opt.compLimitMembers() != 0  // Enabled
               && !varp->isStatic()  // Not a static variable
               && !varp->isSc()  // Aggregates can't be anon
               && !VN_IS(dtp, SampleQueueDType)  // Aggregates can't be anon
               && !(VN_IS(dtp, NodeUOrStructDType) && !VN_CAST(dtp, NodeUOrStructDType)->packed())
               && (varp->basicp() && !varp->basicp()->isOpaque());  // Aggregates can't be anon
    }
    static bool isConstPoolMod(const AstNode* modp) {
        return modp == v3Global.rootp()->constPoolp()->modp();
    }
};

class EmitCBaseVisitorConst VL_NOT_FINAL : public VNVisitorConst, public EmitCBase {
public:
    // STATE
    V3OutCFile* m_ofp = nullptr;
    bool m_trackText = false;  // Always track AstText nodes
    // METHODS
    V3OutCFile* ofp() const VL_MT_SAFE { return m_ofp; }
    void puts(const string& str) { ofp()->puts(str); }
    void putns(const AstNode* nodep, const string& str) { ofp()->putns(nodep, str); }
    void putsHeader() { ofp()->putsHeader(); }
    void putbs(const string& str) { ofp()->putbs(str); }
    void putnbs(const AstNode* nodep, const string& str) { ofp()->putnbs(nodep, str); }
    void putsDecoration(const AstNode* nodep, const string& str) {
        if (v3Global.opt.decoration()) putns(nodep, str);
    }
    void putsQuoted(const string& str) { ofp()->putsQuoted(str); }
    void ensureNewLine() { ofp()->ensureNewLine(); }
    bool optSystemC() { return v3Global.opt.systemC(); }
    static string protect(const string& name) VL_MT_SAFE { return VIdProtect::protect(name); }
    static string protectIf(const string& name, bool doIt) {
        return VIdProtect::protectIf(name, doIt);
    }
    static string protectWordsIf(const string& name, bool doIt) {
        return VIdProtect::protectWordsIf(name, doIt);
    }
    static string ifNoProtect(const string& in) VL_MT_SAFE {
        return v3Global.opt.protectIds() ? "" : in;
    }
    static string funcNameProtect(const AstCFunc* nodep, const AstNodeModule* modp = nullptr);
    static AstCFile* newCFile(const string& filename, bool slow, bool source);
    static AstCFile* createCFile(const string& filename, bool slow, bool source) VL_MT_SAFE;
    string cFuncArgs(const AstCFunc* nodep);
    void emitCFuncHeader(const AstCFunc* funcp, const AstNodeModule* modp, bool withScope);
    void emitCFuncDecl(const AstCFunc* funcp, const AstNodeModule* modp, bool cLinkage = false);
    void emitVarDecl(const AstVar* nodep, bool asRef = false);
    void emitVarAccessors(const AstVar* nodep);
    template <typename F>
    static void forModCUse(const AstNodeModule* modp, VUseType useType, F action) {
        for (AstNode* itemp = modp->stmtsp(); itemp; itemp = itemp->nextp()) {
            if (AstCUse* const usep = VN_CAST(itemp, CUse)) {
                if (usep->useType().containsAny(useType)) {
                    if (usep->useType().containsAny(VUseType::INT_INCLUDE)) {
                        action("#include \"" + prefixNameProtect(usep) + ".h\"\n");
                        continue;  // Forward declaration is not necessary
                    }
                    if (usep->useType().containsAny(VUseType::INT_FWD_CLASS)) {
                        action("class " + prefixNameProtect(usep) + ";\n");
                    }
                }
            }
        }
    }
    void emitModCUse(const AstNodeModule* modp, VUseType useType);
    void emitTextSection(const AstNodeModule* modp, VNType type);

    // CONSTRUCTORS
    EmitCBaseVisitorConst() = default;
    ~EmitCBaseVisitorConst() override = default;
};

#endif  // guard
