// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing expressions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains all 'AstNode' sub-types that represent expressions,
// i.e.: those constructs that represent, or evaluate to [a possible void]
// value. The root of the hierarchy is 'AstNodeExpr'.
//
// Think of expressions in a very general sense as constructs that "name
// things". The "thing" can be considered the value, but can be highly
// structured. For example, an AstConst can name the value '1', which is
// hopefully familiar. On the opposite end of the spectrum of "things" named by
// expressions, consider AstClassOrPackageRef, that can name a collection of
// pairs (specifically the collection of ('member name', 'member thing')
// pairs). Nevertheless, that collection itself can be considered a value. The
// valid composition of expressions then defines the calculus of values in the
// language.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODEEXPR_H_
#define VERILATOR_V3ASTNODEEXPR_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeExpr VL_NOT_FINAL : public AstNode {
    // An expression tree node
protected:
    AstNodeExpr(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeExpr;
    // METHODS
    void dump(std::ostream& str) const override;
    // TODO: The only AstNodeExpr without dtype is AstArg. Otherwise this could be final.
    bool hasDType() const override { return true; }
    virtual string emitVerilog() = 0;  /// Format string for verilog writing; see V3EmitV
    // For documentation on emitC format see EmitCFunc::emitOpName
    virtual string emitC() = 0;
    virtual string emitSimpleOperator() { return ""; }  // "" means not ok to use
    virtual bool emitCheckMaxWords() { return false; }  // Check VL_MULS_MAX_WORDS
    virtual bool cleanOut() const = 0;  // True if output has extra upper bits zero
    // Someday we will generically support data types on every expr node
    // Until then isOpaque indicates we shouldn't constant optimize this node type
    bool isOpaque() const { return VN_IS(this, CvtPackString); }

    // Wrap This expression into an AstStmtExpr to denote it occurs in statement position
    inline AstStmtExpr* makeStmt();
    virtual void clearCachedPurity(){};  // Most nodes don't cache their purity
};
class AstNodeBiop VL_NOT_FINAL : public AstNodeExpr {
    // Binary expression
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    VIsCached m_purity;  // Pure state

protected:
    AstNodeBiop(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : AstNodeExpr{t, fl} {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeBiop;
    // Clone single node, just get same type back.
    virtual AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) = 0;
    // METHODS
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    // Signed flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode*) const override { return true; }
    bool isPure() override;
    const char* broken() const override;
    void clearCachedPurity() override;

private:
    bool getPurityRecurse() const { return lhsp()->isPure() && rhsp()->isPure(); }
};
class AstNodeBiCom VL_NOT_FINAL : public AstNodeBiop {
    // Binary expr with commutative properties
protected:
    AstNodeBiCom(VNType t, FileLine* fl, AstNodeExpr* lhs, AstNodeExpr* rhs)
        : AstNodeBiop{t, fl, lhs, rhs} {}

public:
    ASTGEN_MEMBERS_AstNodeBiCom;
};
class AstNodeBiComAsv VL_NOT_FINAL : public AstNodeBiCom {
    // Binary expr with commutative & associative properties
protected:
    AstNodeBiComAsv(VNType t, FileLine* fl, AstNodeExpr* lhs, AstNodeExpr* rhs)
        : AstNodeBiCom{t, fl, lhs, rhs} {}

public:
    ASTGEN_MEMBERS_AstNodeBiComAsv;
};
class AstNodeDistBiop VL_NOT_FINAL : public AstNodeBiop {
public:
    AstNodeDistBiop(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : AstNodeBiop{t, fl, lhsp, rhsp} {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstNodeDistBiop;
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        V3ERROR_NA;
        return nullptr;
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
};
class AstNodeSel VL_NOT_FINAL : public AstNodeBiop {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // @astgen alias op1 := fromp // Expression we are indexing into
    // @astgen alias op2 := bitp // The index // TODO: rename to idxp
protected:
    AstNodeSel(VNType t, FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : AstNodeBiop{t, fl, fromp, bitp} {}

public:
    ASTGEN_MEMBERS_AstNodeSel;
    int bitConst() const;
};
class AstNodeStream VL_NOT_FINAL : public AstNodeBiop {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
protected:
    AstNodeStream(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : AstNodeBiop{t, fl, lhsp, rhsp} {
        if (lhsp->dtypep()) dtypeSetLogicSized(lhsp->dtypep()->width(), VSigning::UNSIGNED);
    }

public:
    ASTGEN_MEMBERS_AstNodeStream;
};
class AstNodeSystemBiopD VL_NOT_FINAL : public AstNodeBiop {
public:
    AstNodeSystemBiopD(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : AstNodeBiop{t, fl, lhsp, rhsp} {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstNodeSystemBiopD;
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    bool doubleFlavor() const override { return true; }
};
class AstNodeCCall VL_NOT_FINAL : public AstNodeExpr {
    // A call of a C++ function, perhaps a AstCFunc or perhaps globally named
    // @astgen op2 := argsp : List[AstNodeExpr] // Note: op1 used by some sub-types only
    AstCFunc* m_funcp;
    string m_argTypes;

protected:
    AstNodeCCall(VNType t, FileLine* fl, AstCFunc* funcp, AstNodeExpr* argsp = nullptr)
        : AstNodeExpr{t, fl}
        , m_funcp{funcp} {
        addArgsp(argsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeCCall;
    void dump(std::ostream& str = std::cout) const override;
    void cloneRelink() override;
    const char* broken() const override;
    int instrCount() const override { return INSTR_COUNT_CALL; }
    bool same(const AstNode* samep) const override {
        const AstNodeCCall* const asamep = static_cast<const AstNodeCCall*>(samep);
        return (funcp() == asamep->funcp() && argTypes() == asamep->argTypes());
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override;
    bool isOutputter() override { return !isPure(); }
    AstCFunc* funcp() const { return m_funcp; }
    void funcp(AstCFunc* funcp) { m_funcp = funcp; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }

    string emitVerilog() final override { V3ERROR_NA_RETURN(""); }
    string emitC() final override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const final override { return true; }
};
class AstNodeFTaskRef VL_NOT_FINAL : public AstNodeExpr {
    // A reference to a task (or function)
    // @astgen op1 := namep : Optional[AstNode]
    // op2 used by some sub-types only
    // @astgen op3 := pinsp : List[AstNodeExpr]
    // @astgen op4 := scopeNamep : Optional[AstScopeName]
    AstNodeFTask* m_taskp = nullptr;  // [AfterLink] Pointer to task referenced
    AstNodeModule* m_classOrPackagep = nullptr;  // Class/package of the task
    string m_name;  // Name of variable
    string m_dotted;  // Dotted part of scope the name()ed task/func is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
    bool m_pli = false;  // Pli system call ($name)
    VIsCached m_purity;  // Pure state

protected:
    AstNodeFTaskRef(VNType t, FileLine* fl, AstNode* namep, AstNodeExpr* pinsp)
        : AstNodeExpr{t, fl} {
        this->namep(namep);
        this->addPinsp(pinsp);
    }
    AstNodeFTaskRef(VNType t, FileLine* fl, const string& name, AstNodeExpr* pinsp)
        : AstNodeExpr{t, fl}
        , m_name{name} {
        this->addPinsp(pinsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeFTaskRef;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool isGateOptimizable() const override;
    string dotted() const { return m_dotted; }  // * = Scope name or ""
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    AstNodeFTask* taskp() const { return m_taskp; }  // [After Link] Pointer to variable
    void taskp(AstNodeFTask* taskp) { m_taskp = taskp; }
    void name(const string& name) override { m_name = name; }
    void dotted(const string& name) { m_dotted = name; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    bool pli() const { return m_pli; }
    void pli(bool flag) { m_pli = flag; }
    bool isPure() override;

    string emitVerilog() final override { V3ERROR_NA_RETURN(""); }
    string emitC() final override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const final override { V3ERROR_NA_RETURN(true); }
    void clearCachedPurity() override;

private:
    bool getPurityRecurse() const;
};
class AstNodePreSel VL_NOT_FINAL : public AstNodeExpr {
    // Something that becomes an AstSel
    // @astgen op1 := fromp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    // @astgen op3 := thsp : Optional[AstNodeExpr]
    // @astgen op4 := attrp : Optional[AstAttrOf]
    VIsCached m_purity;  // Pure state

protected:
    AstNodePreSel(VNType t, FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : AstNodeExpr{t, fl} {
        this->fromp(fromp);
        this->rhsp(rhsp);
        this->thsp(thsp);
    }

public:
    ASTGEN_MEMBERS_AstNodePreSel;
    // METHODS
    bool same(const AstNode*) const override { return true; }

    string emitVerilog() final override { V3ERROR_NA_RETURN(""); }
    string emitC() final override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const final override { V3ERROR_NA_RETURN(true); }
    bool isPure() override;
    const char* broken() const override;
    void clearCachedPurity() override;

private:
    bool getPurityRecurse() const {
        return fromp()->isPure() && rhsp()->isPure() && (!thsp() || thsp()->isPure());
    }
};
class AstNodeQuadop VL_NOT_FINAL : public AstNodeExpr {
    // 4-ary expression
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    // @astgen op3 := thsp : AstNodeExpr
    // @astgen op4 := fhsp : AstNodeExpr
    VIsCached m_purity;  // Pure state

protected:
    AstNodeQuadop(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp,
                  AstNodeExpr* fhsp)
        : AstNodeExpr{t, fl} {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
        this->thsp(thsp);
        this->fhsp(fhsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeQuadop;
    // METHODS
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths, const V3Number& fhs)
        = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool cleanThs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool cleanFhs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool sizeMattersThs() const = 0;  // True if output result depends on ths size
    virtual bool sizeMattersFhs() const = 0;  // True if output result depends on ths size
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode*) const override { return true; }
    bool isPure() override;
    const char* broken() const override;
    void clearCachedPurity() override;

private:
    bool getPurityRecurse() const {
        return lhsp()->isPure() && rhsp()->isPure() && thsp()->isPure() && fhsp()->isPure();
    }
};
class AstNodeTermop VL_NOT_FINAL : public AstNodeExpr {
    // Terminal operator -- an operator with no "inputs"
protected:
    AstNodeTermop(VNType t, FileLine* fl)
        : AstNodeExpr{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeTermop;
    // Know no children, and hot function, so skip iterator for speed
    // cppcheck-suppress functionConst
    void iterateChildren(VNVisitorConst& v) {}
    void dump(std::ostream& str) const override;
};
class AstNodeTriop VL_NOT_FINAL : public AstNodeExpr {
    // Ternary expression
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    // @astgen op3 := thsp : AstNodeExpr
    VIsCached m_purity;  // Pure state

protected:
    AstNodeTriop(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : AstNodeExpr{t, fl} {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
        this->thsp(thsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeTriop;
    // METHODS
    void dump(std::ostream& str) const override;
    // Set out to evaluation of a AstConst'ed
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths)
        = 0;
    virtual bool cleanLhs() const = 0;  // True if LHS must have extra upper bits zero
    virtual bool cleanRhs() const = 0;  // True if RHS must have extra upper bits zero
    virtual bool cleanThs() const = 0;  // True if THS must have extra upper bits zero
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool sizeMattersRhs() const = 0;  // True if output result depends on rhs size
    virtual bool sizeMattersThs() const = 0;  // True if output result depends on ths size
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode*) const override { return true; }
    bool isPure() override;
    const char* broken() const override;
    void clearCachedPurity() override;

private:
    bool getPurityRecurse() const {
        return lhsp()->isPure() && rhsp()->isPure() && thsp()->isPure();
    }
};
class AstNodeCond VL_NOT_FINAL : public AstNodeTriop {
    // @astgen alias op1 := condp
    // @astgen alias op2 := thenp
    // @astgen alias op3 := elsep
protected:
    AstNodeCond(VNType t, FileLine* fl, AstNodeExpr* condp, AstNodeExpr* thenp,
                AstNodeExpr* elsep);

public:
    ASTGEN_MEMBERS_AstNodeCond;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override;
    string emitVerilog() override { return "%k(%l %f? %r %k: %t)"; }
    string emitC() override { return "VL_COND_%nq%lq%rq%tq(%nw, %P, %li, %ri, %ti)"; }
    bool cleanOut() const override { return false; }  // clean if e1 & e2 clean
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }  // Propagates up
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual AstNodeExpr* cloneType(AstNodeExpr* condp, AstNodeExpr* thenp, AstNodeExpr* elsep) = 0;
};
class AstNodeDistTriop VL_NOT_FINAL : public AstNodeTriop {
public:
    AstNodeDistTriop(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
                     AstNodeExpr* thsp)
        : AstNodeTriop{t, fl, lhsp, rhsp, thsp} {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstNodeDistTriop;
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        V3ERROR_NA;
    }
};
class AstNodeUniop VL_NOT_FINAL : public AstNodeExpr {
    // Unary expression
    // @astgen op1 := lhsp : AstNodeExpr
    VIsCached m_purity;  // Pure state

protected:
    AstNodeUniop(VNType t, FileLine* fl, AstNodeExpr* lhsp)
        : AstNodeExpr{t, fl} {
        dtypeFrom(lhsp);
        this->lhsp(lhsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeUniop;
    // METHODS
    void dump(std::ostream& str) const override;
    // Set out to evaluation of a AstConst'ed lhs
    virtual void numberOperate(V3Number& out, const V3Number& lhs) = 0;
    virtual bool cleanLhs() const = 0;
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    // Signed flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode*) const override { return true; }
    bool isPure() override;
    const char* broken() const override;
    void clearCachedPurity() override;
};
class AstNodeSystemUniopD VL_NOT_FINAL : public AstNodeUniop {
public:
    AstNodeSystemUniopD(VNType t, FileLine* fl, AstNodeExpr* lhsp)
        : AstNodeUniop{t, fl, lhsp} {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstNodeSystemUniopD;
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    bool doubleFlavor() const override { return true; }
};
class AstNodeVarRef VL_NOT_FINAL : public AstNodeExpr {
    // An AstVarRef or AstVarXRef
    VAccess m_access;  // Left hand side assignment
    AstVar* m_varp;  // [AfterLink] Pointer to variable itself
    AstVarScope* m_varScopep = nullptr;  // Varscope for hierarchy
    AstNodeModule* m_classOrPackagep = nullptr;  // Class/package of the variable
    VSelfPointerText m_selfPointer
        = VSelfPointerText{VSelfPointerText::Empty()};  // Output code object
                                                        // pointer (e.g.: 'this')
protected:
    AstNodeVarRef(VNType t, FileLine* fl, const VAccess& access)
        : AstNodeExpr{t, fl}
        , m_access{access} {
        varp(nullptr);
    }
    AstNodeVarRef(VNType t, FileLine* fl, AstVar* varp, const VAccess& access)
        : AstNodeExpr{t, fl}
        , m_access{access} {
        // May have varp==nullptr
        this->varp(varp);
    }

public:
    ASTGEN_MEMBERS_AstNodeVarRef;
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    int instrCount() const override { return widthInstrs(); }
    void cloneRelink() override;
    VAccess access() const { return m_access; }
    void access(const VAccess& flag) { m_access = flag; }  // Avoid using this; Set in constructor
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) {
        m_varp = varp;
        dtypeFrom((AstNode*)varp);
    }
    AstVarScope* varScopep() const { return m_varScopep; }
    void varScopep(AstVarScope* varscp) { m_varScopep = varscp; }
    const VSelfPointerText& selfPointer() const { return m_selfPointer; }
    void selfPointer(const VSelfPointerText& selfPointer) { m_selfPointer = selfPointer; }
    string selfPointerProtect(bool useSelfForThis) const {
        return selfPointer().protect(useSelfForThis, protect());
    }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    // Know no children, and hot function, so skip iterator for speed
    // cppcheck-suppress functionConst
    void iterateChildren(VNVisitorConst& v) {}
};

// === Concrete node types =====================================================

// === AstNodeExpr ===
class AstAddrOfCFunc final : public AstNodeExpr {
    // Get address of CFunc
    AstCFunc* m_funcp;  // Pointer to function itself

public:
    AstAddrOfCFunc(FileLine* fl, AstCFunc* funcp)
        : ASTGEN_SUPER_AddrOfCFunc(fl)
        , m_funcp{funcp} {
        dtypep(findCHandleDType());
    }

public:
    ASTGEN_MEMBERS_AstAddrOfCFunc;
    void cloneRelink() override;
    const char* broken() const override;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    AstCFunc* funcp() const { return m_funcp; }
};
class AstArg final : public AstNodeExpr {
    // An argument to a function/task, which is either an expression, or is a placeholder for an
    // omitted argument.
    // TODO: AstArg should not be AstNodeExpr, but is currently used as such widely. Fix later.
    // @astgen op1 := exprp : Optional[AstNodeExpr] // nullptr if omitted
    string m_name;  // Pin name, or "" for number based interconnect
public:
    AstArg(FileLine* fl, const string& name, AstNodeExpr* exprp)
        : ASTGEN_SUPER_Arg(fl)
        , m_name{name} {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstArg;
    bool hasDType() const override { return false; }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Pin name, ""=go by number
    void name(const string& name) override { m_name = name; }
    bool emptyConnectNoNext() const { return !exprp() && name() == "" && !nextp(); }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstAttrOf final : public AstNodeExpr {
    // Return a value of a attribute, for example a LSB or array LSB of a signal
    // @astgen op1 := fromp : Optional[AstNode] // Expr or DType
    // @astgen op2 := dimp : Optional[AstNodeExpr]
    VAttrType m_attrType;  // What sort of extraction
public:
    AstAttrOf(FileLine* fl, VAttrType attrtype, AstNode* fromp = nullptr,
              AstNodeExpr* dimp = nullptr)
        : ASTGEN_SUPER_AttrOf(fl) {
        this->fromp(fromp);
        this->dimp(dimp);
        m_attrType = attrtype;
    }
    ASTGEN_MEMBERS_AstAttrOf;
    VAttrType attrType() const { return m_attrType; }
    void dump(std::ostream& str = std::cout) const override;

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstCExpr final : public AstNodeExpr {
    // @astgen op1 := exprsp : List[AstNode] // Expressions to print
    const bool m_cleanOut;
    bool m_pure;  // Pure optimizable
public:
    // Emit C textual expr function (like AstUCFunc)
    AstCExpr(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_CExpr(fl)
        , m_cleanOut{true}
        , m_pure{false} {
        addExprsp(exprsp);
        dtypeFrom(exprsp);
    }
    inline AstCExpr(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut = true);
    ASTGEN_MEMBERS_AstCExpr;
    bool isGateOptimizable() const override { return m_pure; }
    bool isPredictOptimizable() const override { return m_pure; }
    bool cleanOut() const override { return m_cleanOut; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool pure() const { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
};
class AstCMethodHard final : public AstNodeExpr {
    // A reference to a "C" hardcoded member task (or function)
    // PARENTS: stmt/expr
    // @astgen op1 := fromp : AstNodeExpr // Subject of method call
    // @astgen op2 := pinsp : List[AstNodeExpr] // Arguments
    string m_name;  // Name of method
    bool m_pure = false;  // Pure optimizable
public:
    AstCMethodHard(FileLine* fl, AstNodeExpr* fromp, const string& name,
                   AstNodeExpr* pinsp = nullptr)
        : ASTGEN_SUPER_CMethodHard(fl)
        , m_name{name} {
        this->fromp(fromp);
        this->addPinsp(pinsp);
        setPurity();
    }
    ASTGEN_MEMBERS_AstCMethodHard;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    void name(const string& name) override { m_name = name; }
    bool same(const AstNode* samep) const override {
        const AstCMethodHard* asamep = static_cast<const AstCMethodHard*>(samep);
        return (m_name == asamep->m_name);
    }
    bool isPure() override { return m_pure; }
    int instrCount() const override;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }

private:
    void setPurity();
};
class AstCast final : public AstNodeExpr {
    // Cast to appropriate data type
    // @astgen op1 := fromp : AstNodeExpr
    // @astgen op2 := childDTypep : Optional[AstNodeDType]
public:
    AstCast(FileLine* fl, AstNodeExpr* fromp, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_Cast(fl) {
        this->fromp(fromp);
        this->childDTypep(dtp);
        dtypeFrom(dtp);
    }
    AstCast(FileLine* fl, AstNodeExpr* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER_Cast(fl) {
        this->fromp(fromp);
        dtypeFrom(dtp);
    }
    ASTGEN_MEMBERS_AstCast;
    string emitVerilog() override { return "((%d)'(%l))"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const VL_MT_STABLE { return dtypep() ? dtypep() : childDTypep(); }
};
class AstCastParse final : public AstNodeExpr {
    // Cast to appropriate type, where we haven't determined yet what the data type is
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := dtp : AstNode
public:
    AstCastParse(FileLine* fl, AstNodeExpr* lhsp, AstNode* dtp)
        : ASTGEN_SUPER_CastParse(fl) {
        this->lhsp(lhsp);
        this->dtp(dtp);
    }
    ASTGEN_MEMBERS_AstCastParse;
    string emitVerilog() override { return "((%d)'(%l))"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstCastSize final : public AstNodeExpr {
    // Cast to specific size; signed/twostate inherited from lower element per IEEE
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstConst
public:
    AstCastSize(FileLine* fl, AstNodeExpr* lhsp, AstConst* rhsp)
        : ASTGEN_SUPER_CastSize(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstCastSize;
    // No hasDType because widthing removes this node before the hasDType check
    string emitVerilog() override { return "((%r)'(%l))"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstCellArrayRef final : public AstNodeExpr {
    // As-of-yet unlinkable reference into an array of cells
    // @astgen op1 := selp : List[AstNodeExpr] // Select expression
    string m_name;  // Array name
public:
    AstCellArrayRef(FileLine* fl, const string& name, AstNodeExpr* selp)
        : ASTGEN_SUPER_CellArrayRef(fl)
        , m_name{name} {
        this->addSelp(selp);
    }
    ASTGEN_MEMBERS_AstCellArrayRef;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Array name

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstCellRef final : public AstNodeExpr {
    // As-of-yet unlinkable reference into a cell
    // @astgen op1 := cellp : AstNode
    // @astgen op2 := exprp : AstNodeExpr
private:
    string m_name;  // Cell name
public:
    AstCellRef(FileLine* fl, const string& name, AstNode* cellp, AstNodeExpr* exprp)
        : ASTGEN_SUPER_CellRef(fl)
        , m_name{name} {
        this->cellp(cellp);
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstCellRef;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Array name

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstClassOrPackageRef final : public AstNodeExpr {
    // @astgen op1 := paramsp : List[AstPin]
private:
    string m_name;
    // Node not NodeModule to appease some early parser usage
    AstNode* m_classOrPackageNodep;  // Pointer to class/package referenced
public:
    AstClassOrPackageRef(FileLine* fl, const string& name, AstNode* classOrPackageNodep,
                         AstPin* paramsp)
        : ASTGEN_SUPER_ClassOrPackageRef(fl)
        , m_name{name}
        , m_classOrPackageNodep{classOrPackageNodep} {
        this->addParamsp(paramsp);
    }
    ASTGEN_MEMBERS_AstClassOrPackageRef;
    // METHODS
    const char* broken() const override {
        BROKEN_RTN(m_classOrPackageNodep && !m_classOrPackageNodep->brokeExists());
        return nullptr;
    }
    void cloneRelink() override {
        if (m_classOrPackageNodep && m_classOrPackageNodep->clonep()) {
            m_classOrPackageNodep = m_classOrPackageNodep->clonep();
        }
    }
    bool same(const AstNode* samep) const override {
        return (m_classOrPackageNodep
                == static_cast<const AstClassOrPackageRef*>(samep)->m_classOrPackageNodep);
    }
    void dump(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    AstNode* classOrPackageNodep() const { return m_classOrPackageNodep; }
    void classOrPackageNodep(AstNode* nodep) { m_classOrPackageNodep = nodep; }
    AstNodeModule* classOrPackagep() const;
    AstPackage* packagep() const { return VN_CAST(classOrPackageNodep(), Package); }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackageNodep = (AstNode*)nodep; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstConsAssoc final : public AstNodeExpr {
    // Construct an assoc array and return object, '{}
    // @astgen op1 := defaultp : Optional[AstNode]
public:
    AstConsAssoc(FileLine* fl, AstNode* defaultp)
        : ASTGEN_SUPER_ConsAssoc(fl) {
        this->defaultp(defaultp);
    }
    ASTGEN_MEMBERS_AstConsAssoc;
    string emitVerilog() override { return "'{}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsDynArray final : public AstNodeExpr {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // @astgen op1 := lhsp : Optional[AstNode]
    // @astgen op2 := rhsp : Optional[AstNode]
public:
    explicit AstConsDynArray(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER_ConsDynArray(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstConsDynArray;
    string emitVerilog() override { return "'{%l, %r}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsPackMember final : public AstNodeExpr {
    // Construct a packed array single emement [member1: value1]
    // Don't need the member we are constructing, as the dtypep can get us to it
    // @astgen op2 := rhsp : AstNodeExpr
public:
    explicit AstConsPackMember(FileLine* fl, AstMemberDType* dtypep, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_ConsPackMember(fl) {
        this->dtypep(dtypep);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstConsPackMember;
    const char* broken() const override {
        BROKEN_RTN(dtypep() && !VN_IS(dtypep(), MemberDType));
        return nullptr;
    }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsPackUOrStruct final : public AstNodeExpr {
    // Construct a packed struct and return object, '{member1: value1, member2: value2}
    // Don't need the class we are constructing, as the dtypep can get us to it
    // @astgen op1 := membersp : List[AstConsPackMember]
public:
    explicit AstConsPackUOrStruct(FileLine* fl, AstNodeUOrStructDType* dtypep,
                                  AstConsPackMember* membersp = nullptr)
        : ASTGEN_SUPER_ConsPackUOrStruct(fl) {
        this->dtypep(dtypep);
        this->addMembersp(membersp);
    }
    ASTGEN_MEMBERS_AstConsPackUOrStruct;
    const char* broken() const override {
        BROKEN_RTN(dtypep() && !VN_IS(dtypep(), NodeUOrStructDType));
        return nullptr;
    }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsQueue final : public AstNodeExpr {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // @astgen op1 := lhsp : Optional[AstNode]
    // @astgen op2 := rhsp : Optional[AstNode]
public:
    explicit AstConsQueue(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER_ConsQueue(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstConsQueue;
    string emitVerilog() override { return "'{%l, %r}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsWildcard final : public AstNodeExpr {
    // Construct a wildcard assoc array and return object, '{}
    // @astgen op1 := defaultp : Optional[AstNode]
public:
    AstConsWildcard(FileLine* fl, AstNode* defaultp)
        : ASTGEN_SUPER_ConsWildcard(fl) {
        this->defaultp(defaultp);
    }
    ASTGEN_MEMBERS_AstConsWildcard;
    string emitVerilog() override { return "'{}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConst final : public AstNodeExpr {
    // A constant
    V3Number m_num;  // Constant value
    void initWithNumber() {
        if (m_num.isDouble()) {
            dtypeSetDouble();
        } else if (m_num.isString()) {
            dtypeSetString();
        } else {
            dtypeSetLogicUnsized(m_num.width(), (m_num.sized() ? 0 : m_num.widthMin()),
                                 VSigning::fromBool(m_num.isSigned()));
        }
        m_num.nodep(this);
    }

public:
    AstConst(FileLine* fl, const V3Number& num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(num) {
        initWithNumber();
    }
    class WidthedValue {};  // for creator type-overload selection
    AstConst(FileLine* fl, WidthedValue, int width, uint32_t value)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, width, value) {
        initWithNumber();
    }
    class DTyped {};  // for creator type-overload selection
    // Zero/empty constant with a type matching nodetypep
    AstConst(FileLine* fl, DTyped, const AstNodeDType* nodedtypep)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, nodedtypep) {
        initWithNumber();
    }
    class StringToParse {};  // for creator type-overload selection
    AstConst(FileLine* fl, StringToParse, const char* sourcep)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, sourcep) {
        initWithNumber();
    }
    class VerilogStringLiteral {};  // for creator type-overload selection
    AstConst(FileLine* fl, VerilogStringLiteral, const string& str)
        : ASTGEN_SUPER_Const(fl)
        , m_num(V3Number::VerilogStringLiteral{}, this, str) {
        initWithNumber();
    }
    AstConst(FileLine* fl, uint32_t num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 32, num) {
        dtypeSetLogicUnsized(m_num.width(), 0, VSigning::UNSIGNED);
    }
    class Unsized32 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Unsized32, uint32_t num)  // Unsized 32-bit integer of specified value
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 32, num) {
        m_num.width(32, false);
        dtypeSetLogicUnsized(32, m_num.widthMin(), VSigning::UNSIGNED);
    }
    class Signed32 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Signed32, int32_t num)  // Signed 32-bit integer of specified value
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 32, num) {
        m_num.width(32, true);
        dtypeSetLogicUnsized(32, m_num.widthMin(), VSigning::SIGNED);
    }
    class Unsized64 {};  // for creator type-overload selection
    AstConst(FileLine* fl, Unsized64, uint64_t num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 64, 0) {
        m_num.setQuad(num);
        dtypeSetLogicSized(64, VSigning::UNSIGNED);
    }
    class SizedEData {};  // for creator type-overload selection
    AstConst(FileLine* fl, SizedEData, uint64_t num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, VL_EDATASIZE, 0) {
        m_num.setQuad(num);
        dtypeSetLogicSized(VL_EDATASIZE, VSigning::UNSIGNED);
    }
    class RealDouble {};  // for creator type-overload selection
    AstConst(FileLine* fl, RealDouble, double num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 64) {
        m_num.setDouble(num);
        dtypeSetDouble();
    }
    class String {};  // for creator type-overload selection
    AstConst(FileLine* fl, String, const string& num)
        : ASTGEN_SUPER_Const(fl)
        , m_num(V3Number::String{}, this, num) {
        dtypeSetString();
    }
    class BitFalse {};
    AstConst(FileLine* fl, BitFalse)  // Shorthand const 0, dtype should be a logic of size 1
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 1, 0) {
        dtypeSetBit();
    }
    // Shorthand const 1 (or with argument 0/1), dtype should be a logic of size 1
    class BitTrue {};
    AstConst(FileLine* fl, BitTrue, bool on = true)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, 1, on) {
        dtypeSetBit();
    }
    class All0 {};
    AstConst(FileLine* fl, All0)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, "'0") {
        initWithNumber();
        fl->warnOff(V3ErrorCode::NEWERSTD, true);
    }
    class All1 {};
    AstConst(FileLine* fl, All1)
        : ASTGEN_SUPER_Const(fl)
        , m_num(this, "'1") {
        initWithNumber();
        fl->warnOff(V3ErrorCode::NEWERSTD, true);
    }
    class Null {};
    AstConst(FileLine* fl, Null)
        : ASTGEN_SUPER_Const(fl)
        , m_num(V3Number::Null{}, this) {
        dtypeSetBit();  // Events 1 bit, objects 64 bits, so autoExtend=1 and use bit here
        initWithNumber();
    }
    class OneStep {};
    AstConst(FileLine* fl, OneStep)
        : ASTGEN_SUPER_Const(fl)
        , m_num(V3Number::OneStep{}, this) {
        dtypeSetLogicSized(64, VSigning::UNSIGNED);
        initWithNumber();
    }
    ASTGEN_MEMBERS_AstConst;
    string name() const override VL_MT_STABLE { return num().ascii(); }  // * = Value
    const V3Number& num() const VL_MT_SAFE { return m_num; }  // * = Value
    V3Number& num() { return m_num; }  // * = Value
    uint32_t toUInt() const { return num().toUInt(); }
    int32_t toSInt() const VL_MT_SAFE { return num().toSInt(); }
    uint64_t toUQuad() const { return num().toUQuad(); }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* samep) const override {
        const AstConst* const sp = static_cast<const AstConst*>(samep);
        return num().isCaseEq(sp->num());
    }
    void cloneRelink() override { m_num.nodep(this); }
    const char* broken() const override {
        BROKEN_RTN(m_num.nodep() && m_num.nodep() != this);
        return nullptr;
    }
    int instrCount() const override { return widthInstrs(); }
    bool isEqAllOnes() const { return num().isEqAllOnes(width()); }
    bool isEqAllOnesV() const { return num().isEqAllOnes(widthMinV()); }
    // Parse string and create appropriate type of AstConst.
    // May return nullptr on parse failure.
    static AstConst* parseParamLiteral(FileLine* fl, const string& literal);
};
class AstCvtDynArrayToPacked final : public AstNodeExpr {
    // Cast from dynamic queue data type to packed array
    // @astgen op1 := fromp : AstNodeExpr
public:
    AstCvtDynArrayToPacked(FileLine* fl, AstNodeExpr* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER_CvtDynArrayToPacked(fl) {
        this->fromp(fromp);
        dtypeFrom(dtp);
    }
    ASTGEN_MEMBERS_AstCvtDynArrayToPacked;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstCvtPackedToDynArray final : public AstNodeExpr {
    // Cast from packed array to dynamic queue data type
    // @astgen op1 := fromp : AstNodeExpr
public:
    AstCvtPackedToDynArray(FileLine* fl, AstNodeExpr* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER_CvtPackedToDynArray(fl) {
        this->fromp(fromp);
        dtypeFrom(dtp);
    }
    ASTGEN_MEMBERS_AstCvtPackedToDynArray;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstDot final : public AstNodeExpr {
    // A dot separating paths in an AstVarXRef, AstFuncRef or AstTaskRef
    // These are eliminated in the link stage
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    const bool m_colon;  // Is a "::" instead of a "." (lhs must be package/class)
public:
    AstDot(FileLine* fl, bool colon, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Dot(fl)
        , m_colon{colon} {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstDot;
    // For parser, make only if non-null package
    static AstNodeExpr* newIfPkg(FileLine* fl, AstNodeExpr* packageOrClassp, AstNodeExpr* rhsp) {
        if (!packageOrClassp) return rhsp;
        return new AstDot{fl, true, packageOrClassp, rhsp};
    }
    void dump(std::ostream& str) const override;
    bool colon() const { return m_colon; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstEmptyQueue final : public AstNodeExpr {
public:
    explicit AstEmptyQueue(FileLine* fl)
        : ASTGEN_SUPER_EmptyQueue(fl) {}
    ASTGEN_MEMBERS_AstEmptyQueue;
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitVerilog() override { return "{}"; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool cleanOut() const override { return true; }
};
class AstEnumItemRef final : public AstNodeExpr {
    AstEnumItem* m_itemp;  // [AfterLink] Pointer to item
    AstNodeModule* m_classOrPackagep;  // Class/package in which it was defined
public:
    AstEnumItemRef(FileLine* fl, AstEnumItem* itemp, AstNodeModule* classOrPackagep)
        : ASTGEN_SUPER_EnumItemRef(fl)
        , m_itemp{itemp}
        , m_classOrPackagep{classOrPackagep} {
        dtypeFrom(m_itemp);
    }
    ASTGEN_MEMBERS_AstEnumItemRef;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return itemp()->name(); }
    int instrCount() const override { return 0; }
    const char* broken() const override;
    void cloneRelink() override {
        if (m_itemp->clonep()) m_itemp = m_itemp->clonep();
    }
    bool same(const AstNode* samep) const override {
        const AstEnumItemRef* const sp = static_cast<const AstEnumItemRef*>(samep);
        return itemp() == sp->itemp();
    }
    AstEnumItem* itemp() const VL_MT_STABLE { return m_itemp; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
};
class AstExprStmt final : public AstNodeExpr {
    // Perform a statement, often assignment inside an expression node,
    // the parent gets passed the 'resultp()'.
    // resultp is evaluated AFTER the statement(s).
    // @astgen op1 := stmtsp : List[AstNode]
    // @astgen op2 := resultp : AstNodeExpr
public:
    AstExprStmt(FileLine* fl, AstNode* stmtsp, AstNodeExpr* resultp)
        : ASTGEN_SUPER_ExprStmt(fl) {
        addStmtsp(stmtsp);
        this->resultp(resultp);
        dtypeFrom(resultp);
    }
    ASTGEN_MEMBERS_AstExprStmt;
    // METHODS
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool isPure() override {
        if (AstNode::afterCommentp(stmtsp())) return false;
        return resultp()->isPure();
    }
    bool same(const AstNode*) const override { return true; }
};
class AstFError final : public AstNodeExpr {
    // @astgen op1 := filep : AstNode
    // @astgen op2 := strp : AstNode
public:
    AstFError(FileLine* fl, AstNode* filep, AstNode* strp)
        : ASTGEN_SUPER_FError(fl) {
        this->filep(filep);
        this->strp(strp);
    }
    ASTGEN_MEMBERS_AstFError;
    string emitVerilog() override { return "%f$ferror(%l, %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs() * 64; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFOpen final : public AstNodeExpr {
    // @astgen op2 := filenamep : AstNodeExpr
    // @astgen op3 := modep : AstNodeExpr
public:
    AstFOpen(FileLine* fl, AstNodeExpr* filenamep, AstNodeExpr* modep)
        : ASTGEN_SUPER_FOpen(fl) {
        this->filenamep(filenamep);
        this->modep(modep);
    }
    ASTGEN_MEMBERS_AstFOpen;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    string verilogKwd() const override { return "$fopen"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFOpenMcd final : public AstNodeExpr {
    // @astgen op2 := filenamep : AstNodeExpr
public:
    AstFOpenMcd(FileLine* fl, AstNodeExpr* filenamep)
        : ASTGEN_SUPER_FOpenMcd(fl) {
        this->filenamep(filenamep);
    }
    ASTGEN_MEMBERS_AstFOpenMcd;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    string verilogKwd() const override { return "$fopen"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFRead final : public AstNodeExpr {
    // @astgen op1 := memp : AstNode // VarRef for result
    // @astgen op2 := filep : AstNode // file (must be a VarRef)
    // @astgen op3 := startp : Optional[AstNode] // Offset
    // @astgen op4 := countp : Optional[AstNode] // Size
public:
    AstFRead(FileLine* fl, AstNode* memp, AstNode* filep, AstNode* startp, AstNode* countp)
        : ASTGEN_SUPER_FRead(fl) {
        this->memp(memp);
        this->filep(filep);
        this->startp(startp);
        this->countp(countp);
    }
    ASTGEN_MEMBERS_AstFRead;
    string verilogKwd() const override { return "$fread"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: makes output
    bool cleanOut() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFRewind final : public AstNodeExpr {
    // @astgen op1 := filep : Optional[AstNode]
public:
    AstFRewind(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FRewind(fl) {
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstFRewind;
    string verilogKwd() const override { return "$frewind"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool cleanOut() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFScanF final : public AstNodeExpr {
    // @astgen op1 := exprsp : List[AstNode] // VarRefs for results
    // @astgen op2 := filep : Optional[AstNode] // file (must be a VarRef)
    string m_text;

public:
    AstFScanF(FileLine* fl, const string& text, AstNode* filep, AstNode* exprsp)
        : ASTGEN_SUPER_FScanF(fl)
        , m_text{text} {
        addExprsp(exprsp);
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstFScanF;
    string name() const override VL_MT_STABLE { return m_text; }
    string verilogKwd() const override { return "$fscanf"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: makes output
    bool cleanOut() const override { return false; }
    bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstFScanF*>(samep)->text();
    }
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
};
class AstFSeek final : public AstNodeExpr {
    // @astgen op1 := filep : AstNode // file (must be a VarRef)
    // @astgen op2 := offset : Optional[AstNode]
    // @astgen op3 := operation : Optional[AstNode]
public:
    AstFSeek(FileLine* fl, AstNode* filep, AstNode* offset, AstNode* operation)
        : ASTGEN_SUPER_FSeek(fl) {
        this->filep(filep);
        this->offset(offset);
        this->operation(operation);
    }
    ASTGEN_MEMBERS_AstFSeek;
    string verilogKwd() const override { return "$fseek"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: makes output
    bool cleanOut() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFTell final : public AstNodeExpr {
    // @astgen op1 := filep : AstNode // file (must be a VarRef)
public:
    AstFTell(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FTell(fl) {
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstFTell;
    string verilogKwd() const override { return "$ftell"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool cleanOut() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFell final : public AstNodeExpr {
    // Verilog $fell
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := sentreep : Optional[AstSenTree]
public:
    AstFell(FileLine* fl, AstNodeExpr* exprp, AstSenTree* sentreep)
        : ASTGEN_SUPER_Fell(fl) {
        this->exprp(exprp);
        this->sentreep(sentreep);
    }
    ASTGEN_MEMBERS_AstFell;
    string emitVerilog() override { return "$fell(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstGatePin final : public AstNodeExpr {
    // Possibly expand a gate primitive input pin value to match the range of the gate primitive
    // @astgen op1 := exprp : AstNodeExpr // Pin expression
    // @astgen op2 := rangep : AstRange // Range of pin
public:
    AstGatePin(FileLine* fl, AstNodeExpr* exprp, AstRange* rangep)
        : ASTGEN_SUPER_GatePin(fl) {
        this->exprp(exprp);
        this->rangep(rangep);
    }
    ASTGEN_MEMBERS_AstGatePin;
    string emitVerilog() override { return "%l"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstImplication final : public AstNodeExpr {
    // Verilog Implication Operator
    // Nonoverlapping "|=>"
    // Overlapping "|->" (doesn't currently use this - might make new Ast type)
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
    // @astgen op3 := sentreep : Optional[AstSenTree]
public:
    AstImplication(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Implication(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstImplication;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstInitArray final : public AstNodeExpr {
    // This is also used as an array value in V3Simulate/const prop.
    // Would be better called as 'AstConstArray'
    // Set a var to a map of values
    // The list of initsp() is not relevant
    // If default is specified, the vector may be sparse, and not provide each value.
    // Key values are C++ array style, with lo() at index 0
    // Parents: ASTVAR::init()
    // @astgen op1 := defaultp : Optional[AstNodeExpr] // Default, if sparse
    // @astgen op2 := initsp : List[AstNode] // Initial value expressions
    //
public:
    using KeyItemMap = std::map<uint64_t, AstInitItem*>;

private:
    KeyItemMap m_map;  // Node value for each array index
public:
    AstInitArray(FileLine* fl, AstNodeDType* newDTypep, AstNodeExpr* defaultp)
        : ASTGEN_SUPER_InitArray(fl) {
        dtypep(newDTypep);
        this->defaultp(defaultp);
    }
    ASTGEN_MEMBERS_AstInitArray;
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    void cloneRelink() override;
    bool same(const AstNode* samep) const override {
        // Only works if exact same children, instead should override comparison
        // of children list, and instead use map-vs-map key/value compare
        return m_map == static_cast<const AstInitArray*>(samep)->m_map;
    }
    void addValuep(AstNodeExpr* newp) { addIndexValuep(m_map.size(), newp); }
    const KeyItemMap& map() const { return m_map; }
    void addIndexValuep(uint64_t index, AstNodeExpr* newp);
    AstNodeExpr* getIndexValuep(uint64_t index) const;
    AstNodeExpr* getIndexDefaultedValuep(uint64_t index) const;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstInside final : public AstNodeExpr {
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := itemsp : List[AstNodeExpr]
public:
    AstInside(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* itemsp)
        : ASTGEN_SUPER_Inside(fl) {
        this->exprp(exprp);
        this->addItemsp(itemsp);
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstInside;
    string emitVerilog() override { return "%l inside { %r }"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }  // NA
};
class AstInsideRange final : public AstNodeExpr {
    // @astgen op1 := lhsp : AstNodeExpr
    // @astgen op2 := rhsp : AstNodeExpr
public:
    AstInsideRange(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_InsideRange(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstInsideRange;
    string emitVerilog() override { return "[%l:%r]"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }  // NA
    // Create AstAnd(AstGte(...), AstLte(...))
    AstNodeExpr* newAndFromInside(AstNodeExpr* exprp, AstNodeExpr* lhsp, AstNodeExpr* rhsp);
};
class AstLambdaArgRef final : public AstNodeExpr {
    // Lambda argument usage
    // These are not AstVarRefs because we need to be able to delete/clone lambdas during
    // optimizations and AstVar's are painful to remove.
    string m_name;  // Name of variable
    bool m_index;  // Index, not value

public:
    AstLambdaArgRef(FileLine* fl, const string& name, bool index)
        : ASTGEN_SUPER_LambdaArgRef(fl)
        , m_name{name}
        , m_index(index) {}
    ASTGEN_MEMBERS_AstLambdaArgRef;
    bool same(const AstNode* /*samep*/) const override { return true; }
    string emitVerilog() override { return name(); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    void name(const string& name) override { m_name = name; }
    bool index() const { return m_index; }
};
class AstMemberSel final : public AstNodeExpr {
    // @astgen op1 := fromp : AstNodeExpr
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    string m_name;
    VAccess m_access;  // Read or write, as in AstNodeVarRef
    AstVar* m_varp = nullptr;  // Post link, variable within class that is target of selection
public:
    AstMemberSel(FileLine* fl, AstNodeExpr* fromp, VFlagChildDType, const string& name)
        : ASTGEN_SUPER_MemberSel(fl)
        , m_name{name} {
        this->fromp(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMemberSel(FileLine* fl, AstNodeExpr* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER_MemberSel(fl)
        , m_name{dtp->name()} {
        this->fromp(fromp);
        dtypep(dtp);
    }
    ASTGEN_MEMBERS_AstMemberSel;
    void cloneRelink() override;
    const char* broken() const override;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    void name(const string& name) override { m_name = name; }
    VAccess access() const { return m_access; }
    void access(const VAccess& flag) { m_access = flag; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* samep) const override;
    int instrCount() const override { return widthInstrs(); }
    AstVar* varp() const { return m_varp; }
    void varp(AstVar* nodep) { m_varp = nodep; }
};
class AstNewCopy final : public AstNodeExpr {
    // New as shallow copy
    // @astgen op1 := rhsp : AstNodeExpr
public:
    AstNewCopy(FileLine* fl, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NewCopy(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstNewCopy;
    string emitVerilog() override { return "new"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
};
class AstNewDynamic final : public AstNodeExpr {
    // New for dynamic array
    // @astgen op1 := sizep : AstNodeExpr
    // @astgen op2 := rhsp : Optional[AstNodeExpr]
public:
    AstNewDynamic(FileLine* fl, AstNodeExpr* sizep, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NewDynamic(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        this->sizep(sizep);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstNewDynamic;
    string emitVerilog() override { return "new"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
};
class AstParseRef final : public AstNodeExpr {
    // A reference to a variable, function or task
    // We don't know which at parse time due to bison constraints
    // The link stages will replace this with AstVarRef, or AstTaskRef, etc.
    // @astgen op1 := lhsp : Optional[AstNode]
    // @astgen op2 := ftaskrefp : Optional[AstNodeFTaskRef]

    VParseRefExp m_expect;  // Type we think it should resolve to
    string m_name;

public:
    AstParseRef(FileLine* fl, VParseRefExp expect, const string& name, AstNode* lhsp = nullptr,
                AstNodeFTaskRef* ftaskrefp = nullptr)
        : ASTGEN_SUPER_ParseRef(fl)
        , m_expect{expect}
        , m_name{name} {
        this->lhsp(lhsp);
        this->ftaskrefp(ftaskrefp);
    }
    ASTGEN_MEMBERS_AstParseRef;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool same(const AstNode* samep) const override {
        const AstParseRef* const asamep = static_cast<const AstParseRef*>(samep);
        return (expect() == asamep->expect() && m_name == asamep->m_name);
    }
    void name(const string& name) override { m_name = name; }
    VParseRefExp expect() const { return m_expect; }
    void expect(VParseRefExp exp) { m_expect = exp; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstPast final : public AstNodeExpr {
    // Verilog $past
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := ticksp : Optional[AstNode]
    // @astgen op3 := sentreep : Optional[AstSenTree]
public:
    AstPast(FileLine* fl, AstNodeExpr* exprp, AstNode* ticksp)
        : ASTGEN_SUPER_Past(fl) {
        this->exprp(exprp);
        this->ticksp(ticksp);
    }
    ASTGEN_MEMBERS_AstPast;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstPatMember final : public AstNodeExpr {
    // Verilog '{a} or '{a{b}}
    // Parents: AstPattern
    // Children: expression, AstPattern, replication count
    // Expression to assign or another AstPattern (list if replicated)
    // @astgen op1 := lhssp : List[AstNodeExpr]
    // @astgen op2 := keyp : Optional[AstNode]
    // @astgen op3 := repp : Optional[AstNodeExpr]  // replication count, or nullptr for count 1
    bool m_default = false;

public:
    AstPatMember(FileLine* fl, AstNodeExpr* lhssp, AstNode* keyp, AstNodeExpr* repp)
        : ASTGEN_SUPER_PatMember(fl) {
        this->addLhssp(lhssp);
        this->keyp(keyp);
        this->repp(repp);
    }
    ASTGEN_MEMBERS_AstPatMember;
    string emitVerilog() override { return lhssp() ? "%f{%r{%k%l}}" : "%l"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs() * 2; }
    void dump(std::ostream& str = std::cout) const override;
    bool isDefault() const { return m_default; }
    void isDefault(bool flag) { m_default = flag; }
};
class AstPattern final : public AstNodeExpr {
    // Verilog '{a,b,c,d...}
    // Parents: AstNodeAssign, AstPattern, ...
    // Children: expression, AstPattern, AstPatReplicate
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := itemsp : List[AstNode] // AstPatReplicate, AstPatMember, etc
public:
    AstPattern(FileLine* fl, AstNode* itemsp)
        : ASTGEN_SUPER_Pattern(fl) {
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstPattern;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const VL_MT_STABLE { return dtypep() ? dtypep() : childDTypep(); }
};
class AstRand final : public AstNodeExpr {
    // $random/$random(seed) or $urandom/$urandom(seed)
    // Return a random number, based upon width()
    // @astgen op1 := seedp : Optional[AstNode]
    const bool m_urandom = false;  // $urandom vs $random
    const bool m_reset = false;  // Random reset, versus always random
public:
    class Reset {};
    AstRand(FileLine* fl, Reset, AstNodeDType* dtp, bool reset)
        : ASTGEN_SUPER_Rand(fl)
        , m_reset{reset} {
        dtypep(dtp);
    }
    AstRand(FileLine* fl, AstNode* seedp, bool urandom)
        : ASTGEN_SUPER_Rand(fl)
        , m_urandom{urandom} {
        this->seedp(seedp);
    }
    ASTGEN_MEMBERS_AstRand;
    string emitVerilog() override {
        return seedp() ? (m_urandom ? "%f$urandom(%l)" : "%f$random(%l)")
                       : (m_urandom ? "%f$urandom()" : "%f$random()");
    }
    string emitC() override {
        return m_reset ? "VL_RAND_RESET_%nq(%nw, %P)"
               : seedp()
                   // cppcheck-has-bug-suppress knownConditionTrueFalse
                   ? (urandom() ? "VL_URANDOM_SEEDED_%nq%lq(%li)"  //
                                : "VL_RANDOM_SEEDED_%nq%lq(%li)")
                   : (isWide() ? "VL_RANDOM_%nq(%nw, %P)"  //
                               : "VL_RANDOM_%nq()");
    }
    bool cleanOut() const override { return false; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool combinable(const AstRand* samep) const {
        return !seedp() && !samep->seedp() && reset() == samep->reset()
               && urandom() == samep->urandom();
    }
    bool reset() const { return m_reset; }
    bool urandom() const { return m_urandom; }
};
class AstRandRNG final : public AstNodeExpr {
    // Random used in a class using VlRNG
    // Return a random number, based upon width()
public:
    AstRandRNG(FileLine* fl, AstNodeDType* dtp)
        : ASTGEN_SUPER_RandRNG(fl) {
        dtypep(dtp);
    }
    ASTGEN_MEMBERS_AstRandRNG;
    string emitVerilog() override { return "%f$rngrandom()"; }
    string emitC() override {
        return isWide() ? "VL_RANDOM_RNG_%nq(__Vm_rng, %nw, %P)"  //
                        : "VL_RANDOM_RNG_%nq(__Vm_rng)";
    }
    bool cleanOut() const override { return false; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstRose final : public AstNodeExpr {
    // Verilog $rose
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := sentreep : Optional[AstSenTree]
public:
    AstRose(FileLine* fl, AstNodeExpr* exprp, AstSenTree* sentreep)
        : ASTGEN_SUPER_Rose(fl) {
        this->exprp(exprp);
        this->sentreep(sentreep);
    }
    ASTGEN_MEMBERS_AstRose;
    string emitVerilog() override { return "$rose(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstSFormatF final : public AstNodeExpr {
    // Convert format to string, generally under an AstDisplay or AstSFormat
    // Also used as "real" function for /*verilator sformat*/ functions
    // @astgen op1 := exprsp : List[AstNodeExpr]
    // @astgen op2 := scopeNamep : Optional[AstScopeName]
    string m_text;
    const bool m_hidden;  // Under display, etc
    bool m_hasFormat;  // Has format code
    const char m_missingArgChar;  // Format code when argument without format, 'h'/'o'/'b'
    VTimescale m_timeunit;  // Parent module time unit
public:
    class NoFormat {};
    AstSFormatF(FileLine* fl, const string& text, bool hidden, AstNodeExpr* exprsp,
                char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormatF(fl)
        , m_text{text}
        , m_hidden{hidden}
        , m_hasFormat{true}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addExprsp(exprsp);
    }
    AstSFormatF(FileLine* fl, NoFormat, AstNodeExpr* exprsp, char missingArgChar = 'd',
                bool hidden = true)
        : ASTGEN_SUPER_SFormatF(fl)
        , m_text{""}
        , m_hidden{hidden}
        , m_hasFormat{false}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addExprsp(exprsp);
    }
    ASTGEN_MEMBERS_AstSFormatF;
    string name() const override VL_MT_STABLE { return m_text; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSFormatF*>(samep)->text();
    }
    string verilogKwd() const override { return "$sformatf"; }
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    bool formatScopeTracking() const {  // Track scopeNamep();  Ok if false positive
        return (name().find("%m") != string::npos || name().find("%M") != string::npos);
    }
    bool hidden() const { return m_hidden; }
    void hasFormat(bool flag) { m_hasFormat = flag; }
    bool hasFormat() const { return m_hasFormat; }
    char missingArgChar() const { return m_missingArgChar; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstSScanF final : public AstNodeExpr {
    // @astgen op1 := exprsp : List[AstNode] // VarRefs for results
    // @astgen op2 := fromp : AstNode
    string m_text;

public:
    AstSScanF(FileLine* fl, const string& text, AstNode* fromp, AstNode* exprsp)
        : ASTGEN_SUPER_SScanF(fl)
        , m_text{text} {
        this->addExprsp(exprsp);
        this->fromp(fromp);
    }
    ASTGEN_MEMBERS_AstSScanF;
    string name() const override VL_MT_STABLE { return m_text; }
    string verilogKwd() const override { return "$sscanf"; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: makes output
    bool cleanOut() const override { return false; }
    bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSScanF*>(samep)->text();
    }
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
};
class AstSampled final : public AstNodeExpr {
    // Verilog $sampled
    // @astgen op1 := exprp : AstNode // AstNodeExpr or AstPropSpec
public:
    AstSampled(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER_Sampled(fl) {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstSampled;
    string emitVerilog() override { return "$sampled(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return 0; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstScopeName final : public AstNodeExpr {
    // For display %m and DPI context imports
    // Parents:  DISPLAY
    // @astgen op1 := scopeAttrp : List[AstText]
    // @astgen op2 := scopeEntrp : List[AstText]
    bool m_dpiExport = false;  // Is for dpiExport
    const bool m_forFormat = false;  // Is for a format %m
    string scopeNameFormatter(AstText* scopeTextp) const;
    string scopePrettyNameFormatter(AstText* scopeTextp) const;

public:
    class ForFormat {};
    AstScopeName(FileLine* fl, bool forFormat)
        : ASTGEN_SUPER_ScopeName(fl)
        , m_forFormat{forFormat} {
        dtypeSetUInt64();
    }
    ASTGEN_MEMBERS_AstScopeName;
    bool same(const AstNode* samep) const override {
        return (m_dpiExport == static_cast<const AstScopeName*>(samep)->m_dpiExport
                && m_forFormat == static_cast<const AstScopeName*>(samep)->m_forFormat);
    }
    string emitVerilog() override { return ""; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    void dump(std::ostream& str = std::cout) const override;
    string scopeSymName() const {  // Name for __Vscope variable including children
        return scopeNameFormatter(scopeAttrp());
    }
    string scopeDpiName() const {  // Name for DPI import scope
        return scopeNameFormatter(scopeEntrp());
    }
    string scopePrettySymName() const {  // Name for __Vscope variable including children
        return scopePrettyNameFormatter(scopeAttrp());
    }
    string scopePrettyDpiName() const {  // Name for __Vscope variable including children
        return scopePrettyNameFormatter(scopeEntrp());
    }
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
    bool forFormat() const { return m_forFormat; }
};
class AstSelLoopVars final : public AstNodeExpr {
    // Parser only concept "[id, id, id]" for a foreach statement
    // Unlike normal selects elements is a list
    // TODO: Should not be an AstNodeExpr, model foreach better
    // @astgen op1 := fromp : AstNodeExpr
    // @astgen op2 := elementsp : List[AstNode]
public:
    AstSelLoopVars(FileLine* fl, AstNodeExpr* fromp, AstNode* elementsp)
        : ASTGEN_SUPER_SelLoopVars(fl) {
        this->fromp(fromp);
        this->addElementsp(elementsp);
    }
    ASTGEN_MEMBERS_AstSelLoopVars;
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool maybePointedTo() const override { return false; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstSetAssoc final : public AstNodeExpr {
    // Set an assoc array element and return object, '{}
    // @astgen op1 := lhsp : AstNode
    // @astgen op2 := keyp : Optional[AstNode]
    // @astgen op3 := valuep : AstNodeExpr
public:
    AstSetAssoc(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNodeExpr* valuep)
        : ASTGEN_SUPER_SetAssoc(fl) {
        this->lhsp(lhsp);
        this->keyp(keyp);
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstSetAssoc;
    string emitVerilog() override { return "'{}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstSetWildcard final : public AstNodeExpr {
    // Set a wildcard assoc array element and return object, '{}
    // @astgen op1 := lhsp : AstNode
    // @astgen op2 := keyp : Optional[AstNode]
    // @astgen op3 := valuep : AstNodeExpr
public:
    AstSetWildcard(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNodeExpr* valuep)
        : ASTGEN_SUPER_SetWildcard(fl) {
        this->lhsp(lhsp);
        this->keyp(keyp);
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstSetWildcard;
    string emitVerilog() override { return "'{}"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstStable final : public AstNodeExpr {
    // Verilog $stable
    // @astgen op1 := exprp : AstNodeExpr
    // @astgen op2 := sentreep : Optional[AstSenTree]
public:
    AstStable(FileLine* fl, AstNodeExpr* exprp, AstSenTree* sentreep)
        : ASTGEN_SUPER_Stable(fl) {
        this->exprp(exprp);
        this->sentreep(sentreep);
    }
    ASTGEN_MEMBERS_AstStable;
    string emitVerilog() override { return "$stable(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstStackTraceF final : public AstNodeExpr {
    // $stacktrace used as function
public:
    explicit AstStackTraceF(FileLine* fl)
        : ASTGEN_SUPER_StackTraceF(fl) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstStackTraceF;
    string verilogKwd() const override { return "$stacktrace"; }
    string emitVerilog() override { return verilogKwd(); }
    string emitC() override { return "VL_STACKTRACE_N()"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstStructSel final : public AstNodeExpr {
    // Unpacked struct/union member access
    // Parents: math|stmt
    // Children: varref, math
    // @astgen op1 := fromp : AstNodeExpr
private:
    string m_name;  // Name of the member
public:
    AstStructSel(FileLine* fl, AstNodeExpr* fromp, const string& name)
        : ASTGEN_SUPER_StructSel(fl)
        , m_name{name} {
        this->fromp(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_AstStructSel;
    string name() const override VL_MT_STABLE { return m_name; }
    void name(const string& name) override { m_name = name; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override {
        // Not a union
        return VN_IS(fromp()->dtypep()->skipRefp(), StructDType);
    }
    bool same(const AstNode* samep) const override {
        const AstStructSel* const sp = static_cast<const AstStructSel*>(samep);
        return m_name == sp->m_name;
    }
    int instrCount() const override { return widthInstrs(); }
};
class AstSysIgnore final : public AstNodeExpr {
    // @astgen op1 := exprsp : List[AstNode] // Expressions to output (???)
public:
    AstSysIgnore(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_SysIgnore(fl) {
        this->addExprsp(exprsp);
    }
    ASTGEN_MEMBERS_AstSysIgnore;
    string verilogKwd() const override { return "$ignored"; }
    bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    bool isPredictOptimizable() const override { return false; }  // Though deleted before opt
    bool isPure() override { return false; }  // Though deleted before opt
    bool isOutputter() override { return true; }  // Though deleted before opt
    int instrCount() const override { return INSTR_COUNT_PLI; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstSystemF final : public AstNodeExpr {
    // $system used as function
    // @astgen op1 := lhsp : AstNode
public:
    AstSystemF(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SystemF(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstSystemF;
    string verilogKwd() const override { return "$system"; }
    string emitVerilog() override { return verilogKwd(); }
    string emitC() override { return "VL_SYSTEM_%nq(%lw, %P)"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstTestPlusArgs final : public AstNodeExpr {
    // Search expression. If nullptr then this is a $test$plusargs instead of $value$plusargs.
    // @astgen op1 := searchp : Optional[AstNode]
public:
    AstTestPlusArgs(FileLine* fl, AstNode* searchp)
        : ASTGEN_SUPER_TestPlusArgs(fl) {
        this->searchp(searchp);
    }
    ASTGEN_MEMBERS_AstTestPlusArgs;
    string verilogKwd() const override { return "$test$plusargs"; }
    string emitVerilog() override { return verilogKwd(); }
    string emitC() override { return "VL_VALUEPLUSARGS_%nq(%lw, %P, nullptr)"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstThisRef final : public AstNodeExpr {
    // Reference to 'this'.
    // @astgen op1 := childDTypep : Optional[AstClassRefDType] // dtype of the node
public:
    AstThisRef(FileLine* fl, VFlagChildDType, AstClassRefDType* dtypep)
        : ASTGEN_SUPER_ThisRef(fl) {
        childDTypep(dtypep);
    }
    ASTGEN_MEMBERS_AstThisRef;
    string emitC() override { return "this"; }
    string emitVerilog() override { return "this"; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool cleanOut() const override { return true; }
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* subDTypep() const VL_MT_STABLE { return dtypep() ? dtypep() : childDTypep(); }
};
class AstTimePrecision final : public AstNodeExpr {
    // Verilog $timeprecision
public:
    explicit AstTimePrecision(FileLine* fl)
        : ASTGEN_SUPER_TimePrecision(fl) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstTimePrecision;
    string emitVerilog() override { return "$timeprecision"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstTimeUnit final : public AstNodeExpr {
    VTimescale m_timeunit;  // Parent module time unit
    // Verilog $timeunit
public:
    explicit AstTimeUnit(FileLine* fl)
        : ASTGEN_SUPER_TimeUnit(fl) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstTimeUnit;
    string emitVerilog() override { return "$timeunit"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* /*samep*/) const override { return true; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstUCFunc final : public AstNodeExpr {
    // User's $c function
    // @astgen op1 := exprsp : List[AstNode] // Expressions to print (some are AstText)
public:
    AstUCFunc(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_UCFunc(fl) {
        this->addExprsp(exprsp);
    }
    ASTGEN_MEMBERS_AstUCFunc;
    bool cleanOut() const override { return false; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
    bool isGateOptimizable() const override { return false; }
    bool isSubstOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstUnbounded final : public AstNodeExpr {
    // A $ in the parser, used for unbounded and queues
    // Due to where is used, treated as Signed32
public:
    explicit AstUnbounded(FileLine* fl)
        : ASTGEN_SUPER_Unbounded(fl) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstUnbounded;
    string emitVerilog() override { return "$"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstUnlinkedRef final : public AstNodeExpr {
    // As-of-yet unlinkable Ref
    // @astgen op1 := refp : AstNode
    // @astgen op2 := cellrefp : AstNode

    string m_name;  // Var name // TODO: There is no way to access this, fix or remove
public:
    AstUnlinkedRef(FileLine* fl, AstNode* refp, const string& name, AstNode* cellrefp)
        : ASTGEN_SUPER_UnlinkedRef(fl)
        , m_name{name} {
        this->refp(refp);
        this->cellrefp(cellrefp);
    }
    ASTGEN_MEMBERS_AstUnlinkedRef;

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstValuePlusArgs final : public AstNodeExpr {
    // Search expression. If nullptr then this is a $test$plusargs instead of $value$plusargs.
    // @astgen op1 := searchp : Optional[AstNode]
    // @astgen op2 := outp : AstNode // VarRef for result
public:
    AstValuePlusArgs(FileLine* fl, AstNode* searchp, AstNode* outp)
        : ASTGEN_SUPER_ValuePlusArgs(fl) {
        this->searchp(searchp);
        this->outp(outp);
    }
    ASTGEN_MEMBERS_AstValuePlusArgs;
    string verilogKwd() const override { return "$value$plusargs"; }
    string emitVerilog() override { return "%f$value$plusargs(%l, %k%r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return !outp(); }
    bool cleanOut() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstWith final : public AstNodeExpr {
    // Used as argument to method, then to AstCMethodHard
    // dtypep() contains the with lambda's return dtype
    // Parents: funcref (similar to AstArg)
    // Children: LambdaArgRef that declares the item variable
    // Children: LambdaArgRef that declares the item.index variable
    // Children: expression (equation establishing the with)
    // @astgen op1 := indexArgRefp : AstLambdaArgRef
    // @astgen op2 := valueArgRefp : AstLambdaArgRef
    // @astgen op3 := exprp : List[AstNode]
public:
    AstWith(FileLine* fl, AstLambdaArgRef* indexArgRefp, AstLambdaArgRef* valueArgRefp,
            AstNodeExpr* exprp)
        : ASTGEN_SUPER_With(fl) {
        this->indexArgRefp(indexArgRefp);
        this->valueArgRefp(valueArgRefp);
        this->addExprp(exprp);
    }
    ASTGEN_MEMBERS_AstWith;
    bool same(const AstNode* /*samep*/) const override { return true; }
    const char* broken() const override {
        BROKEN_RTN(!indexArgRefp());  // varp needed to know lambda's arg dtype
        BROKEN_RTN(!valueArgRefp());  // varp needed to know lambda's arg dtype
        return nullptr;
    }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};
class AstWithParse final : public AstNodeExpr {
    // In early parse, FUNC(index) WITH equation-using-index
    // Replaced with AstWith
    // Parents: expr|stmt
    // Children: funcref, expr
    // @astgen op1 := funcrefp : AstNode
    // @astgen op2 := exprp : Optional[AstNodeExpr]
public:
    AstWithParse(FileLine* fl, AstNode* funcrefp, AstNodeExpr* exprp)
        : ASTGEN_SUPER_WithParse(fl) {
        this->funcrefp(funcrefp);
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstWithParse;
    bool same(const AstNode* /*samep*/) const override { return true; }

    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { V3ERROR_NA_RETURN(true); }
};

// === AstNodeBiop ===
class AstBufIf1 final : public AstNodeBiop {
    // lhs is enable, rhs is data to drive
    // Note unlike the Verilog bufif1() UDP, this allows any width; each lhsp
    // bit enables respective rhsp bit
public:
    AstBufIf1(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_BufIf1(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstBufIf1;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstBufIf1{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opBufIf1(lhs, rhs);
    }
    string emitVerilog() override { return "bufif(%r,%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    bool cleanOut() const override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstCastDynamic final : public AstNodeBiop {
    // Verilog $cast used as a function
    // Task usage of $cast is converted during parse to assert($cast(...))
    // lhsp() is value (we are converting FROM) to match AstCCast etc, this
    // is opposite of $cast's order, because the first access is to the
    // value reading from.  Suggest use fromp()/top() instead of lhsp/rhsp().
    // @astgen alias op1 := fromp
    // @astgen alias op2 := top
public:
    AstCastDynamic(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_CastDynamic(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstCastDynamic;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstCastDynamic{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f$cast(%r, %l)"; }
    string emitC() override { return "VL_DYNAMIC_CAST(%r, %l)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 20; }
    bool isPure() override { return true; }
};
class AstCompareNN final : public AstNodeBiop {
    // Verilog str.compare() and str.icompare()
    const bool m_ignoreCase;  // True for str.icompare()
public:
    AstCompareNN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, bool ignoreCase)
        : ASTGEN_SUPER_CompareNN(fl, lhsp, rhsp)
        , m_ignoreCase{ignoreCase} {
        dtypeSetUInt32();
    }
    ASTGEN_MEMBERS_AstCompareNN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstCompareNN{fileline(), lhsp, rhsp, m_ignoreCase};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCompareNN(lhs, rhs, m_ignoreCase);
    }
    string name() const override VL_MT_STABLE { return m_ignoreCase ? "icompare" : "compare"; }
    string emitVerilog() override {
        return m_ignoreCase ? "%k(%l.icompare(%r))" : "%k(%l.compare(%r))";
    }
    string emitC() override {
        return m_ignoreCase ? "VL_CMP_NN(%li,%ri,true)" : "VL_CMP_NN(%li,%ri,false)";
    }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstConcat final : public AstNodeBiop {
    // If you're looking for {#{}}, see AstReplicate
public:
    AstConcat(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Concat(fl, lhsp, rhsp) {
        if (lhsp->dtypep() && rhsp->dtypep()) {
            dtypeSetLogicSized(lhsp->dtypep()->width() + rhsp->dtypep()->width(),
                               VSigning::UNSIGNED);
        }
    }
    ASTGEN_MEMBERS_AstConcat;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstConcat{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f{%l, %k%r}"; }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcat(lhs, rhs);
    }
    string emitC() override { return "VL_CONCAT_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 2; }
};
class AstConcatN final : public AstNodeBiop {
    // String concatenate
public:
    AstConcatN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_ConcatN(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstConcatN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstConcatN{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f{%l, %k%r}"; }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcatN(lhs, rhs);
    }
    string emitC() override { return "VL_CONCATN_NNN(%li, %ri)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstDiv final : public AstNodeBiop {
public:
    AstDiv(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Div(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstDiv;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstDiv{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDiv(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f/ %r)"; }
    string emitC() override { return "VL_DIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
};
class AstDivD final : public AstNodeBiop {
public:
    AstDivD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DivD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstDivD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstDivD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f/ %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "/"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_DIV; }
    bool doubleFlavor() const override { return true; }
};
class AstDivS final : public AstNodeBiop {
public:
    AstDivS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DivS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstDivS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstDivS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f/ %r)"; }
    string emitC() override { return "VL_DIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
    bool signedFlavor() const override { return true; }
};
class AstEqWild final : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
public:
    AstEqWild(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_EqWild(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEqWild;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEqWild{fileline(), lhsp, rhsp};
    }
    // Return AstEqWild/AstEqD
    static AstNodeBiop* newTyped(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp);
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildEq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f==? %r)"; }
    string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstFGetS final : public AstNodeBiop {
public:
    AstFGetS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_FGetS(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstFGetS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstFGetS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%f$fgets(%l,%r)"; }
    string emitC() override {
        return strgp()->dtypep()->basicp()->isString() ? "VL_FGETS_NI(%li, %ri)"
                                                       : "VL_FGETS_%nqX%rq(%lw, %P, &(%li), %ri)";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 64; }
    AstNode* strgp() const { return lhsp(); }
    AstNode* filep() const { return rhsp(); }
};
class AstFUngetC final : public AstNodeBiop {
public:
    AstFUngetC(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_FUngetC(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstFUngetC;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstFUngetC{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f$ungetc(%r, %l)"; }
    // Non-existent filehandle returns EOF
    string emitC() override {
        return "(%li ? (ungetc(%ri, VL_CVT_I_FP(%li)) >= 0 ? 0 : -1) : -1)";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 64; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
    AstNode* charp() const { return rhsp(); }
};
class AstGetcN final : public AstNodeBiop {
    // Verilog string.getc()
public:
    AstGetcN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GetcN(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstGetcN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGetcN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGetcN(lhs, rhs);
    }
    string name() const override VL_MT_STABLE { return "getc"; }
    string emitVerilog() override { return "%k(%l.getc(%r))"; }
    string emitC() override { return "VL_GETC_N(%li,%ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstGetcRefN final : public AstNodeBiop {
    // Verilog string[#] on the left-hand-side of assignment
    // Spec says is of type byte (not string of single character)
public:
    AstGetcRefN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GetcRefN(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstGetcRefN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGetcRefN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k%l[%r]"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstGt final : public AstNodeBiop {
public:
    AstGt(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Gt(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGt;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGt{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGt(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f> %r)"; }
    string emitC() override { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ">"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstGtD final : public AstNodeBiop {
public:
    AstGtD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GtD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGtD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGtD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f> %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return ">"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstGtN final : public AstNodeBiop {
public:
    AstGtN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GtN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGtN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGtN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f> %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return ">"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstGtS final : public AstNodeBiop {
public:
    AstGtS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GtS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGtS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGtS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f> %r)"; }
    string emitC() override { return "VL_GTS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool signedFlavor() const override { return true; }
};
class AstGte final : public AstNodeBiop {
public:
    AstGte(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Gte(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGte;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGte{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGte(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f>= %r)"; }
    string emitC() override { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ">="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstGteD final : public AstNodeBiop {
public:
    AstGteD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GteD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGteD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGteD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f>= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return ">="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstGteN final : public AstNodeBiop {
public:
    AstGteN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GteN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGteN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGteN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f>= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return ">="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstGteS final : public AstNodeBiop {
public:
    AstGteS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_GteS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstGteS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstGteS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f>= %r)"; }
    string emitC() override { return "VL_GTES_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool signedFlavor() const override { return true; }
};
class AstLogAnd final : public AstNodeBiop {
public:
    AstLogAnd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LogAnd(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLogAnd;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLogAnd{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogAnd(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f&& %r)"; }
    string emitC() override { return "VL_LOGAND_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "&&"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstLogIf final : public AstNodeBiop {
public:
    AstLogIf(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LogIf(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLogIf;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLogIf{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogIf(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f-> %r)"; }
    string emitC() override { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "->"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstLogOr final : public AstNodeBiop {
public:
    AstLogOr(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LogOr(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLogOr;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLogOr{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogOr(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f|| %r)"; }
    string emitC() override { return "VL_LOGOR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "||"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstLt final : public AstNodeBiop {
public:
    AstLt(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Lt(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLt;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLt{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLt(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f< %r)"; }
    string emitC() override { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "<"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstLtD final : public AstNodeBiop {
public:
    AstLtD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LtD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLtD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLtD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f< %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "<"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstLtN final : public AstNodeBiop {
public:
    AstLtN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LtN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLtN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLtN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f< %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "<"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstLtS final : public AstNodeBiop {
public:
    AstLtS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LtS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLtS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLtS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f< %r)"; }
    string emitC() override { return "VL_LTS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool signedFlavor() const override { return true; }
};
class AstLte final : public AstNodeBiop {
public:
    AstLte(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Lte(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLte;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLte{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLte(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<= %r)"; }
    string emitC() override { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "<="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstLteD final : public AstNodeBiop {
public:
    AstLteD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LteD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLteD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLteD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "<="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstLteN final : public AstNodeBiop {
public:
    AstLteN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LteN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLteN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLteN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "<="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstLteS final : public AstNodeBiop {
public:
    AstLteS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LteS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLteS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLteS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<= %r)"; }
    string emitC() override { return "VL_LTES_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool signedFlavor() const override { return true; }
};
class AstModDiv final : public AstNodeBiop {
public:
    AstModDiv(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_ModDiv(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstModDiv;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstModDiv{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDiv(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f%% %r)"; }
    string emitC() override { return "VL_MODDIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
};
class AstModDivS final : public AstNodeBiop {
public:
    AstModDivS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_ModDivS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstModDivS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstModDivS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDivS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f%% %r)"; }
    string emitC() override { return "VL_MODDIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
    bool signedFlavor() const override { return true; }
};
class AstNeqWild final : public AstNodeBiop {
public:
    AstNeqWild(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NeqWild(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeqWild;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeqWild{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildNeq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f!=? %r)"; }
    string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstPow final : public AstNodeBiop {
public:
    AstPow(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Pow(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstPow;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstPow{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPow(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f** %r)"; }
    string emitC() override { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
};
class AstPowD final : public AstNodeBiop {
public:
    AstPowD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_PowD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstPowD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstPowD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f** %r)"; }
    string emitC() override { return "pow(%li,%ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL_DIV * 5; }
    bool doubleFlavor() const override { return true; }
};
class AstPowSS final : public AstNodeBiop {
public:
    AstPowSS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_PowSS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstPowSS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstPowSS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f** %r)"; }
    string emitC() override { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,1)"; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    bool signedFlavor() const override { return true; }
};
class AstPowSU final : public AstNodeBiop {
public:
    AstPowSU(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_PowSU(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstPowSU;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstPowSU{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSU(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f** %r)"; }
    string emitC() override { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,0)"; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    bool signedFlavor() const override { return true; }
};
class AstPowUS final : public AstNodeBiop {
public:
    AstPowUS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_PowUS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstPowUS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstPowUS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowUS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f** %r)"; }
    string emitC() override { return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 0,1)"; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    bool signedFlavor() const override { return true; }
};
class AstReplicate final : public AstNodeBiop {
    // Also used as a "Uniop" flavor of Concat, e.g. "{a}"
    // Verilog {rhs{lhs}} - Note rhsp() is the replicate value, not the lhsp()
    // @astgen alias op1 := srcp
    // @astgen alias op2 := countp
public:
    AstReplicate(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Replicate(fl, lhsp, rhsp) {
        if (lhsp) {
            if (const AstConst* const constp = VN_CAST(rhsp, Const)) {
                dtypeSetLogicSized(lhsp->width() * constp->toUInt(), VSigning::UNSIGNED);
            }
        }
    }
    AstReplicate(FileLine* fl, AstNodeExpr* lhsp, uint32_t repCount)
        : AstReplicate{fl, lhsp, new AstConst{fl, repCount}} {}
    ASTGEN_MEMBERS_AstReplicate;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstReplicate{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opRepl(lhs, rhs);
    }
    string emitVerilog() override { return "%f{%r{%k%l}}"; }
    string emitC() override { return "VL_REPLICATE_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 2; }
};
class AstReplicateN final : public AstNodeBiop {
    // String replicate
public:
    AstReplicateN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_ReplicateN(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    AstReplicateN(FileLine* fl, AstNodeExpr* lhsp, uint32_t repCount)
        : AstReplicateN{fl, lhsp, new AstConst{fl, repCount}} {}
    ASTGEN_MEMBERS_AstReplicateN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstReplicateN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opReplN(lhs, rhs);
    }
    string emitVerilog() override { return "%f{%r{%k%l}}"; }
    string emitC() override { return "VL_REPLICATEN_NN%rq(%li, %ri)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 2; }
    bool stringFlavor() const override { return true; }
};
class AstShiftL final : public AstNodeBiop {
public:
    AstShiftL(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftL(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstShiftL;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstShiftL{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftL(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<< %r)"; }
    string emitC() override { return "VL_SHIFTL_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : "<<";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
};
class AstShiftR final : public AstNodeBiop {
public:
    AstShiftR(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftR(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstShiftR;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstShiftR{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftR(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f>> %r)"; }
    string emitC() override { return "VL_SHIFTR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : ">>";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    // LHS size might be > output size, so don't want to force size
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstShiftRS final : public AstNodeBiop {
    // Shift right with sign extension, >>> operator
    // Output data type's width determines which bit is used for sign extension
public:
    AstShiftRS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftRS(fl, lhsp, rhsp) {
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::SIGNED);
    }
    ASTGEN_MEMBERS_AstShiftRS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstShiftRS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftRS(lhs, rhs, lhsp()->widthMinV());
    }
    string emitVerilog() override { return "%k(%l %f>>> %r)"; }
    string emitC() override { return "VL_SHIFTRS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool signedFlavor() const override { return true; }
};
class AstSub final : public AstNodeBiop {
public:
    AstSub(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Sub(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstSub;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstSub{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSub(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f- %r)"; }
    string emitC() override { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "-"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
};
class AstSubD final : public AstNodeBiop {
public:
    AstSubD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_SubD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstSubD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstSubD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSubD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f- %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "-"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstURandomRange final : public AstNodeBiop {
    // $urandom_range
public:
    AstURandomRange(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_URandomRange(fl, lhsp, rhsp) {
        dtypeSetUInt32();  // Says IEEE
    }
    ASTGEN_MEMBERS_AstURandomRange;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstURandomRange{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%f$urandom_range(%l, %r)"; }
    string emitC() override { return "VL_URANDOM_RANGE_%nq(%li, %ri)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
};

// === AstNodeBiCom ===
class AstEq final : public AstNodeBiCom {
public:
    AstEq(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Eq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEq;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEq{fileline(), lhsp, rhsp};
    }
    // Return AstEq/AstEqD
    static AstNodeBiop* newTyped(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp);
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f== %r)"; }
    string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstEqCase final : public AstNodeBiCom {
public:
    AstEqCase(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_EqCase(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEqCase;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEqCase{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseEq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f=== %r)"; }
    string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstEqD final : public AstNodeBiCom {
public:
    AstEqD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_EqD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEqD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEqD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f== %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstEqN final : public AstNodeBiCom {
public:
    AstEqN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_EqN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEqN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEqN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f== %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstEqT final : public AstNodeBiCom {
    // Equal (==) for data types
public:
    AstEqT(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_EqT(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstEqT;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstEqT{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k(%l %f== %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "=="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
};
class AstLogEq final : public AstNodeBiCom {
public:
    AstLogEq(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_LogEq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLogEq;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstLogEq{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogEq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f<-> %r)"; }
    string emitC() override { return "VL_LOGEQ_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "<->"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstNeq final : public AstNodeBiCom {
public:
    AstNeq(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Neq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeq;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeq{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f!= %r)"; }
    string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstNeqCase final : public AstNodeBiCom {
public:
    AstNeqCase(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NeqCase(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeqCase;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeqCase{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseNeq(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f!== %r)"; }
    string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstNeqD final : public AstNodeBiCom {
public:
    AstNeqD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NeqD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeqD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeqD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f!= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstNeqN final : public AstNodeBiCom {
public:
    AstNeqN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NeqN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeqN;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeqN{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqN(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f!= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
    bool stringFlavor() const override { return true; }
};
class AstNeqT final : public AstNodeBiCom {
    // Not-equal (!=) for data types
public:
    AstNeqT(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_NeqT(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstNeqT;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstNeqT{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k(%l %f!= %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "!="; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_STR; }
};

// === AstNodeBiComAsv ===
class AstAdd final : public AstNodeBiComAsv {
public:
    AstAdd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Add(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstAdd;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAdd{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAdd(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f+ %r)"; }
    string emitC() override { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "+"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
};
class AstAddD final : public AstNodeBiComAsv {
public:
    AstAddD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AddD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstAddD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAddD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAddD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f+ %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "+"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstAnd final : public AstNodeBiComAsv {
public:
    AstAnd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_And(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstAnd;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAnd{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAnd(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f& %r)"; }
    string emitC() override { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "&"; }
    bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstMul final : public AstNodeBiComAsv {
public:
    AstMul(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Mul(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstMul;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstMul{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMul(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f* %r)"; }
    string emitC() override { return "VL_MUL_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "*"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL; }
};
class AstMulD final : public AstNodeBiComAsv {
public:
    AstMulD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_MulD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstMulD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstMulD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulD(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f* %r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "*"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstMulS final : public AstNodeBiComAsv {
public:
    AstMulS(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_MulS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstMulS;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstMulS{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulS(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f* %r)"; }
    string emitC() override { return "VL_MULS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return ""; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL; }
    bool signedFlavor() const override { return true; }
};
class AstOr final : public AstNodeBiComAsv {
public:
    AstOr(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Or(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstOr;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstOr{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opOr(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f| %r)"; }
    string emitC() override { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "|"; }
    bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};
class AstXor final : public AstNodeBiComAsv {
public:
    AstXor(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Xor(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstXor;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstXor{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opXor(lhs, rhs);
    }
    string emitVerilog() override { return "%k(%l %f^ %r)"; }
    string emitC() override { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    string emitSimpleOperator() override { return "^"; }
    bool cleanOut() const override { return false; }  // Lclean && Rclean
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
};

// === AstNodeDistBiop ===
class AstDistChiSquare final : public AstNodeDistBiop {
public:
    AstDistChiSquare(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DistChiSquare(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstDistChiSquare;
    string emitVerilog() override { return "%f$dist_chi_square(%l, %r)"; }
    string emitC() override { return "VL_DIST_CHI_SQUARE(%li, %ri)"; }
};
class AstDistExponential final : public AstNodeDistBiop {
public:
    AstDistExponential(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DistExponential(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstDistExponential;
    string emitVerilog() override { return "%f$dist_exponential(%l, %r)"; }
    string emitC() override { return "VL_DIST_EXPONENTIAL(%li, %ri)"; }
};
class AstDistPoisson final : public AstNodeDistBiop {
public:
    AstDistPoisson(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DistPoisson(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstDistPoisson;
    string emitVerilog() override { return "%f$dist_poisson(%l, %r)"; }
    string emitC() override { return "VL_DIST_POISSON(%li, %ri)"; }
};
class AstDistT final : public AstNodeDistBiop {
public:
    AstDistT(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DistT(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstDistT;
    string emitVerilog() override { return "%f$dist_t(%l, %r)"; }
    string emitC() override { return "VL_DIST_T(%li, %ri)"; }
};

// === AstNodeSel ===
class AstArraySel final : public AstNodeSel {
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), NodeArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), NodeArrayDType)->subDTypep());
        }
    }

public:
    AstArraySel(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : ASTGEN_SUPER_ArraySel(fl, fromp, bitp) {
        init(fromp);
    }
    AstArraySel(FileLine* fl, AstNodeExpr* fromp, int bit)
        : ASTGEN_SUPER_ArraySel(fl, fromp, new AstConst(fl, bit)) {  // Need () constructor
        init(fromp);
    }
    ASTGEN_MEMBERS_AstArraySel;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstArraySel{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA; /* How can from be a const? */
    }
    string emitVerilog() override { return "%k(%l%f[%r])"; }
    string emitC() override { return "%li%k[%ri]"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool isGateOptimizable() const override { return true; }  // esp for V3Const::ifSameAssign
    bool isPredictOptimizable() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    // Special operators
    // Return base var (or const) nodep dereferences
    static AstNode* baseFromp(AstNode* nodep, bool overMembers);
};
class AstAssocSel final : public AstNodeSel {
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), AssocArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), AssocArrayDType)->subDTypep());
        }
    }

public:
    AstAssocSel(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : ASTGEN_SUPER_AssocSel(fl, fromp, bitp) {
        init(fromp);
    }
    ASTGEN_MEMBERS_AstAssocSel;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAssocSel{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k(%l%f[%r])"; }
    string emitC() override { return "%li%k[%ri]"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool isGateOptimizable() const override { return true; }  // esp for V3Const::ifSameAssign
    bool isPredictOptimizable() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
};
class AstWildcardSel final : public AstNodeSel {
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), WildcardArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), WildcardArrayDType)->subDTypep());
        }
    }

public:
    AstWildcardSel(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : ASTGEN_SUPER_WildcardSel(fl, fromp, bitp) {
        init(fromp);
    }
    ASTGEN_MEMBERS_AstWildcardSel;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstWildcardSel{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k(%l%f[%r])"; }
    string emitC() override { return "%li%k[%ri]"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool isGateOptimizable() const override { return true; }  // esp for V3Const::ifSameAssign
    bool isPredictOptimizable() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
};
class AstWordSel final : public AstNodeSel {
    // Select a single word from a multi-word wide value
public:
    AstWordSel(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : ASTGEN_SUPER_WordSel(fl, fromp, bitp) {
        dtypeSetUInt32();  // Always used on WData arrays so returns edata size
    }
    ASTGEN_MEMBERS_AstWordSel;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstWordSel{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { return "%k(%l%f[%r])"; }
    string emitC() override {
        return "%li[%ri]";
    }  // Not %k, as usually it's a small constant rhsp
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};

// === AstNodeStream ===
class AstStreamL final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamL(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_StreamL(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstStreamL;
    AstNodeStream* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstStreamL{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f{ << %r %k{%l} }"; }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opStreamL(lhs, rhs);
    }
    string emitC() override { return "VL_STREAML_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 2; }
};
class AstStreamR final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamR(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_StreamR(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstStreamR;
    AstNodeStream* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstStreamR{fileline(), lhsp, rhsp};
    }
    string emitVerilog() override { return "%f{ >> %r %k{%l} }"; }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAssign(lhs);
    }
    string emitC() override { return isWide() ? "VL_ASSIGN_W(%nw, %P, %li)" : "%li"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 2; }
};

// === AstNodeSystemBiopD ===
class AstAtan2D final : public AstNodeSystemBiopD {
public:
    AstAtan2D(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_Atan2D(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstAtan2D;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAtan2D{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::atan2(lhs.toDouble(), rhs.toDouble()));
    }
    string emitVerilog() override { return "%f$atan2(%l,%r)"; }
    string emitC() override { return "atan2(%li,%ri)"; }
};
class AstHypotD final : public AstNodeSystemBiopD {
public:
    AstHypotD(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_HypotD(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstHypotD;
    AstNodeExpr* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstHypotD{fileline(), lhsp, rhsp};
    }
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::hypot(lhs.toDouble(), rhs.toDouble()));
    }
    string emitVerilog() override { return "%f$hypot(%l,%r)"; }
    string emitC() override { return "hypot(%li,%ri)"; }
};

// === AstNodeCCall ===
class AstCCall final : public AstNodeCCall {
    // C++ function call
    VSelfPointerText m_selfPointer
        = VSelfPointerText{VSelfPointerText::Empty()};  // Output code object
                                                        // pointer (e.g.: 'this')
public:
    AstCCall(FileLine* fl, AstCFunc* funcp, AstNodeExpr* argsp = nullptr)
        : ASTGEN_SUPER_CCall(fl, funcp, argsp) {}
    ASTGEN_MEMBERS_AstCCall;

    const VSelfPointerText& selfPointer() const { return m_selfPointer; }
    void selfPointer(const VSelfPointerText& selfPointer) { m_selfPointer = selfPointer; }
    string selfPointerProtect(bool useSelfForThis) const {
        return selfPointer().protect(useSelfForThis, protect());
    }
};
class AstCMethodCall final : public AstNodeCCall {
    // C++ method call
    // @astgen op1 := fromp : AstNodeExpr
public:
    AstCMethodCall(FileLine* fl, AstNodeExpr* fromp, AstCFunc* funcp, AstNodeExpr* argsp = nullptr)
        : ASTGEN_SUPER_CMethodCall(fl, funcp, argsp) {
        this->fromp(fromp);
    }
    ASTGEN_MEMBERS_AstCMethodCall;
    const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeCCall::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
};
class AstCNew final : public AstNodeCCall {
    // C++ new() call
public:
    AstCNew(FileLine* fl, AstCFunc* funcp, AstNodeExpr* argsp = nullptr)
        : ASTGEN_SUPER_CNew(fl, funcp, argsp) {}
    ASTGEN_MEMBERS_AstCNew;
};

// === AstNodeFTaskRef ===
class AstFuncRef final : public AstNodeFTaskRef {
    // A reference to a function
public:
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_FuncRef(fl, (AstNode*)namep, pinsp) {}
    AstFuncRef(FileLine* fl, const string& name, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_FuncRef(fl, name, pinsp) {}
    ASTGEN_MEMBERS_AstFuncRef;
};
class AstMethodCall final : public AstNodeFTaskRef {
    // A reference to a member task (or function)
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    // @astgen op2 := fromp : AstNodeExpr
    //
public:
    AstMethodCall(FileLine* fl, AstNodeExpr* fromp, VFlagChildDType, const string& name,
                  AstNodeExpr* pinsp)
        : ASTGEN_SUPER_MethodCall(fl, name, pinsp) {
        this->fromp(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMethodCall(FileLine* fl, AstNodeExpr* fromp, const string& name, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_MethodCall(fl, name, pinsp) {
        this->fromp(fromp);
    }
    ASTGEN_MEMBERS_AstMethodCall;
    const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeFTaskRef::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
};
class AstNew final : public AstNodeFTaskRef {
    // New as constructor
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
public:
    AstNew(FileLine* fl, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_New(fl, "new", pinsp) {}
    ASTGEN_MEMBERS_AstNew;
    bool same(const AstNode* /*samep*/) const override { return true; }
    int instrCount() const override { return widthInstrs(); }
};
class AstTaskRef final : public AstNodeFTaskRef {
    // A reference to a task
public:
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_TaskRef(fl, (AstNode*)namep, pinsp) {
        dtypeSetVoid();
    }
    AstTaskRef(FileLine* fl, const string& name, AstNodeExpr* pinsp)
        : ASTGEN_SUPER_TaskRef(fl, name, pinsp) {
        dtypeSetVoid();
    }
    ASTGEN_MEMBERS_AstTaskRef;
};

// === AstNodePreSel ===
class AstSelBit final : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
    // @astgen alias op2 := bitp
public:
    AstSelBit(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp)
        : ASTGEN_SUPER_SelBit(fl, fromp, bitp, nullptr) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTGEN_MEMBERS_AstSelBit;
};
class AstSelExtract final : public AstNodePreSel {
    // Range extraction, gets replaced with AstSel
    // @astgen alias op2 := leftp
    // @astgen alias op3 := rightp
public:
    AstSelExtract(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* msbp, AstNodeExpr* lsbp)
        : ASTGEN_SUPER_SelExtract(fl, fromp, msbp, lsbp) {}
    ASTGEN_MEMBERS_AstSelExtract;
};
class AstSelMinus final : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    // @astgen alias op2 := bitp
    // @astgen alias op3 := widtph
public:
    AstSelMinus(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp, AstNodeExpr* widthp)
        : ASTGEN_SUPER_SelMinus(fl, fromp, bitp, widthp) {}
    ASTGEN_MEMBERS_AstSelMinus;
};
class AstSelPlus final : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
    // @astgen alias op2 := bitp
    // @astgen alias op3 := widtph
public:
    AstSelPlus(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* bitp, AstNodeExpr* widthp)
        : ASTGEN_SUPER_SelPlus(fl, fromp, bitp, widthp) {}
    ASTGEN_MEMBERS_AstSelPlus;
};

// === AstNodeQuadop ===
class AstCountBits final : public AstNodeQuadop {
    // Number of bits set in vector
public:
    AstCountBits(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* ctrl1p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl1p->cloneTreePure(false),
                                 ctrl1p->cloneTreePure(false)) {}
    AstCountBits(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* ctrl1p, AstNodeExpr* ctrl2p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl2p, ctrl2p->cloneTreePure(false)) {}
    AstCountBits(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* ctrl1p, AstNodeExpr* ctrl2p,
                 AstNodeExpr* ctrl3p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl2p, ctrl3p) {}
    ASTGEN_MEMBERS_AstCountBits;
    void numberOperate(V3Number& out, const V3Number& expr, const V3Number& ctrl1,
                       const V3Number& ctrl2, const V3Number& ctrl3) override {
        out.opCountBits(expr, ctrl1, ctrl2, ctrl3);
    }
    string emitVerilog() override { return "%f$countbits(%l, %r, %f, %o)"; }
    string emitC() override { return ""; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool cleanThs() const override { return true; }
    bool cleanFhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
    bool sizeMattersFhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 16; }
};

// === AstNodeTermop ===
class AstTime final : public AstNodeTermop {
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTime(FileLine* fl, const VTimescale& timeunit)
        : ASTGEN_SUPER_Time(fl)
        , m_timeunit{timeunit} {
        dtypeSetUInt64();
    }
    ASTGEN_MEMBERS_AstTime;
    string emitVerilog() override { return "%f$time"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_TIME; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstTimeD final : public AstNodeTermop {
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTimeD(FileLine* fl, const VTimescale& timeunit)
        : ASTGEN_SUPER_TimeD(fl)
        , m_timeunit{timeunit} {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstTimeD;
    string emitVerilog() override { return "%f$realtime"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_TIME; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

// === AstNodeTriop ===
class AstPostAdd final : public AstNodeTriop {
    // Post-increment/add
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostAdd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_PostAdd(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstPostAdd;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    string emitVerilog() override { return "%k(%r++)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    bool sizeMattersThs() const override { return true; }
};
class AstPostSub final : public AstNodeTriop {
    // Post-decrement/subtract
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostSub(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_PostSub(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstPostSub;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    string emitVerilog() override { return "%k(%r--)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    bool sizeMattersThs() const override { return true; }
};
class AstPreAdd final : public AstNodeTriop {
    // Pre-increment/add
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreAdd(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_PreAdd(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstPreAdd;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    string emitVerilog() override { return "%k(++%r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    bool sizeMattersThs() const override { return true; }
};
class AstPreSub final : public AstNodeTriop {
    // Pre-decrement/subtract
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreSub(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_PreSub(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstPreSub;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    string emitVerilog() override { return "%k(--%r)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return false; }
    bool cleanThs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
    bool sizeMattersRhs() const override { return true; }
    bool sizeMattersThs() const override { return true; }
};
class AstPutcN final : public AstNodeTriop {
    // Verilog string.putc()
public:
    AstPutcN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* ths)
        : ASTGEN_SUPER_PutcN(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstPutcN;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        out.opPutcN(lhs, rhs, ths);
    }
    string name() const override VL_MT_STABLE { return "putc"; }
    string emitVerilog() override { return "%k(%l.putc(%r,%t))"; }
    string emitC() override { return "VL_PUTC_N(%li,%ri,%ti)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool cleanThs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
};
class AstSel final : public AstNodeTriop {
    // Multiple bit range extraction
    // @astgen alias op1 := fromp
    // @astgen alias op2 := lsbp
    // @astgen alias op3 := widthp
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
    int m_declElWidth;  // If a packed array, the number of bits per element
public:
    AstSel(FileLine* fl, AstNodeExpr* fromp, AstNodeExpr* lsbp, AstNodeExpr* widthp)
        : ASTGEN_SUPER_Sel(fl, fromp, lsbp, widthp)
        , m_declElWidth{1} {
        if (VN_IS(widthp, Const)) {
            dtypeSetLogicSized(VN_AS(widthp, Const)->toUInt(), VSigning::UNSIGNED);
        }
    }
    AstSel(FileLine* fl, AstNodeExpr* fromp, int lsb, int bitwidth)
        : ASTGEN_SUPER_Sel(fl, fromp, new AstConst(fl, lsb),  // Need () constructor
                           new AstConst(fl, bitwidth))  // Need () constructor
        , m_declElWidth{1} {
        dtypeSetLogicSized(bitwidth, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstSel;
    void dump(std::ostream& str) const override;
    void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit,
                       const V3Number& width) override {
        out.opSel(from, bit.toUInt() + width.toUInt() - 1, bit.toUInt());
    }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override {
        return widthp()->isOne() ? "VL_BITSEL_%nq%lq%rq%tq(%lw, %P, %li, %ri)"
               : isWide()        ? "VL_SEL_%nq%lq%rq%tq(%nw,%lw, %P, %li, %ri, %ti)"
                                 : "VL_SEL_%nq%lq%rq%tq(%lw, %P, %li, %ri, %ti)";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool cleanThs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
    bool same(const AstNode*) const override { return true; }
    int instrCount() const override { return widthInstrs() * (VN_CAST(lsbp(), Const) ? 3 : 10); }
    int widthConst() const { return VN_AS(widthp(), Const)->toSInt(); }
    int lsbConst() const { return VN_AS(lsbp(), Const)->toSInt(); }
    int msbConst() const { return lsbConst() + widthConst() - 1; }
    VNumRange& declRange() { return m_declRange; }
    const VNumRange& declRange() const { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
    int declElWidth() const { return m_declElWidth; }
    void declElWidth(int flag) { m_declElWidth = flag; }
};
class AstSliceSel final : public AstNodeTriop {
    // Multiple array element extraction
    // @astgen alias op1 := fromp
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
public:
    AstSliceSel(FileLine* fl, AstNodeExpr* fromp, const VNumRange& declRange)
        : ASTGEN_SUPER_SliceSel(fl, fromp,
                                new AstConst(fl, declRange.lo()),  // Need () constructor
                                new AstConst(fl, declRange.elements()))  // Need () constructor
        , m_declRange{declRange} {}
    ASTGEN_MEMBERS_AstSliceSel;
    void dump(std::ostream& str) const override;
    void numberOperate(V3Number& out, const V3Number& from, const V3Number& lo,
                       const V3Number& width) override {
        V3ERROR_NA;
    }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }  // Removed before EmitC
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool cleanRhs() const override { return true; }
    bool cleanThs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
    bool same(const AstNode*) const override { return true; }
    int instrCount() const override { return 10; }  // Removed before matters
    // For widthConst()/loConst etc, see declRange().elements() and other VNumRange methods
    VNumRange& declRange() { return m_declRange; }
    const VNumRange& declRange() const { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
};
class AstSubstrN final : public AstNodeTriop {
    // Verilog string.substr()
public:
    AstSubstrN(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* ths)
        : ASTGEN_SUPER_SubstrN(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstSubstrN;
    void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                       const V3Number& ths) override {
        out.opSubstrN(lhs, rhs, ths);
    }
    string name() const override VL_MT_STABLE { return "substr"; }
    string emitVerilog() override { return "%k(%l.substr(%r,%t))"; }
    string emitC() override { return "VL_SUBSTR_N(%li,%ri,%ti)"; }
    string emitSimpleOperator() override { return ""; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool cleanRhs() const override { return true; }
    bool cleanThs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool sizeMattersRhs() const override { return false; }
    bool sizeMattersThs() const override { return false; }
};

// === AstNodeCond ===
class AstCond final : public AstNodeCond {
    // Conditional ?: expression
public:
    AstCond(FileLine* fl, AstNodeExpr* condp, AstNodeExpr* thenp, AstNodeExpr* elsep)
        : ASTGEN_SUPER_Cond(fl, condp, thenp, elsep) {}
    ASTGEN_MEMBERS_AstCond;
    AstNodeExpr* cloneType(AstNodeExpr* condp, AstNodeExpr* thenp, AstNodeExpr* elsep) override {
        return new AstCond{fileline(), condp, thenp, elsep};
    }
};
class AstCondBound final : public AstNodeCond {
    // Conditional ?: expression, specially made for safety checking of array bounds
public:
    AstCondBound(FileLine* fl, AstNodeExpr* condp, AstNodeExpr* thenp, AstNodeExpr* elsep)
        : ASTGEN_SUPER_CondBound(fl, condp, thenp, elsep) {}
    ASTGEN_MEMBERS_AstCondBound;
    AstNodeExpr* cloneType(AstNodeExpr* condp, AstNodeExpr* thenp, AstNodeExpr* elsep) override {
        return new AstCondBound{fileline(), condp, thenp, elsep};
    }
};

// === AstNodeDistTriop ===
class AstDistErlang final : public AstNodeDistTriop {
public:
    AstDistErlang(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_DistErlang(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstDistErlang;
    string emitVerilog() override { return "%f$dist_erlang(%l, %r, %t)"; }
    string emitC() override { return "VL_DIST_ERLANG(%li, %ri, %ti)"; }
};
class AstDistNormal final : public AstNodeDistTriop {
public:
    AstDistNormal(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_DistNormal(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstDistNormal;
    string emitVerilog() override { return "%f$dist_normal(%l, %r, %t)"; }
    string emitC() override { return "VL_DIST_NORMAL(%li, %ri, %ti)"; }
};
class AstDistUniform final : public AstNodeDistTriop {
public:
    AstDistUniform(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp, AstNodeExpr* thsp)
        : ASTGEN_SUPER_DistUniform(fl, lhsp, rhsp, thsp) {}
    ASTGEN_MEMBERS_AstDistUniform;
    string emitVerilog() override { return "%f$dist_uniform(%l, %r, %t)"; }
    string emitC() override { return "VL_DIST_UNIFORM(%li, %ri, %ti)"; }
};

// === AstNodeUniop ===
class AstAtoN final : public AstNodeUniop {
    // string.atoi(), atobin(), atohex(), atooct(), atoireal()
public:
    enum FmtType { ATOI = 10, ATOHEX = 16, ATOOCT = 8, ATOBIN = 2, ATOREAL = -1 };

private:
    const FmtType m_fmt;  // Operation type
public:
    AstAtoN(FileLine* fl, AstNodeExpr* lhsp, FmtType fmt)
        : ASTGEN_SUPER_AtoN(fl, lhsp)
        , m_fmt{fmt} {
        fmt == ATOREAL ? dtypeSetDouble() : dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstAtoN;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAtoN(lhs, m_fmt); }
    string name() const override VL_MT_STABLE {
        switch (m_fmt) {
        case ATOI: return "atoi";
        case ATOHEX: return "atohex";
        case ATOOCT: return "atooct";
        case ATOBIN: return "atobin";
        case ATOREAL: return "atoreal";
        }
        V3ERROR_NA_RETURN("");
    }
    string emitVerilog() override { return "%l." + name() + "()"; }
    string emitC() override {
        switch (m_fmt) {
        case ATOI: return "VL_ATOI_N(%li, 10)";
        case ATOHEX: return "VL_ATOI_N(%li, 16)";
        case ATOOCT: return "VL_ATOI_N(%li, 8)";
        case ATOBIN: return "VL_ATOI_N(%li, 2)";
        case ATOREAL: return "std::atof(%li.c_str())";
        }
        V3ERROR_NA_RETURN("");
    }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    FmtType format() const { return m_fmt; }
};
class AstBitsToRealD final : public AstNodeUniop {
public:
    AstBitsToRealD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_BitsToRealD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstBitsToRealD;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opBitsToRealD(lhs); }
    string emitVerilog() override { return "%f$bitstoreal(%l)"; }
    string emitC() override { return "VL_CVT_D_Q(%li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }  // Eliminated before matters
    bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstCAwait final : public AstNodeUniop {
    // Emit C++'s co_await expression
    // @astgen alias op1 := exprp
    AstSenTree* m_sensesp;  // Sentree related to this await
public:
    AstCAwait(FileLine* fl, AstNodeExpr* exprp, AstSenTree* sensesp = nullptr)
        : ASTGEN_SUPER_CAwait(fl, exprp)
        , m_sensesp{sensesp} {}
    ASTGEN_MEMBERS_AstCAwait;
    bool isTimingControl() const override { return true; }
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    AstSenTree* sensesp() const { return m_sensesp; }
    void clearSensesp() { m_sensesp = nullptr; }
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstCCast final : public AstNodeUniop {
    // Cast to C-based data type
    int m_size;

public:
    AstCCast(FileLine* fl, AstNodeExpr* lhsp, int setwidth, int minwidth = -1)
        : ASTGEN_SUPER_CCast(fl, lhsp) {
        m_size = setwidth;
        if (setwidth) {
            if (minwidth == -1) minwidth = setwidth;
            dtypeSetLogicUnsized(setwidth, minwidth, VSigning::UNSIGNED);
        }
    }
    AstCCast(FileLine* fl, AstNodeExpr* lhsp, AstNode* typeFromp)
        : ASTGEN_SUPER_CCast(fl, lhsp) {
        dtypeFrom(typeFromp);
        m_size = width();
    }
    ASTGEN_MEMBERS_AstCCast;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    string emitVerilog() override { return "%f$_CAST(%l)"; }
    string emitC() override { return "VL_CAST_%nq%lq(%nw,%lw, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }  // Special cased in V3Cast
    bool same(const AstNode* samep) const override {
        return size() == static_cast<const AstCCast*>(samep)->size();
    }
    void dump(std::ostream& str = std::cout) const override;
    //
    int size() const { return m_size; }
};
class AstCLog2 final : public AstNodeUniop {
public:
    AstCLog2(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CLog2(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstCLog2;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opCLog2(lhs); }
    string emitVerilog() override { return "%f$clog2(%l)"; }
    string emitC() override { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 16; }
};
class AstCastWrap final : public AstNodeUniop {
    // A cast which has been expanded and the LHSP does all the lifting
    // This remains until V3Width final commit pass to suppress ENUMVALUE warnings
public:
    AstCastWrap(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CastWrap(fl, lhsp) {}
    ASTGEN_MEMBERS_AstCastWrap;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    string emitVerilog() override { return "(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return 0; }
};
class AstCountOnes final : public AstNodeUniop {
    // Number of bits set in vector
public:
    AstCountOnes(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CountOnes(fl, lhsp) {}
    ASTGEN_MEMBERS_AstCountOnes;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opCountOnes(lhs); }
    string emitVerilog() override { return "%f$countones(%l)"; }
    string emitC() override { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 16; }
};
class AstCvtPackString final : public AstNodeUniop {
    // Convert to Verilator Packed String (aka verilog "string")
public:
    AstCvtPackString(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CvtPackString(fl, lhsp) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstCvtPackString;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    string emitVerilog() override { return "%f$_CAST(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstExtend final : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
public:
    AstExtend(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Extend(fl, lhsp) {}
    AstExtend(FileLine* fl, AstNodeExpr* lhsp, int width)
        : ASTGEN_SUPER_Extend(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstExtend;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    string emitVerilog() override { return "%l"; }
    string emitC() override { return "VL_EXTEND_%nq%lq(%nw,%lw, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    int instrCount() const override { return 0; }
};
class AstExtendS final : public AstNodeUniop {
    // Expand a value into a wider entity by sign extension.  Width is implied from nodep->width()
public:
    AstExtendS(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ExtendS(fl, lhsp) {}
    AstExtendS(FileLine* fl, AstNodeExpr* lhsp, int width)
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        : ASTGEN_SUPER_ExtendS(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTGEN_MEMBERS_AstExtendS;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opExtendS(lhs, lhsp()->widthMinV());
    }
    string emitVerilog() override { return "%l"; }
    string emitC() override { return "VL_EXTENDS_%nq%lq(%nw,%lw, %P, %li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    int instrCount() const override { return 0; }
    bool signedFlavor() const override { return true; }
};
class AstFEof final : public AstNodeUniop {
public:
    AstFEof(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_FEof(fl, lhsp) {}
    ASTGEN_MEMBERS_AstFEof;
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    string emitVerilog() override { return "%f$feof(%l)"; }
    string emitC() override { return "(%li ? feof(VL_CVT_I_FP(%li)) : true)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 16; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};
class AstFGetC final : public AstNodeUniop {
public:
    AstFGetC(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_FGetC(fl, lhsp) {}
    ASTGEN_MEMBERS_AstFGetC;
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    string emitVerilog() override { return "%f$fgetc(%l)"; }
    // Non-existent filehandle returns EOF
    string emitC() override { return "(%li ? fgetc(VL_CVT_I_FP(%li)) : -1)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 64; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};
class AstISToRD final : public AstNodeUniop {
    // $itor where lhs is signed
public:
    AstISToRD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ISToRD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstISToRD;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opISToRD(lhs); }
    string emitVerilog() override { return "%f$itor($signed(%l))"; }
    string emitC() override { return "VL_ISTOR_D_%lq(%lw, %li)"; }
    bool emitCheckMaxWords() override { return true; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstIToRD final : public AstNodeUniop {
    // $itor where lhs is unsigned
public:
    AstIToRD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_IToRD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstIToRD;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opIToRD(lhs); }
    string emitVerilog() override { return "%f$itor(%l)"; }
    string emitC() override { return "VL_ITOR_D_%lq(%lw, %li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstIsUnbounded final : public AstNodeUniop {
    // True if is unbounded ($)
public:
    AstIsUnbounded(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_IsUnbounded(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstIsUnbounded;
    void numberOperate(V3Number& out, const V3Number&) override {
        // Any constant isn't unbounded
        out.setZero();
    }
    string emitVerilog() override { return "%f$isunbounded(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
};
class AstIsUnknown final : public AstNodeUniop {
    // True if any unknown bits
public:
    AstIsUnknown(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_IsUnknown(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstIsUnknown;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opIsUnknown(lhs); }
    string emitVerilog() override { return "%f$isunknown(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
};
class AstLenN final : public AstNodeUniop {
    // Length of a string
public:
    AstLenN(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_LenN(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstLenN;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLenN(lhs); }
    string emitVerilog() override { return "%f(%l)"; }
    string emitC() override { return "VL_LEN_IN(%li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstLogNot final : public AstNodeUniop {
public:
    AstLogNot(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_LogNot(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstLogNot;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLogNot(lhs); }
    string emitVerilog() override { return "%f(! %l)"; }
    string emitC() override { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    string emitSimpleOperator() override { return "!"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstNToI final : public AstNodeUniop {
    // String to any-size integral
public:
    AstNToI(FileLine* fl, AstNodeExpr* lhsp, AstNodeDType* dtypep = nullptr)
        : ASTGEN_SUPER_NToI(fl, lhsp) {
        this->dtypep(dtypep);
    }
    ASTGEN_MEMBERS_AstNToI;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNToI(lhs); }
    string emitVerilog() override { return "'(%l)"; }
    string emitC() override { return "VL_NTOI_%nq(%nw, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstNegate final : public AstNodeUniop {
public:
    AstNegate(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Negate(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstNegate;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegate(lhs); }
    string emitVerilog() override { return "%f(- %l)"; }
    string emitC() override { return "VL_NEGATE_%lq(%lW, %P, %li)"; }
    string emitSimpleOperator() override { return "-"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
};
class AstNegateD final : public AstNodeUniop {
public:
    AstNegateD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_NegateD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTGEN_MEMBERS_AstNegateD;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegateD(lhs); }
    string emitVerilog() override { return "%f(- %l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { return "-"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
    bool doubleFlavor() const override { return true; }
};
class AstNot final : public AstNodeUniop {
public:
    AstNot(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Not(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstNot;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNot(lhs); }
    string emitVerilog() override { return "%f(~ %l)"; }
    string emitC() override { return "VL_NOT_%lq(%lW, %P, %li)"; }
    string emitSimpleOperator() override { return "~"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return true; }
};
class AstNullCheck final : public AstNodeUniop {
    // Return LHS after checking that LHS is non-null
public:
    AstNullCheck(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_NullCheck(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstNullCheck;
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    int instrCount() const override { return 1; }  // Rarely executes
    string emitVerilog() override { return "%l"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    bool same(const AstNode* samep) const override { return fileline() == samep->fileline(); }
};
class AstOneHot final : public AstNodeUniop {
    // True if only single bit set in vector
public:
    AstOneHot(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_OneHot(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstOneHot;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot(lhs); }
    string emitVerilog() override { return "%f$onehot(%l)"; }
    string emitC() override { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 4; }
};
class AstOneHot0 final : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
public:
    AstOneHot0(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_OneHot0(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstOneHot0;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot0(lhs); }
    string emitVerilog() override { return "%f$onehot0(%l)"; }
    string emitC() override { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return widthInstrs() * 3; }
};
class AstRToIRoundS final : public AstNodeUniop {
    // Convert real to integer, with arbitrary sized output (not just "integer" format)
public:
    AstRToIRoundS(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RToIRoundS(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstRToIRoundS;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRToIRoundS(lhs); }
    string emitVerilog() override { return "%f$rtoi_rounded(%l)"; }
    string emitC() override {
        return isWide() ? "VL_RTOIROUND_%nq_D(%nw, %P, %li)" : "VL_RTOIROUND_%nq_D(%li)";
    }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRToIS final : public AstNodeUniop {
    // $rtoi(lhs)
public:
    AstRToIS(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RToIS(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTGEN_MEMBERS_AstRToIS;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRToIS(lhs); }
    string emitVerilog() override { return "%f$rtoi(%l)"; }
    string emitC() override { return "VL_RTOI_I_D(%li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }  // Eliminated before matters
    bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRealToBits final : public AstNodeUniop {
public:
    AstRealToBits(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RealToBits(fl, lhsp) {
        dtypeSetUInt64();
    }
    ASTGEN_MEMBERS_AstRealToBits;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRealToBits(lhs); }
    string emitVerilog() override { return "%f$realtobits(%l)"; }
    string emitC() override { return "VL_CVT_Q_D(%li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }  // Eliminated before matters
    bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRedAnd final : public AstNodeUniop {
public:
    AstRedAnd(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RedAnd(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstRedAnd;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedAnd(lhs); }
    string emitVerilog() override { return "%f(& %l)"; }
    string emitC() override { return "VL_REDAND_%nq%lq(%lw, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstRedOr final : public AstNodeUniop {
public:
    AstRedOr(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RedOr(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstRedOr;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedOr(lhs); }
    string emitVerilog() override { return "%f(| %l)"; }
    string emitC() override { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstRedXor final : public AstNodeUniop {
public:
    AstRedXor(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_RedXor(fl, lhsp) {
        dtypeSetBit();
    }
    ASTGEN_MEMBERS_AstRedXor;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedXor(lhs); }
    string emitVerilog() override { return "%f(^ %l)"; }
    string emitC() override { return "VL_REDXOR_%lq(%lW, %P, %li)"; }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override {
        const int w = lhsp()->width();
        return (w != 1 && w != 2 && w != 4 && w != 8 && w != 16);
    }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return 1 + V3Number::log2b(width()); }
};
class AstResizeLValue final : public AstNodeUniop {
    // Resize a LValue into a wider/narrower entity at function argument boundry
    // Width and signness is implied from nodep->width()
public:
    AstResizeLValue(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ResizeLValue(fl, lhsp) {}
    ASTGEN_MEMBERS_AstResizeLValue;
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    string emitVerilog() override { return "%l"; }
    string emitC() final override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
    int instrCount() const override { return 0; }
};
class AstSigned final : public AstNodeUniop {
    // $signed(lhs)
public:
    AstSigned(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Signed(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTGEN_MEMBERS_AstSigned;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    string emitVerilog() override { return "%f$signed(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }  // Eliminated before matters
    bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    int instrCount() const override { return 0; }
};
class AstTimeImport final : public AstNodeUniop {
    // Take a constant that represents a time and needs conversion based on time units
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTimeImport(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_TimeImport(fl, lhsp) {}
    ASTGEN_MEMBERS_AstTimeImport;
    void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    string emitVerilog() override { return "%l"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }
    bool sizeMattersLhs() const override { return false; }
    void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstToLowerN final : public AstNodeUniop {
    // string.tolower()
public:
    AstToLowerN(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ToLowerN(fl, lhsp) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstToLowerN;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opToLowerN(lhs); }
    string emitVerilog() override { return "%l.tolower()"; }
    string emitC() override { return "VL_TOLOWER_NN(%li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstToUpperN final : public AstNodeUniop {
    // string.toupper()
public:
    AstToUpperN(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ToUpperN(fl, lhsp) {
        dtypeSetString();
    }
    ASTGEN_MEMBERS_AstToUpperN;
    void numberOperate(V3Number& out, const V3Number& lhs) override { out.opToUpperN(lhs); }
    string emitVerilog() override { return "%l.toupper()"; }
    string emitC() override { return "VL_TOUPPER_NN(%li)"; }
    bool cleanOut() const override { return true; }
    bool cleanLhs() const override { return true; }
    bool sizeMattersLhs() const override { return false; }
};
class AstUnsigned final : public AstNodeUniop {
    // $unsigned(lhs)
public:
    AstUnsigned(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Unsigned(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTGEN_MEMBERS_AstUnsigned;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    string emitVerilog() override { return "%f$unsigned(%l)"; }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return false; }
    bool cleanLhs() const override { return false; }  // Eliminated before matters
    bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    int instrCount() const override { return 0; }
};

// === AstNodeSystemUniopD ===
class AstAcosD final : public AstNodeSystemUniopD {
public:
    AstAcosD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AcosD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAcosD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acos(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$acos(%l)"; }
    string emitC() override { return "acos(%li)"; }
};
class AstAcoshD final : public AstNodeSystemUniopD {
public:
    AstAcoshD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AcoshD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAcoshD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acosh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$acosh(%l)"; }
    string emitC() override { return "acosh(%li)"; }
};
class AstAsinD final : public AstNodeSystemUniopD {
public:
    AstAsinD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AsinD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAsinD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asin(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$asin(%l)"; }
    string emitC() override { return "asin(%li)"; }
};
class AstAsinhD final : public AstNodeSystemUniopD {
public:
    AstAsinhD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AsinhD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAsinhD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asinh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$asinh(%l)"; }
    string emitC() override { return "asinh(%li)"; }
};
class AstAtanD final : public AstNodeSystemUniopD {
public:
    AstAtanD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AtanD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAtanD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atan(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$atan(%l)"; }
    string emitC() override { return "atan(%li)"; }
};
class AstAtanhD final : public AstNodeSystemUniopD {
public:
    AstAtanhD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_AtanhD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstAtanhD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atanh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$atanh(%l)"; }
    string emitC() override { return "atanh(%li)"; }
};
class AstCeilD final : public AstNodeSystemUniopD {
public:
    AstCeilD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CeilD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstCeilD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::ceil(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$ceil(%l)"; }
    string emitC() override { return "ceil(%li)"; }
};
class AstCosD final : public AstNodeSystemUniopD {
public:
    AstCosD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CosD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstCosD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cos(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$cos(%l)"; }
    string emitC() override { return "cos(%li)"; }
};
class AstCoshD final : public AstNodeSystemUniopD {
public:
    AstCoshD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CoshD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstCoshD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cosh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$cosh(%l)"; }
    string emitC() override { return "cosh(%li)"; }
};
class AstExpD final : public AstNodeSystemUniopD {
public:
    AstExpD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_ExpD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstExpD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::exp(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$exp(%l)"; }
    string emitC() override { return "exp(%li)"; }
};
class AstFloorD final : public AstNodeSystemUniopD {
public:
    AstFloorD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_FloorD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstFloorD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::floor(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$floor(%l)"; }
    string emitC() override { return "floor(%li)"; }
};
class AstLog10D final : public AstNodeSystemUniopD {
public:
    AstLog10D(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Log10D(fl, lhsp) {}
    ASTGEN_MEMBERS_AstLog10D;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log10(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$log10(%l)"; }
    string emitC() override { return "log10(%li)"; }
};
class AstLogD final : public AstNodeSystemUniopD {
public:
    AstLogD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_LogD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstLogD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$ln(%l)"; }
    string emitC() override { return "log(%li)"; }
};
class AstSinD final : public AstNodeSystemUniopD {
public:
    AstSinD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_SinD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstSinD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sin(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$sin(%l)"; }
    string emitC() override { return "sin(%li)"; }
};
class AstSinhD final : public AstNodeSystemUniopD {
public:
    AstSinhD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_SinhD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstSinhD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sinh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$sinh(%l)"; }
    string emitC() override { return "sinh(%li)"; }
};
class AstSqrtD final : public AstNodeSystemUniopD {
public:
    AstSqrtD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_SqrtD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstSqrtD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sqrt(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$sqrt(%l)"; }
    string emitC() override { return "sqrt(%li)"; }
};
class AstTanD final : public AstNodeSystemUniopD {
public:
    AstTanD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_TanD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstTanD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tan(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$tan(%l)"; }
    string emitC() override { return "tan(%li)"; }
};
class AstTanhD final : public AstNodeSystemUniopD {
public:
    AstTanhD(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_TanhD(fl, lhsp) {}
    ASTGEN_MEMBERS_AstTanhD;
    void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tanh(lhs.toDouble()));
    }
    string emitVerilog() override { return "%f$tanh(%l)"; }
    string emitC() override { return "tanh(%li)"; }
};

// === AstNodeVarRef ===
class AstVarRef final : public AstNodeVarRef {
    // A reference to a variable (lvalue or rvalue)
public:
    // This form only allowed post-link because output/wire compression may
    // lead to deletion of AstVar's
    inline AstVarRef(FileLine* fl, AstVar* varp, const VAccess& access);
    // This form only allowed post-link (see above)
    inline AstVarRef(FileLine* fl, AstVarScope* varscp, const VAccess& access);
    ASTGEN_MEMBERS_AstVarRef;
    inline string name() const override;  // * = Var name
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    bool same(const AstNode* samep) const override;
    inline bool same(const AstVarRef* samep) const;
    inline bool sameNoLvalue(AstVarRef* samep) const;
    int instrCount() const override;
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
};
class AstVarXRef final : public AstNodeVarRef {
    // A VarRef to something in another module before AstScope.
    // Includes pin on a cell, as part of a ASSIGN statement to connect I/Os until AstScope
    string m_name;
    string m_dotted;  // Dotted part of scope the name()'ed reference is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
public:
    AstVarXRef(FileLine* fl, const string& name, const string& dotted, const VAccess& access)
        : ASTGEN_SUPER_VarXRef(fl, nullptr, access)
        , m_name{name}
        , m_dotted{dotted} {}
    inline AstVarXRef(FileLine* fl, AstVar* varp, const string& dotted, const VAccess& access);
    ASTGEN_MEMBERS_AstVarXRef;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    void dump(std::ostream& str) const override;
    string dotted() const { return m_dotted; }
    void dotted(const string& dotted) { m_dotted = dotted; }
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    string emitC() override { V3ERROR_NA_RETURN(""); }
    bool cleanOut() const override { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode* samep) const override {
        const AstVarXRef* asamep = static_cast<const AstVarXRef*>(samep);
        return (selfPointer() == asamep->selfPointer() && varp() == asamep->varp()
                && name() == asamep->name() && dotted() == asamep->dotted());
    }
};

#endif  // Guard
