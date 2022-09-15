// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing expressions
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
//
// This files contains all 'AstNode' sub-types that representing expressions,
// i.e.: those constructs that evaluate to [a possible void/unit] value.  The
// root of the hierarchy is 'AstNodeMath', which could also be called
// 'AstNodeExpr'.
//
// Warning: Although the above is what we are aiming for, currently there are
// some 'AstNode' sub-types defined elsewhere, that represent expressions but
// are not part of the `AstNodeMath` hierarchy (e.g.: 'AstNodeCall' and its
// sub-types). These should eventually be fixed and moved under 'AstNodeMath'.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODEMATH_H_
#define VERILATOR_V3ASTNODEMATH_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeMath VL_NOT_FINAL : public AstNode {
    // Math -- anything that's part of an expression tree
protected:
    AstNodeMath(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeMath)
    // METHODS
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual string emitVerilog() = 0;  /// Format string for verilog writing; see V3EmitV
    // For documentation on emitC format see EmitCFunc::emitOpName
    virtual string emitC() = 0;
    virtual string emitSimpleOperator() { return ""; }  // "" means not ok to use
    virtual bool emitCheckMaxWords() { return false; }  // Check VL_MULS_MAX_WORDS
    virtual bool cleanOut() const = 0;  // True if output has extra upper bits zero
    // Someday we will generically support data types on every math node
    // Until then isOpaque indicates we shouldn't constant optimize this node type
    bool isOpaque() const { return VN_IS(this, CvtPackString); }
};
class AstNodeBiop VL_NOT_FINAL : public AstNodeMath {
    // Binary math
protected:
    AstNodeBiop(VNType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
    }

public:
    ASTNODE_BASE_FUNCS(NodeBiop)
    // Clone single node, just get same type back.
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;
    // ACCESSORS
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
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
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};
class AstNodeBiCom VL_NOT_FINAL : public AstNodeBiop {
    // Binary math with commutative properties
protected:
    AstNodeBiCom(VNType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiop{t, fl, lhs, rhs} {}

public:
    ASTNODE_BASE_FUNCS(NodeBiCom)
};
class AstNodeBiComAsv VL_NOT_FINAL : public AstNodeBiCom {
    // Binary math with commutative & associative properties
protected:
    AstNodeBiComAsv(VNType t, FileLine* fl, AstNode* lhs, AstNode* rhs)
        : AstNodeBiCom{t, fl, lhs, rhs} {}

public:
    ASTNODE_BASE_FUNCS(NodeBiComAsv)
};
class AstNodeSel VL_NOT_FINAL : public AstNodeBiop {
    // Single bit range extraction, perhaps with non-constant selection or array selection
protected:
    AstNodeSel(VNType t, FileLine* fl, AstNode* fromp, AstNode* bitp)
        : AstNodeBiop{t, fl, fromp, bitp} {}

public:
    ASTNODE_BASE_FUNCS(NodeSel)
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* bitp() const { return op2p(); }  // op2 = Msb selection expression
    void bitp(AstNode* nodep) { setOp2p(nodep); }
    int bitConst() const;
    virtual bool hasDType() const override { return true; }
};
class AstNodeStream VL_NOT_FINAL : public AstNodeBiop {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
protected:
    AstNodeStream(VNType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop{t, fl, lhsp, rhsp} {
        if (lhsp->dtypep()) dtypeSetLogicSized(lhsp->dtypep()->width(), VSigning::UNSIGNED);
    }

public:
    ASTNODE_BASE_FUNCS(NodeStream)
};
class AstNodeSystemBiop VL_NOT_FINAL : public AstNodeBiop {
public:
    AstNodeSystemBiop(VNType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : AstNodeBiop(t, fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstNodeQuadop VL_NOT_FINAL : public AstNodeMath {
    // Quaternary math
protected:
    AstNodeQuadop(VNType t, FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths, AstNode* fhs)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
        setOp3p(ths);
        setOp4p(fhs);
    }

public:
    ASTNODE_BASE_FUNCS(NodeQuadop)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    AstNode* fhsp() const { return op4p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    void fhsp(AstNode* nodep) { return setOp4p(nodep); }
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
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};
class AstNodeTermop VL_NOT_FINAL : public AstNodeMath {
    // Terminal operator -- a operator with no "inputs"
protected:
    AstNodeTermop(VNType t, FileLine* fl)
        : AstNodeMath{t, fl} {}

public:
    ASTNODE_BASE_FUNCS(NodeTermop)
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(VNVisitor& v) {}
    virtual void dump(std::ostream& str) const override;
};
class AstNodeTriop VL_NOT_FINAL : public AstNodeMath {
    // Trinary math
protected:
    AstNodeTriop(VNType t, FileLine* fl, AstNode* lhs, AstNode* rhs, AstNode* ths)
        : AstNodeMath{t, fl} {
        setOp1p(lhs);
        setOp2p(rhs);
        setOp3p(ths);
    }

public:
    ASTNODE_BASE_FUNCS(NodeTriop)
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    // METHODS
    virtual void dump(std::ostream& str) const override;
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
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};
class AstNodeCond VL_NOT_FINAL : public AstNodeTriop {
protected:
    AstNodeCond(VNType t, FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : AstNodeTriop{t, fl, condp, expr1p, expr2p} {
        if (expr1p) {
            dtypeFrom(expr1p);
        } else if (expr2p) {
            dtypeFrom(expr2p);
        }
    }

public:
    ASTNODE_BASE_FUNCS(NodeCond)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override;
    AstNode* condp() const { return op1p(); }  // op1 = Condition
    AstNode* expr1p() const { return op2p(); }  // op2 = If true...
    AstNode* expr2p() const { return op3p(); }  // op3 = If false...
    virtual string emitVerilog() override { return "%k(%l %f? %r %k: %t)"; }
    virtual string emitC() override { return "VL_COND_%nq%lq%rq%tq(%nw, %P, %li, %ri, %ti)"; }
    virtual bool cleanOut() const override { return false; }  // clean if e1 & e2 clean
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }  // Propagates up
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) = 0;
};
class AstNodeUniop VL_NOT_FINAL : public AstNodeMath {
    // Unary math
protected:
    AstNodeUniop(VNType t, FileLine* fl, AstNode* lhsp)
        : AstNodeMath{t, fl} {
        dtypeFrom(lhsp);
        setOp1p(lhsp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeUniop)
    AstNode* lhsp() const { return op1p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    // METHODS
    virtual void dump(std::ostream& str) const override;
    // Set out to evaluation of a AstConst'ed lhs
    virtual void numberOperate(V3Number& out, const V3Number& lhs) = 0;
    virtual bool cleanLhs() const = 0;
    virtual bool sizeMattersLhs() const = 0;  // True if output result depends on lhs size
    virtual bool doubleFlavor() const { return false; }  // D flavor of nodes with both flavors?
    // Signed flavor of nodes with both flavors?
    virtual bool signedFlavor() const { return false; }
    virtual bool stringFlavor() const { return false; }  // N flavor of nodes with both flavors?
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
};
class AstNodeSystemUniop VL_NOT_FINAL : public AstNodeUniop {
public:
    AstNodeSystemUniop(VNType t, FileLine* fl, AstNode* lhsp)
        : AstNodeUniop(t, fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_BASE_FUNCS(NodeSystemUniop)
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL_TRIG; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstNodeVarRef VL_NOT_FINAL : public AstNodeMath {
    // An AstVarRef or AstVarXRef
private:
    VAccess m_access;  // Left hand side assignment
    AstVar* m_varp;  // [AfterLink] Pointer to variable itself
    AstVarScope* m_varScopep = nullptr;  // Varscope for hierarchy
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
    string m_name;  // Name of variable
    string m_selfPointer;  // Output code object pointer (e.g.: 'this')

protected:
    AstNodeVarRef(VNType t, FileLine* fl, const string& name, const VAccess& access)
        : AstNodeMath{t, fl}
        , m_access{access}
        , m_name{name} {
        varp(nullptr);
    }
    AstNodeVarRef(VNType t, FileLine* fl, const string& name, AstVar* varp, const VAccess& access)
        : AstNodeMath{t, fl}
        , m_access{access}
        , m_name{name} {
        // May have varp==nullptr
        this->varp(varp);
    }

public:
    ASTNODE_BASE_FUNCS(NodeVarRef)
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    virtual const char* broken() const override;
    virtual int instrCount() const override { return widthInstrs(); }
    virtual void cloneRelink() override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void name(const string& name) override { m_name = name; }
    VAccess access() const { return m_access; }
    void access(const VAccess& flag) { m_access = flag; }  // Avoid using this; Set in constructor
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp);
    AstVarScope* varScopep() const { return m_varScopep; }
    void varScopep(AstVarScope* varscp) { m_varScopep = varscp; }
    string selfPointer() const { return m_selfPointer; }
    void selfPointer(const string& value) { m_selfPointer = value; }
    string selfPointerProtect(bool useSelfForThis) const;
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    // Know no children, and hot function, so skip iterator for speed
    // See checkTreeIter also that asserts no children
    // cppcheck-suppress functionConst
    void iterateChildren(VNVisitor& v) {}
};

// === Concrete node types =====================================================

// === AstNodeMath ===
class AstAddrOfCFunc final : public AstNodeMath {
    // Get address of CFunc
private:
    AstCFunc* m_funcp;  // Pointer to function itself

public:
    AstAddrOfCFunc(FileLine* fl, AstCFunc* funcp)
        : ASTGEN_SUPER_AddrOfCFunc(fl)
        , m_funcp{funcp} {
        dtypep(findCHandleDType());
    }

public:
    ASTNODE_NODE_FUNCS(AddrOfCFunc)
    virtual void cloneRelink() override;
    virtual const char* broken() const override;
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstCFunc* funcp() const { return m_funcp; }
};
class AstCMath final : public AstNodeMath {
private:
    const bool m_cleanOut;
    bool m_pure;  // Pure optimizable
public:
    // Emit C textual math function (like AstUCFunc)
    AstCMath(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_CMath(fl)
        , m_cleanOut{true}
        , m_pure{false} {
        addOp1p(exprsp);
        dtypeFrom(exprsp);
    }
    inline AstCMath(FileLine* fl, const string& textStmt, int setwidth, bool cleanOut = true);
    ASTNODE_NODE_FUNCS(CMath)
    virtual bool isGateOptimizable() const override { return m_pure; }
    virtual bool isPredictOptimizable() const override { return m_pure; }
    virtual bool cleanOut() const override { return m_cleanOut; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    bool pure() const { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
};
class AstConsAssoc final : public AstNodeMath {
    // Construct an assoc array and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstConsAssoc(FileLine* fl, AstNode* defaultp)
        : ASTGEN_SUPER_ConsAssoc(fl) {
        setNOp1p(defaultp);
    }
    ASTNODE_NODE_FUNCS(ConsAssoc)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* defaultp() const { return op1p(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsDynArray final : public AstNodeMath {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    explicit AstConsDynArray(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER_ConsDynArray(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(ConsDynArray)
    virtual string emitVerilog() override { return "'{%l, %r}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }  // op1 = expression
    AstNode* rhsp() const { return op2p(); }  // op2 = expression
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsQueue final : public AstNodeMath {
    // Construct a queue and return object, '{}. '{lhs}, '{lhs. rhs}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    explicit AstConsQueue(FileLine* fl, AstNode* lhsp = nullptr, AstNode* rhsp = nullptr)
        : ASTGEN_SUPER_ConsQueue(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(ConsQueue)
    virtual string emitVerilog() override { return "'{%l, %r}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }  // op1 = expression
    AstNode* rhsp() const { return op2p(); }  // op2 = expression
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConsWildcard final : public AstNodeMath {
    // Construct a wildcard assoc array and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstConsWildcard(FileLine* fl, AstNode* defaultp)
        : ASTGEN_SUPER_ConsWildcard(fl) {
        setNOp1p(defaultp);
    }
    ASTNODE_NODE_FUNCS(ConsWildcard)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* defaultp() const { return op1p(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstConst final : public AstNodeMath {
    // A constant
private:
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
        , m_num(V3Number::VerilogStringLiteral(), this, str) {
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
        , m_num(V3Number::String(), this, num) {
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
    class Null {};
    AstConst(FileLine* fl, Null)
        : ASTGEN_SUPER_Const(fl)
        , m_num(V3Number::Null{}, this) {
        dtypeSetBit();  // Events 1 bit, objects 64 bits, so autoExtend=1 and use bit here
        initWithNumber();
    }
    ASTNODE_NODE_FUNCS(Const)
    virtual string name() const override { return num().ascii(); }  // * = Value
    const V3Number& num() const { return m_num; }  // * = Value
    V3Number& num() { return m_num; }  // * = Value
    uint32_t toUInt() const { return num().toUInt(); }
    int32_t toSInt() const { return num().toSInt(); }
    uint64_t toUQuad() const { return num().toUQuad(); }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        const AstConst* const sp = static_cast<const AstConst*>(samep);
        return num().isCaseEq(sp->num());
    }
    virtual int instrCount() const override { return widthInstrs(); }
    bool isEqAllOnes() const { return num().isEqAllOnes(width()); }
    bool isEqAllOnesV() const { return num().isEqAllOnes(widthMinV()); }
    // Parse string and create appropriate type of AstConst.
    // May return nullptr on parse failure.
    static AstConst* parseParamLiteral(FileLine* fl, const string& literal);
};
class AstEmptyQueue final : public AstNodeMath {
public:
    explicit AstEmptyQueue(FileLine* fl)
        : ASTGEN_SUPER_EmptyQueue(fl) {}
    ASTNODE_NODE_FUNCS(EmptyQueue)
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() override { return "{}"; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual bool cleanOut() const override { return true; }
};
class AstEnumItemRef final : public AstNodeMath {
private:
    AstEnumItem* m_itemp;  // [AfterLink] Pointer to item
    AstNodeModule* m_classOrPackagep;  // Package hierarchy
public:
    AstEnumItemRef(FileLine* fl, AstEnumItem* itemp, AstNodeModule* classOrPackagep)
        : ASTGEN_SUPER_EnumItemRef(fl)
        , m_itemp{itemp}
        , m_classOrPackagep{classOrPackagep} {
        dtypeFrom(m_itemp);
    }
    ASTNODE_NODE_FUNCS(EnumItemRef)
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return itemp()->name(); }
    virtual int instrCount() const override { return 0; }
    const char* broken() const override;
    virtual void cloneRelink() override {
        if (m_itemp->clonep()) m_itemp = m_itemp->clonep();
    }
    virtual bool same(const AstNode* samep) const override {
        const AstEnumItemRef* const sp = static_cast<const AstEnumItemRef*>(samep);
        return itemp() == sp->itemp();
    }
    AstEnumItem* itemp() const { return m_itemp; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
};
class AstExprStmt final : public AstNodeMath {
    // Perform a statement, often assignment inside an expression/math node,
    // the parent gets passed the 'resultp()'.
    // resultp is evaluated AFTER the statement(s).
public:
    AstExprStmt(FileLine* fl, AstNode* stmtsp, AstNode* resultp)
        : ASTGEN_SUPER_ExprStmt(fl) {
        addOp1p(stmtsp);
        setOp2p(resultp);  // Possibly in future nullptr could mean return rhsp()
        dtypeFrom(resultp);
    }
    ASTNODE_NODE_FUNCS(ExprStmt)
    // ACCESSORS
    AstNode* stmtsp() const { return op1p(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* resultp() const { return op2p(); }
    // METHODS
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode*) const override { return true; }
};
class AstFError final : public AstNodeMath {
public:
    AstFError(FileLine* fl, AstNode* filep, AstNode* strp)
        : ASTGEN_SUPER_FError(fl) {
        setOp1p(filep);
        setOp2p(strp);
    }
    ASTNODE_NODE_FUNCS(FError)
    virtual string emitVerilog() override { return "%f$ferror(%l, %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    void filep(AstNode* nodep) { setOp1p(nodep); }
    AstNode* filep() const { return op1p(); }
    void strp(AstNode* nodep) { setOp2p(nodep); }
    AstNode* strp() const { return op2p(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstFRead final : public AstNodeMath {
    // Parents: expr
    // Children: varrefs to load
    // Children: file which must be a varref
    // Children: low index
    // Children: count
public:
    AstFRead(FileLine* fl, AstNode* memp, AstNode* filep, AstNode* startp, AstNode* countp)
        : ASTGEN_SUPER_FRead(fl) {
        setOp1p(memp);
        setOp2p(filep);
        setNOp3p(startp);
        setNOp4p(countp);
    }
    ASTNODE_NODE_FUNCS(FRead)
    virtual string verilogKwd() const override { return "$fread"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* memp() const { return op1p(); }
    void memp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* filep() const { return op2p(); }
    void filep(AstNode* nodep) { setOp2p(nodep); }
    AstNode* startp() const { return op3p(); }
    void startp(AstNode* nodep) { setNOp3p(nodep); }
    AstNode* countp() const { return op4p(); }
    void countp(AstNode* nodep) { setNOp4p(nodep); }
};
class AstFRewind final : public AstNodeMath {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFRewind(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FRewind(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FRewind)
    virtual string verilogKwd() const override { return "$frewind"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstFScanF final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string m_text;

public:
    AstFScanF(FileLine* fl, const string& text, AstNode* filep, AstNode* exprsp)
        : ASTGEN_SUPER_FScanF(fl)
        , m_text{text} {
        addNOp1p(exprsp);
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FScanF)
    virtual string name() const override { return m_text; }
    virtual string verilogKwd() const override { return "$fscanf"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstFScanF*>(samep)->text();
    }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstFSeek final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: offset
    // Children: operation
public:
    AstFSeek(FileLine* fl, AstNode* filep, AstNode* offset, AstNode* operation)
        : ASTGEN_SUPER_FSeek(fl) {
        setOp2p(filep);
        setNOp3p(offset);
        setNOp4p(operation);
    }
    ASTNODE_NODE_FUNCS(FSeek)
    virtual string verilogKwd() const override { return "$fseek"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNode* nodep) { setOp2p(nodep); }
    AstNode* offset() const { return op3p(); }
    void offset(AstNode* nodep) { setNOp3p(nodep); }
    AstNode* operation() const { return op4p(); }
    void operation(AstNode* nodep) { setNOp4p(nodep); }
};
class AstFTell final : public AstNodeMath {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFTell(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FTell(fl) {
        setNOp2p(filep);
    }
    ASTNODE_NODE_FUNCS(FTell)
    virtual string verilogKwd() const override { return "$ftell"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstFell final : public AstNodeMath {
    // Verilog $fell
    // Parents: math
    // Children: expression
public:
    AstFell(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER_Fell(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Fell)
    virtual string emitVerilog() override { return "$fell(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_AS(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p((AstNode*)sentreep); }  // op2 = clock domain
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstGatePin final : public AstNodeMath {
    // Possibly expand a gate primitive input pin value to match the range of the gate primitive
public:
    AstGatePin(FileLine* fl, AstNode* lhsp, AstRange* rangep)
        : ASTGEN_SUPER_GatePin(fl) {
        setOp1p(lhsp);
        setOp2p((AstNode*)rangep);
    }
    ASTNODE_NODE_FUNCS(GatePin)
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    AstNode* exprp() const { return op1p(); }  // op1 = Pin expression
    AstRange* rangep() const { return VN_AS(op2p(), Range); }  // op2 = Range of pin
};
class AstImplication final : public AstNodeMath {
    // Verilog |-> |=>
    // Parents: math
    // Children: expression
public:
    AstImplication(FileLine* fl, AstNode* lhs, AstNode* rhs)
        : ASTGEN_SUPER_Implication(fl) {
        setOp1p(lhs);
        setOp2p(rhs);
    }
    ASTNODE_NODE_FUNCS(Implication)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    void lhsp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    AstSenTree* sentreep() const { return VN_AS(op4p(), SenTree); }  // op4 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp4p((AstNode*)sentreep); }  // op4 = clock domain
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstInside final : public AstNodeMath {
public:
    AstInside(FileLine* fl, AstNode* exprp, AstNode* itemsp)
        : ASTGEN_SUPER_Inside(fl) {
        addOp1p(exprp);
        addOp2p(itemsp);
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Inside)
    AstNode* exprp() const { return op1p(); }  // op1 = LHS expression to compare with
    // op2 = RHS, possibly a list of expr or AstInsideRange
    AstNode* itemsp() const { return op2p(); }
    virtual string emitVerilog() override { return "%l inside { %r }"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }  // NA
};
class AstInsideRange final : public AstNodeMath {
public:
    AstInsideRange(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_InsideRange(fl) {
        addOp1p(lhsp);
        addOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(InsideRange)
    AstNode* lhsp() const { return op1p(); }  // op1 = LHS
    AstNode* rhsp() const { return op2p(); }  // op2 = RHS
    virtual string emitVerilog() override { return "[%l:%r]"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }  // NA
    // Create AstAnd(AstGte(...), AstLte(...))
    AstNode* newAndFromInside(AstNode* exprp, AstNode* lhsp, AstNode* rhsp);
};
class AstLambdaArgRef final : public AstNodeMath {
    // Lambda argument usage
    // These are not AstVarRefs because we need to be able to delete/clone lambdas during
    // optimizations and AstVar's are painful to remove.
private:
    string m_name;  // Name of variable
    bool m_index;  // Index, not value

public:
    AstLambdaArgRef(FileLine* fl, const string& name, bool index)
        : ASTGEN_SUPER_LambdaArgRef(fl)
        , m_name{name}
        , m_index(index) {}
    ASTNODE_NODE_FUNCS(LambdaArgRef)
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual string emitVerilog() override { return name(); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void name(const string& name) override { m_name = name; }
    bool index() const { return m_index; }
};
class AstMemberSel final : public AstNodeMath {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    string m_name;
    AstVar* m_varp = nullptr;  // Post link, variable within class that is target of selection
public:
    AstMemberSel(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name)
        : ASTGEN_SUPER_MemberSel(fl)
        , m_name{name} {
        setOp1p(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMemberSel(FileLine* fl, AstNode* fromp, AstNodeDType* dtp)
        : ASTGEN_SUPER_MemberSel(fl)
        , m_name{dtp->name()} {
        setOp1p(fromp);
        dtypep(dtp);
    }
    ASTNODE_NODE_FUNCS(MemberSel)
    void cloneRelink() override;
    const char* broken() const override;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return true;
    }  // dtype comparison does it
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstVar* varp() const { return m_varp; }
    void varp(AstVar* nodep) { m_varp = nodep; }
};
class AstNewCopy final : public AstNodeMath {
    // New as shallow copy
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNewCopy(FileLine* fl, AstNode* rhsp)
        : ASTGEN_SUPER_NewCopy(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        setNOp1p(rhsp);
    }
    ASTNODE_NODE_FUNCS(NewCopy)
    virtual string emitVerilog() override { return "new"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* rhsp() const { return op1p(); }
};
class AstNewDynamic final : public AstNodeMath {
    // New for dynamic array
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNewDynamic(FileLine* fl, AstNode* sizep, AstNode* rhsp)
        : ASTGEN_SUPER_NewDynamic(fl) {
        dtypeFrom(rhsp);  // otherwise V3Width will resolve
        setNOp1p(sizep);
        setNOp2p(rhsp);
    }
    ASTNODE_NODE_FUNCS(NewDynamic)
    virtual string emitVerilog() override { return "new"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* sizep() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};
class AstPast final : public AstNodeMath {
    // Verilog $past
    // Parents: math
    // Children: expression
public:
    AstPast(FileLine* fl, AstNode* exprp, AstNode* ticksp)
        : ASTGEN_SUPER_Past(fl) {
        addOp1p(exprp);
        addNOp2p(ticksp);
    }
    ASTNODE_NODE_FUNCS(Past)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstNode* ticksp() const { return op2p(); }  // op2 = ticks or nullptr means 1
    AstSenTree* sentreep() const { return VN_AS(op4p(), SenTree); }  // op4 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp4p((AstNode*)sentreep); }  // op4 = clock domain
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstPatMember final : public AstNodeMath {
    // Verilog '{a} or '{a{b}}
    // Parents: AstPattern
    // Children: expression, AstPattern, replication count
private:
    bool m_default = false;

public:
    AstPatMember(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* repp)
        : ASTGEN_SUPER_PatMember(fl) {
        addOp1p(lhsp), setNOp2p(keyp), setNOp3p(repp);
    }
    ASTNODE_NODE_FUNCS(PatMember)
    virtual string emitVerilog() override { return lhssp() ? "%f{%r{%k%l}}" : "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs() * 2; }
    virtual void dump(std::ostream& str = std::cout) const override;
    // op1 = expression to assign or another AstPattern (list if replicated)
    AstNode* lhssp() const { return op1p(); }
    AstNode* keyp() const { return op2p(); }  // op2 = assignment key (Const, id Text)
    AstNode* repp() const { return op3p(); }  // op3 = replication count, or nullptr for count 1
    bool isDefault() const { return m_default; }
    void isDefault(bool flag) { m_default = flag; }
};
class AstPattern final : public AstNodeMath {
    // Verilog '{a,b,c,d...}
    // Parents: AstNodeAssign, AstPattern, ...
    // Children: expression, AstPattern, AstPatReplicate
public:
    AstPattern(FileLine* fl, AstNode* itemsp)
        : ASTGEN_SUPER_Pattern(fl) {
        addNOp2p(itemsp);
    }
    ASTNODE_NODE_FUNCS(Pattern)
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNode* itemsp() const { return op2p(); }  // op2 = AstPatReplicate, AstPatMember, etc
    void addItemsp(AstNode* nodep) { addOp2p(nodep); }
};
class AstRand final : public AstNodeMath {
    // $random/$random(seed) or $urandom/$urandom(seed)
    // Return a random number, based upon width()
private:
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
        setNOp1p(seedp);
    }
    ASTNODE_NODE_FUNCS(Rand)
    virtual string emitVerilog() override {
        return seedp() ? (m_urandom ? "%f$urandom(%l)" : "%f$random(%l)")
                       : (m_urandom ? "%f$urandom()" : "%f$random()");
    }
    virtual string emitC() override {
        return m_reset ? "VL_RAND_RESET_%nq(%nw, %P)"
               : seedp()
                   ? (urandom() ? "VL_URANDOM_SEEDED_%nq%lq(%li)" : "VL_RANDOM_SEEDED_%nq%lq(%li)")
               : isWide() ? "VL_RANDOM_%nq(%nw, %P)"  //
                          : "VL_RANDOM_%nq()";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    bool combinable(const AstRand* samep) const {
        return !seedp() && !samep->seedp() && reset() == samep->reset()
               && urandom() == samep->urandom();
    }
    AstNode* seedp() const { return op1p(); }
    bool reset() const { return m_reset; }
    bool urandom() const { return m_urandom; }
};
class AstRose final : public AstNodeMath {
    // Verilog $rose
    // Parents: math
    // Children: expression
public:
    AstRose(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER_Rose(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Rose)
    virtual string emitVerilog() override { return "$rose(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_AS(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p((AstNode*)sentreep); }  // op2 = clock domain
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstSScanF final : public AstNodeMath {
    // Parents: expr
    // Children: file which must be a varref
    // Children: varrefs to load
private:
    string m_text;

public:
    AstSScanF(FileLine* fl, const string& text, AstNode* fromp, AstNode* exprsp)
        : ASTGEN_SUPER_SScanF(fl)
        , m_text{text} {
        addNOp1p(exprsp);
        setOp2p(fromp);
    }
    ASTNODE_NODE_FUNCS(SScanF)
    virtual string name() const override { return m_text; }
    virtual string verilogKwd() const override { return "$sscanf"; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }  // SPECIAL: has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: makes output
    virtual bool cleanOut() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSScanF*>(samep)->text();
    }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstNode* fromp() const { return op2p(); }
    void fromp(AstNode* nodep) { setOp2p(nodep); }
};
class AstSampled final : public AstNodeMath {
    // Verilog $sampled
    // Parents: math
    // Children: expression
public:
    AstSampled(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER_Sampled(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Sampled)
    virtual string emitVerilog() override { return "$sampled(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return 0; }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstScopeName final : public AstNodeMath {
    // For display %m and DPI context imports
    // Parents:  DISPLAY
    // Children: TEXT
private:
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
    ASTNODE_NODE_FUNCS(ScopeName)
    virtual bool same(const AstNode* samep) const override {
        return (m_dpiExport == static_cast<const AstScopeName*>(samep)->m_dpiExport
                && m_forFormat == static_cast<const AstScopeName*>(samep)->m_forFormat);
    }
    virtual string emitVerilog() override { return ""; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    AstText* scopeAttrp() const { return VN_AS(op1p(), Text); }
    void scopeAttrp(AstNode* nodep) { addOp1p(nodep); }
    AstText* scopeEntrp() const { return VN_AS(op2p(), Text); }
    void scopeEntrp(AstNode* nodep) { addOp2p(nodep); }
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
class AstSetAssoc final : public AstNodeMath {
    // Set an assoc array element and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstSetAssoc(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* valuep)
        : ASTGEN_SUPER_SetAssoc(fl) {
        setOp1p(lhsp);
        setNOp2p(keyp);
        setOp3p(valuep);
    }
    ASTNODE_NODE_FUNCS(SetAssoc)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }
    AstNode* keyp() const { return op2p(); }
    AstNode* valuep() const { return op3p(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstSetWildcard final : public AstNodeMath {
    // Set a wildcard assoc array element and return object, '{}
    // Parents: math
    // Children: expression (elements or other queues)
public:
    AstSetWildcard(FileLine* fl, AstNode* lhsp, AstNode* keyp, AstNode* valuep)
        : ASTGEN_SUPER_SetWildcard(fl) {
        setOp1p(lhsp);
        setNOp2p(keyp);
        setOp3p(valuep);
    }
    ASTNODE_NODE_FUNCS(SetWildcard)
    virtual string emitVerilog() override { return "'{}"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* lhsp() const { return op1p(); }
    AstNode* keyp() const { return op2p(); }
    AstNode* valuep() const { return op3p(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstStable final : public AstNodeMath {
    // Verilog $stable
    // Parents: math
    // Children: expression
public:
    AstStable(FileLine* fl, AstNode* exprp)
        : ASTGEN_SUPER_Stable(fl) {
        addOp1p(exprp);
    }
    ASTNODE_NODE_FUNCS(Stable)
    virtual string emitVerilog() override { return "$stable(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }
    virtual int instrCount() const override { return widthInstrs(); }
    AstNode* exprp() const { return op1p(); }  // op1 = expression
    AstSenTree* sentreep() const { return VN_AS(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p((AstNode*)sentreep); }  // op2 = clock domain
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstSystemF final : public AstNodeMath {
    // $system used as function
public:
    AstSystemF(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SystemF(fl) {
        setOp1p(lhsp);
    }
    ASTNODE_NODE_FUNCS(SystemF)
    virtual string verilogKwd() const override { return "$system"; }
    virtual string emitVerilog() override { return verilogKwd(); }
    virtual string emitC() override { return "VL_SYSTEM_%nq(%lw, %P)"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* lhsp() const { return op1p(); }
};
class AstTestPlusArgs final : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If nullptr then this is a $test$plusargs instead of $value$plusargs
public:
    AstTestPlusArgs(FileLine* fl, AstNode* searchp)
        : ASTGEN_SUPER_TestPlusArgs(fl) {
        setOp1p(searchp);
    }
    ASTNODE_NODE_FUNCS(TestPlusArgs)
    virtual string verilogKwd() const override { return "$test$plusargs"; }
    virtual string emitVerilog() override { return verilogKwd(); }
    virtual string emitC() override { return "VL_VALUEPLUSARGS_%nq(%lw, %P, nullptr)"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* searchp() const { return op1p(); }  // op1 = Search expression
    void searchp(AstNode* nodep) { setOp1p(nodep); }
};
class AstUCFunc final : public AstNodeMath {
    // User's $c function
    // Perhaps this should be an AstNodeListop; but there's only one list math right now
public:
    AstUCFunc(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_UCFunc(fl) {
        addNOp1p(exprsp);
    }
    ASTNODE_NODE_FUNCS(UCFunc)
    virtual bool cleanOut() const override { return false; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isSubstOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstUnbounded final : public AstNodeMath {
    // A $ in the parser, used for unbounded and queues
    // Due to where is used, treated as Signed32
public:
    explicit AstUnbounded(FileLine* fl)
        : ASTGEN_SUPER_Unbounded(fl) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(Unbounded)
    virtual string emitVerilog() override { return "$"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
};
class AstValuePlusArgs final : public AstNodeMath {
    // Parents: expr
    // Child: variable to set.  If nullptr then this is a $test$plusargs instead of $value$plusargs
public:
    AstValuePlusArgs(FileLine* fl, AstNode* searchp, AstNode* outp)
        : ASTGEN_SUPER_ValuePlusArgs(fl) {
        setOp1p(searchp);
        setOp2p(outp);
    }
    ASTNODE_NODE_FUNCS(ValuePlusArgs)
    virtual string verilogKwd() const override { return "$value$plusargs"; }
    virtual string emitVerilog() override { return "%f$value$plusargs(%l, %k%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return !outp(); }
    virtual bool cleanOut() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* searchp() const { return op1p(); }  // op1 = Search expression
    void searchp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* outp() const { return op2p(); }  // op2 = Expressions to output
    void outp(AstNode* nodep) { setOp2p(nodep); }
};

// === AstNodeBiop ===
class AstBufIf1 final : public AstNodeBiop {
    // lhs is enable, rhs is data to drive
    // Note unlike the Verilog bufif1() UDP, this allows any width; each lhsp
    // bit enables respective rhsp bit
public:
    AstBufIf1(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_BufIf1(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(BufIf1)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstBufIf1(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opBufIf1(lhs, rhs);
    }
    virtual string emitVerilog() override { return "bufif(%r,%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(""); }  // Lclean || Rclean
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstCastDynamic final : public AstNodeBiop {
    // Verilog $cast used as a function
    // Task usage of $cast is converted during parse to assert($cast(...))
    // Parents: MATH
    // Children: MATH
    // lhsp() is value (we are converting FROM) to match AstCCast etc, this
    // is opposite of $cast's order, because the first access is to the
    // value reading from.  Suggest use fromp()/top() instead of lhsp/rhsp().
public:
    AstCastDynamic(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_CastDynamic(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(CastDynamic)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstCastDynamic(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f$cast(%r, %l)"; }
    virtual string emitC() override { return "VL_DYNAMIC_CAST(%r, %l)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 20; }
    virtual bool isPure() const override { return true; }
    AstNode* fromp() const { return lhsp(); }
    AstNode* top() const { return rhsp(); }
};
class AstCompareNN final : public AstNodeBiop {
    // Verilog str.compare() and str.icompare()
private:
    const bool m_ignoreCase;  // True for str.icompare()
public:
    AstCompareNN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, bool ignoreCase)
        : ASTGEN_SUPER_CompareNN(fl, lhsp, rhsp)
        , m_ignoreCase{ignoreCase} {
        dtypeSetUInt32();
    }
    ASTNODE_NODE_FUNCS(CompareNN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstCompareNN(this->fileline(), lhsp, rhsp, m_ignoreCase);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCompareNN(lhs, rhs, m_ignoreCase);
    }
    virtual string name() const override { return m_ignoreCase ? "icompare" : "compare"; }
    virtual string emitVerilog() override {
        return m_ignoreCase ? "%k(%l.icompare(%r))" : "%k(%l.compare(%r))";
    }
    virtual string emitC() override {
        return m_ignoreCase ? "VL_CMP_NN(%li,%ri,true)" : "VL_CMP_NN(%li,%ri,false)";
    }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstConcat final : public AstNodeBiop {
    // If you're looking for {#{}}, see AstReplicate
public:
    AstConcat(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Concat(fl, lhsp, rhsp) {
        if (lhsp->dtypep() && rhsp->dtypep()) {
            dtypeSetLogicSized(lhsp->dtypep()->width() + rhsp->dtypep()->width(),
                               VSigning::UNSIGNED);
        }
    }
    ASTNODE_NODE_FUNCS(Concat)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstConcat(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcat(lhs, rhs);
    }
    virtual string emitC() override { return "VL_CONCAT_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstConcatN final : public AstNodeBiop {
    // String concatenate
public:
    AstConcatN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_ConcatN(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ConcatN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstConcatN(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{%l, %k%r}"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opConcatN(lhs, rhs);
    }
    virtual string emitC() override { return "VL_CONCATN_NNN(%li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstDiv final : public AstNodeBiop {
public:
    AstDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Div(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Div)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDiv(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDiv(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { return "VL_DIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
};
class AstDivD final : public AstNodeBiop {
public:
    AstDivD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_DivD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(DivD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDivD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "/"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL_DIV; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstDivS final : public AstNodeBiop {
public:
    AstDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_DivS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(DivS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstDivS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opDivS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f/ %r)"; }
    virtual string emitC() override { return "VL_DIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
    virtual bool signedFlavor() const override { return true; }
};
class AstEqWild final : public AstNodeBiop {
    // Note wildcard operator rhs differs from lhs
public:
    AstEqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_EqWild(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqWild)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqWild(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstEqWild/AstEqD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f==? %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstFGetS final : public AstNodeBiop {
public:
    AstFGetS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_FGetS(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(FGetS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstFGetS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%f$fgets(%l,%r)"; }
    virtual string emitC() override {
        return strgp()->dtypep()->basicp()->isString() ? "VL_FGETS_NI(%li, %ri)"
                                                       : "VL_FGETS_%nqX%rq(%lw, %P, &(%li), %ri)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    AstNode* strgp() const { return lhsp(); }
    AstNode* filep() const { return rhsp(); }
};
class AstFUngetC final : public AstNodeBiop {
public:
    AstFUngetC(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_FUngetC(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(FUngetC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstFUngetC(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f$ungetc(%r, %l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() override {
        return "(%li ? (ungetc(%ri, VL_CVT_I_FP(%li)) >= 0 ? 0 : -1) : -1)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
    AstNode* charp() const { return rhsp(); }
};
class AstGetcN final : public AstNodeBiop {
    // Verilog string.getc()
public:
    AstGetcN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GetcN(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(GetcN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGetcN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGetcN(lhs, rhs);
    }
    virtual string name() const override { return "getc"; }
    virtual string emitVerilog() override { return "%k(%l.getc(%r))"; }
    virtual string emitC() override { return "VL_GETC_N(%li,%ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGetcRefN final : public AstNodeBiop {
    // Verilog string[#] on the left-hand-side of assignment
    // Spec says is of type byte (not string of single character)
public:
    AstGetcRefN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GetcRefN(fl, lhsp, rhsp) {
        dtypeSetBitSized(8, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(GetcRefN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGetcRefN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k%l[%r]"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGt final : public AstNodeBiop {
public:
    AstGt(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Gt(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Gt)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGt(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGt(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { return "VL_GT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGtD final : public AstNodeBiop {
public:
    AstGtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GtD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstGtN final : public AstNodeBiop {
public:
    AstGtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GtN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstGtS final : public AstNodeBiop {
public:
    AstGtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GtS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GtS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGtS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGtS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f> %r)"; }
    virtual string emitC() override { return "VL_GTS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstGte final : public AstNodeBiop {
public:
    AstGte(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Gte(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Gte)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGte(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGte(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { return "VL_GTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstGteD final : public AstNodeBiop {
public:
    AstGteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GteD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstGteN final : public AstNodeBiop {
public:
    AstGteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GteN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return ">="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstGteS final : public AstNodeBiop {
public:
    AstGteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_GteS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(GteS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstGteS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opGteS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>= %r)"; }
    virtual string emitC() override { return "VL_GTES_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstLogAnd final : public AstNodeBiop {
public:
    AstLogAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LogAnd(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogAnd)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogAnd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogAnd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f&& %r)"; }
    virtual string emitC() override { return "VL_LOGAND_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "&&"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstLogIf final : public AstNodeBiop {
public:
    AstLogIf(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LogIf(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogIf)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogIf(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogIf(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f-> %r)"; }
    virtual string emitC() override { return "VL_LOGIF_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "->"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstLogOr final : public AstNodeBiop {
    // LOGOR with optional side effects
    // Side effects currently used in some V3Width code
    // TBD if this concept is generally adopted for side-effect tracking
    // versus V3Const tracking it itself
    bool m_sideEffect = false;  // Has side effect, relies on short-circuiting
public:
    AstLogOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LogOr(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogOr)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogOr(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogOr(lhs, rhs);
    }
    virtual bool same(const AstNode* samep) const override {
        const AstLogOr* const sp = static_cast<const AstLogOr*>(samep);
        return m_sideEffect == sp->m_sideEffect;
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string emitVerilog() override { return "%k(%l %f|| %r)"; }
    virtual string emitC() override { return "VL_LOGOR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "||"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
    virtual bool isPure() const override { return !m_sideEffect; }
    void sideEffect(bool flag) { m_sideEffect = flag; }
    bool sideEffect() const { return m_sideEffect; }
};
class AstLt final : public AstNodeBiop {
public:
    AstLt(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Lt(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Lt)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLt(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLt(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { return "VL_LT_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstLtD final : public AstNodeBiop {
public:
    AstLtD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LtD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstLtN final : public AstNodeBiop {
public:
    AstLtN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LtN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstLtS final : public AstNodeBiop {
public:
    AstLtS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LtS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LtS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLtS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLtS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f< %r)"; }
    virtual string emitC() override { return "VL_LTS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstLte final : public AstNodeBiop {
public:
    AstLte(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Lte(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Lte)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLte(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLte(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { return "VL_LTE_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstLteD final : public AstNodeBiop {
public:
    AstLteD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LteD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstLteN final : public AstNodeBiop {
public:
    AstLteN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LteN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "<="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstLteS final : public AstNodeBiop {
public:
    AstLteS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LteS(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LteS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLteS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLteS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<= %r)"; }
    virtual string emitC() override { return "VL_LTES_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstModDiv final : public AstNodeBiop {
public:
    AstModDiv(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_ModDiv(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(ModDiv)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstModDiv(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDiv(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f%% %r)"; }
    virtual string emitC() override { return "VL_MODDIV_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
};
class AstModDivS final : public AstNodeBiop {
public:
    AstModDivS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_ModDivS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(ModDivS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstModDivS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opModDivS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f%% %r)"; }
    virtual string emitC() override { return "VL_MODDIVS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_DIV; }
    virtual bool signedFlavor() const override { return true; }
};
class AstNeqWild final : public AstNodeBiop {
public:
    AstNeqWild(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_NeqWild(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqWild)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqWild(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opWildNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!=? %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstPow final : public AstNodeBiop {
public:
    AstPow(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Pow(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Pow)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPow(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPow(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override { return "VL_POW_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
};
class AstPowD final : public AstNodeBiop {
public:
    AstPowD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_PowD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(PowD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override { return "pow(%li,%ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL_DIV * 5; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstPowSS final : public AstNodeBiop {
public:
    AstPowSS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_PowSS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowSS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowSS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,1)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstPowSU final : public AstNodeBiop {
public:
    AstPowSU(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_PowSU(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowSU)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowSU(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowSU(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 1,0)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstPowUS final : public AstNodeBiop {
public:
    AstPowUS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_PowUS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(PowUS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstPowUS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opPowUS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f** %r)"; }
    virtual string emitC() override {
        return "VL_POWSS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri, 0,1)";
    }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL * 10; }
    virtual bool signedFlavor() const override { return true; }
};
class AstReplicate final : public AstNodeBiop {
    // Also used as a "Uniop" flavor of Concat, e.g. "{a}"
    // Verilog {rhs{lhs}} - Note rhsp() is the replicate value, not the lhsp()
public:
    AstReplicate(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Replicate(fl, lhsp, rhsp) {
        if (lhsp) {
            if (const AstConst* const constp = VN_CAST(rhsp, Const)) {
                dtypeSetLogicSized(lhsp->width() * constp->toUInt(), VSigning::UNSIGNED);
            }
        }
    }
    AstReplicate(FileLine* fl, AstNode* lhsp, uint32_t repCount)
        : AstReplicate(fl, lhsp, new AstConst(fl, repCount)) {}
    ASTNODE_NODE_FUNCS(Replicate)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstReplicate(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opRepl(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%f{%r{%k%l}}"; }
    virtual string emitC() override { return "VL_REPLICATE_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstReplicateN final : public AstNodeBiop {
    // String replicate
public:
    AstReplicateN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_ReplicateN(fl, lhsp, rhsp) {
        dtypeSetString();
    }
    AstReplicateN(FileLine* fl, AstNode* lhsp, uint32_t repCount)
        : AstReplicateN(fl, lhsp, new AstConst(fl, repCount)) {}
    ASTNODE_NODE_FUNCS(ReplicateN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstReplicateN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opReplN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%f{%r{%k%l}}"; }
    virtual string emitC() override { return "VL_REPLICATEN_NN%rq(%li, %ri)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
    virtual bool stringFlavor() const override { return true; }
};
class AstShiftL final : public AstNodeBiop {
public:
    AstShiftL(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftL(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftL)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftL(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftL(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<< %r)"; }
    virtual string emitC() override { return "VL_SHIFTL_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : "<<";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstShiftR final : public AstNodeBiop {
public:
    AstShiftR(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftR(fl, lhsp, rhsp) {
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftR)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftR(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftR(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f>> %r)"; }
    virtual string emitC() override { return "VL_SHIFTR_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override {
        return (rhsp()->isWide() || rhsp()->isQuad()) ? "" : ">>";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    // LHS size might be > output size, so don't want to force size
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstShiftRS final : public AstNodeBiop {
    // Shift right with sign extension, >>> operator
    // Output data type's width determines which bit is used for sign extension
public:
    AstShiftRS(FileLine* fl, AstNode* lhsp, AstNode* rhsp, int setwidth = 0)
        : ASTGEN_SUPER_ShiftRS(fl, lhsp, rhsp) {
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        if (setwidth) dtypeSetLogicSized(setwidth, VSigning::SIGNED);
    }
    ASTNODE_NODE_FUNCS(ShiftRS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstShiftRS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opShiftRS(lhs, rhs, lhsp()->widthMinV());
    }
    virtual string emitVerilog() override { return "%k(%l %f>>> %r)"; }
    virtual string emitC() override { return "VL_SHIFTRS_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool signedFlavor() const override { return true; }
};
class AstSub final : public AstNodeBiop {
public:
    AstSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Sub(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Sub)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstSub(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSub(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f- %r)"; }
    virtual string emitC() override { return "VL_SUB_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
};
class AstSubD final : public AstNodeBiop {
public:
    AstSubD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_SubD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(SubD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstSubD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opSubD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f- %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstURandomRange final : public AstNodeBiop {
    // $urandom_range
public:
    explicit AstURandomRange(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_URandomRange(fl, lhsp, rhsp) {
        dtypeSetUInt32();  // Says IEEE
    }
    ASTNODE_NODE_FUNCS(URandomRange)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstURandomRange(fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%f$urandom_range(%l, %r)"; }
    virtual string emitC() override { return "VL_URANDOM_RANGE_%nq(%li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
};

// === AstNodeBiCom ===
class AstEq final : public AstNodeBiCom {
public:
    AstEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Eq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Eq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEq(this->fileline(), lhsp, rhsp);
    }
    static AstNodeBiop* newTyped(FileLine* fl, AstNode* lhsp,
                                 AstNode* rhsp);  // Return AstEq/AstEqD
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstEqCase final : public AstNodeBiCom {
public:
    AstEqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_EqCase(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqCase)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqCase(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f=== %r)"; }
    virtual string emitC() override { return "VL_EQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstEqD final : public AstNodeBiCom {
public:
    AstEqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_EqD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstEqN final : public AstNodeBiCom {
public:
    AstEqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_EqN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(EqN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstEqN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opEqN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f== %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "=="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};
class AstLogEq final : public AstNodeBiCom {
public:
    AstLogEq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_LogEq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogEq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstLogEq(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opLogEq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f<-> %r)"; }
    virtual string emitC() override { return "VL_LOGEQ_%nq%lq%rq(%nw,%lw,%rw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "<->"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
};
class AstNeq final : public AstNodeBiCom {
public:
    AstNeq(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Neq(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(Neq)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeq(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstNeqCase final : public AstNodeBiCom {
public:
    AstNeqCase(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_NeqCase(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqCase)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqCase(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opCaseNeq(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!== %r)"; }
    virtual string emitC() override { return "VL_NEQ_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstNeqD final : public AstNodeBiCom {
public:
    AstNeqD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_NeqD(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstNeqN final : public AstNodeBiCom {
public:
    AstNeqN(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_NeqN(fl, lhsp, rhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(NeqN)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstNeqN(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opNeqN(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f!= %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "!="; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_STR; }
    virtual bool stringFlavor() const override { return true; }
};

// === AstNodeBiComAsv ===
class AstAdd final : public AstNodeBiComAsv {
public:
    AstAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Add(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Add)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAdd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAdd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f+ %r)"; }
    virtual string emitC() override { return "VL_ADD_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "+"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
};
class AstAddD final : public AstNodeBiComAsv {
public:
    AstAddD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AddD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(AddD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAddD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAddD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f+ %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "+"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstAnd final : public AstNodeBiComAsv {
public:
    AstAnd(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_And(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(And)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAnd(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAnd(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f& %r)"; }
    virtual string emitC() override { return "VL_AND_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "&"; }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstMul final : public AstNodeBiComAsv {
public:
    AstMul(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Mul(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Mul)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMul(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMul(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { return "VL_MUL_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "*"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL; }
};
class AstMulD final : public AstNodeBiComAsv {
public:
    AstMulD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_MulD(fl, lhsp, rhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(MulD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMulD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulD(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "*"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstMulS final : public AstNodeBiComAsv {
public:
    AstMulS(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_MulS(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(MulS)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstMulS(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opMulS(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f* %r)"; }
    virtual string emitC() override { return "VL_MULS_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual int instrCount() const override { return widthInstrs() * INSTR_COUNT_INT_MUL; }
    virtual bool signedFlavor() const override { return true; }
};
class AstOr final : public AstNodeBiComAsv {
public:
    AstOr(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Or(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Or)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstOr(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opOr(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f| %r)"; }
    virtual string emitC() override { return "VL_OR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "|"; }
    virtual bool cleanOut() const override { V3ERROR_NA_RETURN(false); }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};
class AstXor final : public AstNodeBiComAsv {
public:
    AstXor(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Xor(fl, lhsp, rhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Xor)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstXor(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opXor(lhs, rhs);
    }
    virtual string emitVerilog() override { return "%k(%l %f^ %r)"; }
    virtual string emitC() override { return "VL_XOR_%lq(%lW, %P, %li, %ri)"; }
    virtual string emitSimpleOperator() override { return "^"; }
    virtual bool cleanOut() const override { return false; }  // Lclean && Rclean
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
};

// === AstNodeSel ===
class AstArraySel final : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), NodeArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), NodeArrayDType)->subDTypep());
        }
    }

public:
    AstArraySel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER_ArraySel(fl, fromp, bitp) {
        init(fromp);
    }
    AstArraySel(FileLine* fl, AstNode* fromp, int bit)
        : ASTGEN_SUPER_ArraySel(fl, fromp, new AstConst(fl, bit)) {
        init(fromp);
    }
    ASTNODE_NODE_FUNCS(ArraySel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstArraySel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA; /* How can from be a const? */
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override { return "%li%k[%ri]"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override {
        return true;
    }  // esp for V3Const::ifSameAssign
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    // Special operators
    // Return base var (or const) nodep dereferences
    static AstNode* baseFromp(AstNode* nodep, bool overMembers);
};
class AstAssocSel final : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), AssocArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), AssocArrayDType)->subDTypep());
        }
    }

public:
    AstAssocSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER_AssocSel(fl, fromp, bitp) {
        init(fromp);
    }
    ASTNODE_NODE_FUNCS(AssocSel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssocSel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override { return "%li%k[%ri]"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override {
        return true;
    }  // esp for V3Const::ifSameAssign
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
};
class AstWildcardSel final : public AstNodeSel {
    // Parents: math|stmt
    // Children: varref|arraysel, math
private:
    void init(AstNode* fromp) {
        if (fromp && VN_IS(fromp->dtypep()->skipRefp(), WildcardArrayDType)) {
            // Strip off array to find what array references
            dtypeFrom(VN_AS(fromp->dtypep()->skipRefp(), WildcardArrayDType)->subDTypep());
        }
    }

public:
    AstWildcardSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER_WildcardSel(fl, fromp, bitp) {
        init(fromp);
    }
    ASTNODE_NODE_FUNCS(WildcardSel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstWildcardSel{this->fileline(), lhsp, rhsp};
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override { return "%li%k[%ri]"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool isGateOptimizable() const override {
        return true;
    }  // esp for V3Const::ifSameAssign
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
};
class AstWordSel final : public AstNodeSel {
    // Select a single word from a multi-word wide value
public:
    AstWordSel(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER_WordSel(fl, fromp, bitp) {
        dtypeSetUInt32();  // Always used on WData arrays so returns edata size
    }
    ASTNODE_NODE_FUNCS(WordSel)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstWordSel(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { return "%k(%l%f[%r])"; }
    virtual string emitC() override {
        return "%li[%ri]";
    }  // Not %k, as usually it's a small constant rhsp
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};

// === AstNodeStream ===
class AstStreamL final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamL(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_StreamL(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamL)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstStreamL(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{ << %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opStreamL(lhs, rhs);
    }
    virtual string emitC() override { return "VL_STREAML_%nq%lq%rq(%lw, %P, %li, %ri)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};
class AstStreamR final : public AstNodeStream {
    // Verilog {rhs{lhs}} - Note rhsp() is the slice size, not the lhsp()
public:
    AstStreamR(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_StreamR(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(StreamR)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstStreamR(this->fileline(), lhsp, rhsp);
    }
    virtual string emitVerilog() override { return "%f{ >> %r %k{%l} }"; }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.opAssign(lhs);
    }
    virtual string emitC() override { return isWide() ? "VL_ASSIGN_W(%nw, %P, %li)" : "%li"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }
};

// === AstNodeSystemBiop ===
class AstAtan2D final : public AstNodeSystemBiop {
public:
    AstAtan2D(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Atan2D(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(Atan2D)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAtan2D(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::atan2(lhs.toDouble(), rhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atan2(%l,%r)"; }
    virtual string emitC() override { return "atan2(%li,%ri)"; }
};
class AstHypotD final : public AstNodeSystemBiop {
public:
    AstHypotD(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_HypotD(fl, lhsp, rhsp) {}
    ASTNODE_NODE_FUNCS(HypotD)
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstHypotD(this->fileline(), lhsp, rhsp);
    }
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs) override {
        out.setDouble(std::hypot(lhs.toDouble(), rhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$hypot(%l,%r)"; }
    virtual string emitC() override { return "hypot(%li,%ri)"; }
};

// === AstNodeQuadop ===
class AstCountBits final : public AstNodeQuadop {
    // Number of bits set in vector
public:
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl1p->cloneTree(false),
                                 ctrl1p->cloneTree(false)) {}
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p, AstNode* ctrl2p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl2p, ctrl2p->cloneTree(false)) {}
    AstCountBits(FileLine* fl, AstNode* exprp, AstNode* ctrl1p, AstNode* ctrl2p, AstNode* ctrl3p)
        : ASTGEN_SUPER_CountBits(fl, exprp, ctrl1p, ctrl2p, ctrl3p) {}
    ASTNODE_NODE_FUNCS(CountBits)
    virtual void numberOperate(V3Number& out, const V3Number& expr, const V3Number& ctrl1,
                               const V3Number& ctrl2, const V3Number& ctrl3) override {
        out.opCountBits(expr, ctrl1, ctrl2, ctrl3);
    }
    virtual string emitVerilog() override { return "%f$countbits(%l, %r, %f, %o)"; }
    virtual string emitC() override { return ""; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool cleanFhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool sizeMattersFhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
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
    ASTNODE_NODE_FUNCS(Time)
    virtual string emitVerilog() override { return "%f$time"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_TIME; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
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
    ASTNODE_NODE_FUNCS(TimeD)
    virtual string emitVerilog() override { return "%f$realtime"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_TIME; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};

// === AstNodeTriop ===
class AstPostAdd final : public AstNodeTriop {
    // Post-increment/add
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER_PostAdd(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PostAdd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(%r++)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPostSub final : public AstNodeTriop {
    // Post-decrement/subtract
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPostSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER_PostSub(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PostSub)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(%r--)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPreAdd final : public AstNodeTriop {
    // Pre-increment/add
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only ++ not +=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreAdd(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER_PreAdd(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PreAdd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(++%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPreSub final : public AstNodeTriop {
    // Pre-decrement/subtract
    // Parents:  MATH
    // Children: lhsp: AstConst (1) as currently support only -- not -=
    // Children: rhsp: tree with AstVarRef that is value to read before operation
    // Children: thsp: tree with AstVarRef LValue that is stored after operation
public:
    AstPreSub(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* thsp)
        : ASTGEN_SUPER_PreSub(fl, lhsp, rhsp, thsp) {}
    ASTNODE_NODE_FUNCS(PreSub)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        V3ERROR_NA;  // Need to modify lhs
    }
    virtual string emitVerilog() override { return "%k(--%r)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return false; }
    virtual bool cleanThs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
    virtual bool sizeMattersRhs() const override { return true; }
    virtual bool sizeMattersThs() const override { return true; }
};
class AstPutcN final : public AstNodeTriop {
    // Verilog string.putc()
public:
    AstPutcN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* ths)
        : ASTGEN_SUPER_PutcN(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(PutcN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        out.opPutcN(lhs, rhs, ths);
    }
    virtual string name() const override { return "putc"; }
    virtual string emitVerilog() override { return "%k(%l.putc(%r,%t))"; }
    virtual string emitC() override { return "VL_PUTC_N(%li,%ri,%ti)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
};
class AstSel final : public AstNodeTriop {
    // Multiple bit range extraction
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
    // Tempting to have an access() style method here as LHS selects are quite
    // different, but that doesn't play well with V3Inst and bidirects which don't know direction
private:
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
    int m_declElWidth;  // If a packed array, the number of bits per element
public:
    AstSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, AstNode* widthp)
        : ASTGEN_SUPER_Sel(fl, fromp, lsbp, widthp)
        , m_declElWidth{1} {
        if (VN_IS(widthp, Const)) {
            dtypeSetLogicSized(VN_AS(widthp, Const)->toUInt(), VSigning::UNSIGNED);
        }
    }
    AstSel(FileLine* fl, AstNode* fromp, int lsb, int bitwidth)
        : ASTGEN_SUPER_Sel(fl, fromp, new AstConst(fl, lsb), new AstConst(fl, bitwidth))
        , m_declElWidth{1} {
        dtypeSetLogicSized(bitwidth, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(Sel)
    virtual void dump(std::ostream& str) const override;
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& bit,
                               const V3Number& width) override {
        out.opSel(from, bit.toUInt() + width.toUInt() - 1, bit.toUInt());
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override {
        return widthp()->isOne() ? "VL_BITSEL_%nq%lq%rq%tq(%lw, %P, %li, %ri)"
               : isWide()        ? "VL_SEL_%nq%lq%rq%tq(%nw,%lw, %P, %li, %ri, %ti)"
                                 : "VL_SEL_%nq%lq%rq%tq(%lw, %P, %li, %ri, %ti)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool same(const AstNode*) const override { return true; }
    virtual int instrCount() const override {
        return widthInstrs() * (VN_CAST(lsbp(), Const) ? 3 : 10);
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    AstNode* lsbp() const { return op2p(); }  // op2 = Msb selection expression
    AstNode* widthp() const { return op3p(); }  // op3 = Width
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
    // Parents: math|stmt
    // Children: varref|arraysel, math, constant math
private:
    VNumRange m_declRange;  // Range of the 'from' array if isRanged() is set, else invalid
public:
    AstSliceSel(FileLine* fl, AstNode* fromp, const VNumRange& declRange)
        : ASTGEN_SUPER_SliceSel(fl, fromp, new AstConst(fl, declRange.lo()),
                                new AstConst(fl, declRange.elements()))
        , m_declRange{declRange} {}
    ASTNODE_NODE_FUNCS(SliceSel)
    virtual void dump(std::ostream& str) const override;
    virtual void numberOperate(V3Number& out, const V3Number& from, const V3Number& lo,
                               const V3Number& width) override {
        V3ERROR_NA;
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }  // Removed before EmitC
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
    virtual bool same(const AstNode*) const override { return true; }
    virtual int instrCount() const override { return 10; }  // Removed before matters
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    // For widthConst()/loConst etc, see declRange().elements() and other VNumRange methods
    VNumRange& declRange() { return m_declRange; }
    const VNumRange& declRange() const { return m_declRange; }
    void declRange(const VNumRange& flag) { m_declRange = flag; }
};
class AstSubstrN final : public AstNodeTriop {
    // Verilog string.substr()
public:
    AstSubstrN(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* ths)
        : ASTGEN_SUPER_SubstrN(fl, lhsp, rhsp, ths) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(SubstrN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs, const V3Number& rhs,
                               const V3Number& ths) override {
        out.opSubstrN(lhs, rhs, ths);
    }
    virtual string name() const override { return "substr"; }
    virtual string emitVerilog() override { return "%k(%l.substr(%r,%t))"; }
    virtual string emitC() override { return "VL_SUBSTR_N(%li,%ri,%ti)"; }
    virtual string emitSimpleOperator() override { return ""; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool cleanRhs() const override { return true; }
    virtual bool cleanThs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool sizeMattersRhs() const override { return false; }
    virtual bool sizeMattersThs() const override { return false; }
};

// === AstNodeCond ===
class AstCond final : public AstNodeCond {
    // Conditional ?: statement
    // Parents:  MATH
    // Children: MATH
public:
    AstCond(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : ASTGEN_SUPER_Cond(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(Cond)
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) override {
        return new AstCond(this->fileline(), condp, expr1p, expr2p);
    }
};
class AstCondBound final : public AstNodeCond {
    // Conditional ?: statement, specially made for safety checking of array bounds
    // Parents:  MATH
    // Children: MATH
public:
    AstCondBound(FileLine* fl, AstNode* condp, AstNode* expr1p, AstNode* expr2p)
        : ASTGEN_SUPER_CondBound(fl, condp, expr1p, expr2p) {}
    ASTNODE_NODE_FUNCS(CondBound)
    virtual AstNode* cloneType(AstNode* condp, AstNode* expr1p, AstNode* expr2p) override {
        return new AstCondBound(this->fileline(), condp, expr1p, expr2p);
    }
};

// === AstNodeUniop ===
class AstAtoN final : public AstNodeUniop {
    // string.atoi(), atobin(), atohex(), atooct(), atoireal()
public:
    enum FmtType { ATOI = 10, ATOHEX = 16, ATOOCT = 8, ATOBIN = 2, ATOREAL = -1 };

private:
    const FmtType m_fmt;  // Operation type
public:
    AstAtoN(FileLine* fl, AstNode* lhsp, FmtType fmt)
        : ASTGEN_SUPER_AtoN(fl, lhsp)
        , m_fmt{fmt} {
        fmt == ATOREAL ? dtypeSetDouble() : dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(AtoN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAtoN(lhs, m_fmt);
    }
    virtual string name() const override {
        switch (m_fmt) {
        case ATOI: return "atoi";
        case ATOHEX: return "atohex";
        case ATOOCT: return "atooct";
        case ATOBIN: return "atobin";
        case ATOREAL: return "atoreal";
        default: V3ERROR_NA;
        }
    }
    virtual string emitVerilog() override { return "%l." + name() + "()"; }
    virtual string emitC() override {
        switch (m_fmt) {
        case ATOI: return "VL_ATOI_N(%li, 10)";
        case ATOHEX: return "VL_ATOI_N(%li, 16)";
        case ATOOCT: return "VL_ATOI_N(%li, 8)";
        case ATOBIN: return "VL_ATOI_N(%li, 2)";
        case ATOREAL: return "std::atof(%li.c_str())";
        default: V3ERROR_NA;
        }
    }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    FmtType format() const { return m_fmt; }
};
class AstBitsToRealD final : public AstNodeUniop {
public:
    AstBitsToRealD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_BitsToRealD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(BitsToRealD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opBitsToRealD(lhs);
    }
    virtual string emitVerilog() override { return "%f$bitstoreal(%l)"; }
    virtual string emitC() override { return "VL_CVT_D_Q(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstCCast final : public AstNodeUniop {
    // Cast to C-based data type
private:
    int m_size;

public:
    AstCCast(FileLine* fl, AstNode* lhsp, int setwidth, int minwidth = -1)
        : ASTGEN_SUPER_CCast(fl, lhsp) {
        m_size = setwidth;
        if (setwidth) {
            if (minwidth == -1) minwidth = setwidth;
            dtypeSetLogicUnsized(setwidth, minwidth, VSigning::UNSIGNED);
        }
    }
    AstCCast(FileLine* fl, AstNode* lhsp, AstNode* typeFromp)
        : ASTGEN_SUPER_CCast(fl, lhsp) {
        dtypeFrom(typeFromp);
        m_size = width();
    }
    ASTNODE_NODE_FUNCS(CCast)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    virtual string emitVerilog() override { return "%f$_CAST(%l)"; }
    virtual string emitC() override { return "VL_CAST_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }  // Special cased in V3Cast
    virtual bool same(const AstNode* samep) const override {
        return size() == static_cast<const AstCCast*>(samep)->size();
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    //
    int size() const { return m_size; }
};
class AstCLog2 final : public AstNodeUniop {
public:
    AstCLog2(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CLog2(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(CLog2)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opCLog2(lhs); }
    virtual string emitVerilog() override { return "%f$clog2(%l)"; }
    virtual string emitC() override { return "VL_CLOG2_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
};
class AstCountOnes final : public AstNodeUniop {
    // Number of bits set in vector
public:
    AstCountOnes(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CountOnes(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CountOnes)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opCountOnes(lhs);
    }
    virtual string emitVerilog() override { return "%f$countones(%l)"; }
    virtual string emitC() override { return "VL_COUNTONES_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
};
class AstCvtPackString final : public AstNodeUniop {
    // Convert to Verilator Packed String (aka verilog "string")
public:
    AstCvtPackString(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CvtPackString(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(CvtPackString)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$_CAST(%l)"; }
    virtual string emitC() override { return "VL_CVT_PACK_STR_N%lq(%lW, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstExtend final : public AstNodeUniop {
    // Expand a value into a wider entity by 0 extension.  Width is implied from nodep->width()
public:
    AstExtend(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Extend(fl, lhsp) {}
    AstExtend(FileLine* fl, AstNode* lhsp, int width)
        : ASTGEN_SUPER_Extend(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(Extend)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opAssign(lhs); }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { return "VL_EXTEND_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    virtual int instrCount() const override { return 0; }
};
class AstExtendS final : public AstNodeUniop {
    // Expand a value into a wider entity by sign extension.  Width is implied from nodep->width()
public:
    AstExtendS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_ExtendS(fl, lhsp) {}
    AstExtendS(FileLine* fl, AstNode* lhsp, int width)
        // Important that widthMin be correct, as opExtend requires it after V3Expand
        : ASTGEN_SUPER_ExtendS(fl, lhsp) {
        dtypeSetLogicSized(width, VSigning::UNSIGNED);
    }
    ASTNODE_NODE_FUNCS(ExtendS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opExtendS(lhs, lhsp()->widthMinV());
    }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { return "VL_EXTENDS_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override {
        return false;  // Because the EXTEND operator self-casts
    }
    virtual int instrCount() const override { return 0; }
    virtual bool signedFlavor() const override { return true; }
};
class AstFEof final : public AstNodeUniop {
public:
    AstFEof(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_FEof(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FEof)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$feof(%l)"; }
    virtual string emitC() override { return "(%li ? feof(VL_CVT_I_FP(%li)) : true)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 16; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};
class AstFGetC final : public AstNodeUniop {
public:
    AstFGetC(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_FGetC(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FGetC)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%f$fgetc(%l)"; }
    // Non-existent filehandle returns EOF
    virtual string emitC() override { return "(%li ? fgetc(VL_CVT_I_FP(%li)) : -1)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 64; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    AstNode* filep() const { return lhsp(); }
};
class AstISToRD final : public AstNodeUniop {
    // $itor where lhs is signed
public:
    AstISToRD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_ISToRD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(ISToRD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opISToRD(lhs); }
    virtual string emitVerilog() override { return "%f$itor($signed(%l))"; }
    virtual string emitC() override { return "VL_ISTOR_D_%lq(%lw, %li)"; }
    virtual bool emitCheckMaxWords() override { return true; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstIToRD final : public AstNodeUniop {
    // $itor where lhs is unsigned
public:
    AstIToRD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_IToRD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(IToRD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opIToRD(lhs); }
    virtual string emitVerilog() override { return "%f$itor(%l)"; }
    virtual string emitC() override { return "VL_ITOR_D_%lq(%lw, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstIsUnbounded final : public AstNodeUniop {
    // True if is unmbounded ($)
public:
    AstIsUnbounded(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_IsUnbounded(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(IsUnbounded)
    virtual void numberOperate(V3Number& out, const V3Number&) override {
        // Any constant isn't unbounded
        out.setZero();
    }
    virtual string emitVerilog() override { return "%f$isunbounded(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstIsUnknown final : public AstNodeUniop {
    // True if any unknown bits
public:
    AstIsUnknown(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_IsUnknown(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(IsUnknown)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opIsUnknown(lhs);
    }
    virtual string emitVerilog() override { return "%f$isunknown(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstLenN final : public AstNodeUniop {
    // Length of a string
public:
    AstLenN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_LenN(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(LenN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLenN(lhs); }
    virtual string emitVerilog() override { return "%f(%l)"; }
    virtual string emitC() override { return "VL_LEN_IN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstLogNot final : public AstNodeUniop {
public:
    AstLogNot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_LogNot(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(LogNot)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opLogNot(lhs); }
    virtual string emitVerilog() override { return "%f(! %l)"; }
    virtual string emitC() override { return "VL_LOGNOT_%nq%lq(%nw,%lw, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "!"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstNegate final : public AstNodeUniop {
public:
    AstNegate(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Negate(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Negate)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegate(lhs); }
    virtual string emitVerilog() override { return "%f(- %l)"; }
    virtual string emitC() override { return "VL_NEGATE_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
};
class AstNegateD final : public AstNodeUniop {
public:
    AstNegateD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_NegateD(fl, lhsp) {
        dtypeSetDouble();
    }
    ASTNODE_NODE_FUNCS(NegateD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNegateD(lhs); }
    virtual string emitVerilog() override { return "%f(- %l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { return "-"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
    virtual bool doubleFlavor() const override { return true; }
};
class AstNot final : public AstNodeUniop {
public:
    AstNot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Not(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(Not)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opNot(lhs); }
    virtual string emitVerilog() override { return "%f(~ %l)"; }
    virtual string emitC() override { return "VL_NOT_%lq(%lW, %P, %li)"; }
    virtual string emitSimpleOperator() override { return "~"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return true; }
};
class AstNullCheck final : public AstNodeUniop {
    // Return LHS after checking that LHS is non-null
    // Children: VarRef or something returning pointer
public:
    AstNullCheck(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_NullCheck(fl, lhsp) {
        dtypeFrom(lhsp);
    }
    ASTNODE_NODE_FUNCS(NullCheck)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual int instrCount() const override { return 1; }  // Rarely executes
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual string emitSimpleOperator() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};
class AstOneHot final : public AstNodeUniop {
    // True if only single bit set in vector
public:
    AstOneHot(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_OneHot(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(OneHot)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot(lhs); }
    virtual string emitVerilog() override { return "%f$onehot(%l)"; }
    virtual string emitC() override { return "VL_ONEHOT_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 4; }
};
class AstOneHot0 final : public AstNodeUniop {
    // True if only single bit, or no bits set in vector
public:
    AstOneHot0(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_OneHot0(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(OneHot0)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opOneHot0(lhs); }
    virtual string emitVerilog() override { return "%f$onehot0(%l)"; }
    virtual string emitC() override { return "VL_ONEHOT0_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 3; }
};
class AstRToIRoundS final : public AstNodeUniop {
    // Convert real to integer, with arbitrary sized output (not just "integer" format)
public:
    AstRToIRoundS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RToIRoundS(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(RToIRoundS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opRToIRoundS(lhs);
    }
    virtual string emitVerilog() override { return "%f$rtoi_rounded(%l)"; }
    virtual string emitC() override {
        return isWide() ? "VL_RTOIROUND_%nq_D(%nw, %P, %li)" : "VL_RTOIROUND_%nq_D(%li)";
    }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRToIS final : public AstNodeUniop {
    // $rtoi(lhs)
public:
    AstRToIS(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RToIS(fl, lhsp) {
        dtypeSetSigned32();
    }
    ASTNODE_NODE_FUNCS(RToIS)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRToIS(lhs); }
    virtual string emitVerilog() override { return "%f$rtoi(%l)"; }
    virtual string emitC() override { return "VL_RTOI_I_D(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRealToBits final : public AstNodeUniop {
public:
    AstRealToBits(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RealToBits(fl, lhsp) {
        dtypeSetUInt64();
    }
    ASTNODE_NODE_FUNCS(RealToBits)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opRealToBits(lhs);
    }
    virtual string emitVerilog() override { return "%f$realtobits(%l)"; }
    virtual string emitC() override { return "VL_CVT_Q_D(%li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return false; }  // Eliminated before matters
    virtual int instrCount() const override { return INSTR_COUNT_DBL; }
};
class AstRedAnd final : public AstNodeUniop {
public:
    AstRedAnd(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RedAnd(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedAnd)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedAnd(lhs); }
    virtual string emitVerilog() override { return "%f(& %l)"; }
    virtual string emitC() override { return "VL_REDAND_%nq%lq(%lw, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstRedOr final : public AstNodeUniop {
public:
    AstRedOr(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RedOr(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedOr)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedOr(lhs); }
    virtual string emitVerilog() override { return "%f(| %l)"; }
    virtual string emitC() override { return "VL_REDOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstRedXor final : public AstNodeUniop {
public:
    AstRedXor(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_RedXor(fl, lhsp) {
        dtypeSetBit();
    }
    ASTNODE_NODE_FUNCS(RedXor)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { out.opRedXor(lhs); }
    virtual string emitVerilog() override { return "%f(^ %l)"; }
    virtual string emitC() override { return "VL_REDXOR_%lq(%lW, %P, %li)"; }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override {
        const int w = lhsp()->width();
        return (w != 1 && w != 2 && w != 4 && w != 8 && w != 16);
    }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual int instrCount() const override { return 1 + V3Number::log2b(width()); }
};
class AstSigned final : public AstNodeUniop {
    // $signed(lhs)
public:
    AstSigned(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Signed(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTNODE_NODE_FUNCS(Signed)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    virtual string emitVerilog() override { return "%f$signed(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    virtual int instrCount() const override { return 0; }
};
class AstTimeImport final : public AstNodeUniop {
    // Take a constant that represents a time and needs conversion based on time units
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstTimeImport(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_TimeImport(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TimeImport)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override { V3ERROR_NA; }
    virtual string emitVerilog() override { return "%l"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }
    virtual bool sizeMattersLhs() const override { return false; }
    virtual void dump(std::ostream& str = std::cout) const override;
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstToLowerN final : public AstNodeUniop {
    // string.tolower()
public:
    AstToLowerN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_ToLowerN(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ToLowerN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opToLowerN(lhs);
    }
    virtual string emitVerilog() override { return "%l.tolower()"; }
    virtual string emitC() override { return "VL_TOLOWER_NN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstToUpperN final : public AstNodeUniop {
    // string.toupper()
public:
    AstToUpperN(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_ToUpperN(fl, lhsp) {
        dtypeSetString();
    }
    ASTNODE_NODE_FUNCS(ToUpperN)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opToUpperN(lhs);
    }
    virtual string emitVerilog() override { return "%l.toupper()"; }
    virtual string emitC() override { return "VL_TOUPPER_NN(%li)"; }
    virtual bool cleanOut() const override { return true; }
    virtual bool cleanLhs() const override { return true; }
    virtual bool sizeMattersLhs() const override { return false; }
};
class AstUnsigned final : public AstNodeUniop {
    // $unsigned(lhs)
public:
    AstUnsigned(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Unsigned(fl, lhsp) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTNODE_NODE_FUNCS(Unsigned)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.opAssign(lhs);
        out.isSigned(false);
    }
    virtual string emitVerilog() override { return "%f$unsigned(%l)"; }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return false; }
    virtual bool cleanLhs() const override { return false; }  // Eliminated before matters
    virtual bool sizeMattersLhs() const override { return true; }  // Eliminated before matters
    virtual int instrCount() const override { return 0; }
};

// === AstNodeSystemUniop ===
class AstAcosD final : public AstNodeSystemUniop {
public:
    AstAcosD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AcosD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AcosD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acos(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$acos(%l)"; }
    virtual string emitC() override { return "acos(%li)"; }
};
class AstAcoshD final : public AstNodeSystemUniop {
public:
    AstAcoshD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AcoshD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AcoshD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::acosh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$acosh(%l)"; }
    virtual string emitC() override { return "acosh(%li)"; }
};
class AstAsinD final : public AstNodeSystemUniop {
public:
    AstAsinD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AsinD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AsinD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asin(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$asin(%l)"; }
    virtual string emitC() override { return "asin(%li)"; }
};
class AstAsinhD final : public AstNodeSystemUniop {
public:
    AstAsinhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AsinhD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AsinhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::asinh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$asinh(%l)"; }
    virtual string emitC() override { return "asinh(%li)"; }
};
class AstAtanD final : public AstNodeSystemUniop {
public:
    AstAtanD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AtanD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AtanD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atan(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atan(%l)"; }
    virtual string emitC() override { return "atan(%li)"; }
};
class AstAtanhD final : public AstNodeSystemUniop {
public:
    AstAtanhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_AtanhD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(AtanhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::atanh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$atanh(%l)"; }
    virtual string emitC() override { return "atanh(%li)"; }
};
class AstCeilD final : public AstNodeSystemUniop {
public:
    AstCeilD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CeilD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CeilD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::ceil(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$ceil(%l)"; }
    virtual string emitC() override { return "ceil(%li)"; }
};
class AstCosD final : public AstNodeSystemUniop {
public:
    AstCosD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CosD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CosD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cos(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$cos(%l)"; }
    virtual string emitC() override { return "cos(%li)"; }
};
class AstCoshD final : public AstNodeSystemUniop {
public:
    AstCoshD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CoshD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(CoshD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::cosh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$cosh(%l)"; }
    virtual string emitC() override { return "cosh(%li)"; }
};
class AstExpD final : public AstNodeSystemUniop {
public:
    AstExpD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_ExpD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(ExpD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::exp(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$exp(%l)"; }
    virtual string emitC() override { return "exp(%li)"; }
};
class AstFloorD final : public AstNodeSystemUniop {
public:
    AstFloorD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_FloorD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(FloorD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::floor(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$floor(%l)"; }
    virtual string emitC() override { return "floor(%li)"; }
};
class AstLog10D final : public AstNodeSystemUniop {
public:
    AstLog10D(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Log10D(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(Log10D)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log10(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$log10(%l)"; }
    virtual string emitC() override { return "log10(%li)"; }
};
class AstLogD final : public AstNodeSystemUniop {
public:
    AstLogD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_LogD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(LogD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::log(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$ln(%l)"; }
    virtual string emitC() override { return "log(%li)"; }
};
class AstSinD final : public AstNodeSystemUniop {
public:
    AstSinD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SinD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SinD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sin(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sin(%l)"; }
    virtual string emitC() override { return "sin(%li)"; }
};
class AstSinhD final : public AstNodeSystemUniop {
public:
    AstSinhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SinhD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SinhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sinh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sinh(%l)"; }
    virtual string emitC() override { return "sinh(%li)"; }
};
class AstSqrtD final : public AstNodeSystemUniop {
public:
    AstSqrtD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SqrtD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(SqrtD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::sqrt(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$sqrt(%l)"; }
    virtual string emitC() override { return "sqrt(%li)"; }
};
class AstTanD final : public AstNodeSystemUniop {
public:
    AstTanD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_TanD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TanD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tan(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$tan(%l)"; }
    virtual string emitC() override { return "tan(%li)"; }
};
class AstTanhD final : public AstNodeSystemUniop {
public:
    AstTanhD(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_TanhD(fl, lhsp) {}
    ASTNODE_NODE_FUNCS(TanhD)
    virtual void numberOperate(V3Number& out, const V3Number& lhs) override {
        out.setDouble(std::tanh(lhs.toDouble()));
    }
    virtual string emitVerilog() override { return "%f$tanh(%l)"; }
    virtual string emitC() override { return "tanh(%li)"; }
};

// === AstNodeVarRef ===
class AstVarRef final : public AstNodeVarRef {
    // A reference to a variable (lvalue or rvalue)
public:
    AstVarRef(FileLine* fl, const string& name, const VAccess& access)
        : ASTGEN_SUPER_VarRef(fl, name, nullptr, access) {}
    // This form only allowed post-link because output/wire compression may
    // lead to deletion of AstVar's
    inline AstVarRef(FileLine* fl, AstVar* varp, const VAccess& access);
    // This form only allowed post-link (see above)
    inline AstVarRef(FileLine* fl, AstVarScope* varscp, const VAccess& access);
    ASTNODE_NODE_FUNCS(VarRef)
    virtual void dump(std::ostream& str) const override;
    bool same(const AstNode* samep) const override;
    inline bool same(const AstVarRef* samep) const;
    inline bool sameNoLvalue(AstVarRef* samep) const;
    virtual int instrCount() const override {
        return widthInstrs() * (access().isReadOrRW() ? INSTR_COUNT_LD : 1);
    }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
};
class AstVarXRef final : public AstNodeVarRef {
    // A VarRef to something in another module before AstScope.
    // Includes pin on a cell, as part of a ASSIGN statement to connect I/Os until AstScope
private:
    string m_dotted;  // Dotted part of scope the name()'ed reference is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
public:
    AstVarXRef(FileLine* fl, const string& name, const string& dotted, const VAccess& access)
        : ASTGEN_SUPER_VarXRef(fl, name, nullptr, access)
        , m_dotted{dotted} {}
    inline AstVarXRef(FileLine* fl, AstVar* varp, const string& dotted, const VAccess& access);
    ASTNODE_NODE_FUNCS(VarXRef)
    virtual void dump(std::ostream& str) const override;
    string dotted() const { return m_dotted; }
    void dotted(const string& dotted) { m_dotted = dotted; }
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    virtual string emitVerilog() override { V3ERROR_NA_RETURN(""); }
    virtual string emitC() override { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode* samep) const override {
        const AstVarXRef* asamep = static_cast<const AstVarXRef*>(samep);
        return (selfPointer() == asamep->selfPointer() && varp() == asamep->varp()
                && name() == asamep->name() && dotted() == asamep->dotted());
    }
};

#endif  // Guard
