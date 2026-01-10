// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing statements
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains all 'AstNode' sub-types that are statements.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODESTMT_H_
#define VERILATOR_V3ASTNODESTMT_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeStmt VL_NOT_FINAL : public AstNode {
    // Procedural statement
protected:
    AstNodeStmt(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeStmt;
    // METHODS
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
};
class AstNodeAssign VL_NOT_FINAL : public AstNodeStmt {
    // Iteration is in order, and we want rhsp to be visited first (which is the execution order)
    // @astgen op1 := rhsp : AstNodeExpr
    // @astgen op2 := lhsp : AstNodeExpr
    // @astgen op3 := timingControlp : Optional[AstNode]
protected:
    AstNodeAssign(VNType t, FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
                  AstNode* timingControlp = nullptr)
        : AstNodeStmt{t, fl} {
        this->rhsp(rhsp);
        this->lhsp(lhsp);
        this->timingControlp(timingControlp);
        dtypeFrom(lhsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeAssign;
    // Clone single node, just get same type back.
    virtual AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) = 0;
    bool hasDType() const override VL_MT_SAFE { return true; }
    virtual bool cleanRhs() const { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool sameNode(const AstNode*) const override { return true; }
    string verilogKwd() const override { return "="; }
    bool isTimingControl() const override { return timingControlp(); }
};
class AstNodeBlock VL_NOT_FINAL : public AstNodeStmt {
    // A Begin/fork block
    // Parents: statement
    // @astgen op1 := declsp : List[AstNode] // Declarations inside block
    // @astgen op2 := stmtsp : List[AstNode] // Sequential statements inside block
    string m_name;  // Name of block
    bool m_unnamed;  // Originally unnamed (name change does not affect this)
protected:
    AstNodeBlock(VNType t, FileLine* fl, const string& name)
        : AstNodeStmt{t, fl}
        , m_name{name}
        , m_unnamed{name == ""} {}

public:
    ASTGEN_MEMBERS_AstNodeBlock;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Block name
    void name(const string& name) override { m_name = name; }
    bool unnamed() const { return m_unnamed; }
};
class AstNodeCoverOrAssert VL_NOT_FINAL : public AstNodeStmt {
    // Cover or Assert
    // Parents:  {statement list}
    // @astgen op1 := propp : AstNode
    // @astgen op2 := sentreep : Optional[AstSenTree]
    // op3 used by some sub-types only
    // @astgen op4 := passsp: List[AstNode] // Statements when propp is passing/truthly
    string m_name;  // Name to report
    const VAssertType m_type;  // Assertion/cover type
    const VAssertDirectiveType m_directive;  // Assertion directive type

public:
    AstNodeCoverOrAssert(VNType t, FileLine* fl, AstNode* propp, AstNode* passsp, VAssertType type,
                         VAssertDirectiveType directive, const string& name = "")
        : AstNodeStmt{t, fl}
        , m_name{name}
        , m_type{type}
        , m_directive{directive} {
        this->propp(propp);
        addPasssp(passsp);
    }
    ASTGEN_MEMBERS_AstNodeCoverOrAssert;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool sameNode(const AstNode* samep) const override { return samep->name() == name(); }
    void name(const string& name) override { m_name = name; }
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    VAssertType type() const VL_MT_SAFE { return m_type; }
    VAssertDirectiveType directive() const { return m_directive; }
    bool immediate() const {
        return this->type().containsAny(VAssertType::SIMPLE_IMMEDIATE
                                        | VAssertType::OBSERVED_DEFERRED_IMMEDIATE
                                        | VAssertType::FINAL_DEFERRED_IMMEDIATE)
               || this->type() == VAssertType::INTERNAL;
    }
};
class AstNodeForeach VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := arrayp : AstNode
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstNodeForeach(VNType t, FileLine* fl, AstNode* arrayp, AstNode* stmtsp)
        : AstNodeStmt(t, fl) {
        this->arrayp(arrayp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstNodeForeach;
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstNodeIf VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := thensp : List[AstNode]
    // @astgen op3 := elsesp : List[AstNode]
    VBranchPred m_branchPred;  // Branch prediction as taken/untaken?
    bool m_isBoundsCheck;  // True if this if node is for assertion/bounds checking
protected:
    AstNodeIf(VNType t, FileLine* fl, AstNodeExpr* condp, AstNode* thensp, AstNode* elsesp)
        : AstNodeStmt{t, fl} {
        this->condp(condp);
        addThensp(thensp);
        addElsesp(elsesp);
        isBoundsCheck(false);
    }

public:
    ASTGEN_MEMBERS_AstNodeIf;
    bool isGateOptimizable() const override { return false; }
    bool isGateDedupable() const override { return true; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    void branchPred(VBranchPred flag) { m_branchPred = flag; }
    VBranchPred branchPred() const { return m_branchPred; }
    void isBoundsCheck(bool flag) { m_isBoundsCheck = flag; }
    bool isBoundsCheck() const { return m_isBoundsCheck; }
};
class AstNodeReadWriteMem VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := filenamep : AstNodeExpr
    // @astgen op2 := memp : AstNodeExpr
    // @astgen op3 := lsbp : Optional[AstNodeExpr]
    // @astgen op4 := msbp : Optional[AstNodeExpr]

    const bool m_isHex;  // readmemh, not readmemb
public:
    AstNodeReadWriteMem(VNType t, FileLine* fl, bool hex, AstNodeExpr* filenamep,
                        AstNodeExpr* memp, AstNodeExpr* lsbp, AstNodeExpr* msbp)
        : AstNodeStmt{t, fl}
        , m_isHex{hex} {
        this->filenamep(filenamep);
        this->memp(memp);
        this->lsbp(lsbp);
        this->msbp(msbp);
    }
    ASTGEN_MEMBERS_AstNodeReadWriteMem;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* samep) const override {
        return isHex() == VN_DBG_AS(samep, NodeReadWriteMem)->isHex();
    }
    bool isHex() const { return m_isHex; }
    virtual const char* cFuncPrefixp() const = 0;
};

// === Concrete node types =====================================================

// === AstNode ===
class AstCaseItem final : public AstNode {
    // Single item of AstCase/AstRandCase
    // @astgen op1 := condsp : List[AstNodeExpr]
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstCaseItem(FileLine* fl, AstNodeExpr* condsp, AstNode* stmtsp)
        : ASTGEN_SUPER_CaseItem(fl) {
        addCondsp(condsp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstCaseItem;
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
    bool isDefault() const { return condsp() == nullptr; }
};

// === AstNodeStmt ===
class AstAssertCtl final : public AstNodeStmt {
    // @astgen op1 := controlTypep : AstNodeExpr
    // @astgen op2 := assertTypesp : Optional[AstNodeExpr]
    // @astgen op3 := directiveTypesp : Optional[AstNodeExpr]
    // Type of assertcontrol task; either known from parser or from evaluated
    // controlTypep expression.
    VAssertCtlType m_ctlType;  // $assert keyword type (control_type)
    VAssertType m_assertTypes;  // Types of assertions affected
    VAssertDirectiveType m_directiveTypes;  // Types of directives affected

public:
    AstAssertCtl(FileLine* fl, VAssertCtlType ctlType, uint32_t assertType, uint32_t directiveType,
                 AstNodeExpr* levelp = nullptr, AstNodeExpr* itemsp = nullptr);
    AstAssertCtl(FileLine* fl, AstNodeExpr* controlTypep, AstNodeExpr* assertTypesp = nullptr,
                 AstNodeExpr* directiveTypep = nullptr, AstNodeExpr* levelp = nullptr,
                 AstNodeExpr* itemsp = nullptr);
    ASTGEN_MEMBERS_AstAssertCtl;
    string verilogKwd() const override { return m_ctlType.ascii(); }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    VAssertCtlType ctlType() const { return m_ctlType; }
    void ctlType(int32_t type) { m_ctlType = VAssertCtlType{type}; }
    VAssertType ctlAssertTypes() const { return m_assertTypes; }
    void ctlAssertTypes(VAssertType types) { m_assertTypes = types; }
    VAssertDirectiveType ctlDirectiveTypes() const { return m_directiveTypes; }
    void ctlDirectiveTypes(VAssertDirectiveType types) { m_directiveTypes = types; }
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
};
class AstBreak final : public AstNodeStmt {
public:
    explicit AstBreak(FileLine* fl)
        : ASTGEN_SUPER_Break(fl) {}
    ASTGEN_MEMBERS_AstBreak;
    string verilogKwd() const override { return "break"; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstCReset final : public AstNodeStmt {
    // Reset variable at startup
    // @astgen op1 := varrefp : AstVarRef
    const bool m_constructing;  // Previously cleared by constructor
public:
    AstCReset(FileLine* fl, AstVarRef* varrefp, bool constructing)
        : ASTGEN_SUPER_CReset(fl)
        , m_constructing{constructing} {
        this->varrefp(varrefp);
    }
    ASTGEN_MEMBERS_AstCReset;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool sameNode(const AstNode* samep) const override {
        return constructing() == VN_DBG_AS(samep, CReset)->constructing();
    }
    bool constructing() const { return m_constructing; }
};
class AstCReturn final : public AstNodeStmt {
    // C++ return from a function
    // @astgen op1 := lhsp : AstNodeExpr
public:
    AstCReturn(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_CReturn(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstCReturn;
    int instrCount() const override { return widthInstrs(); }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstCStmt final : public AstNodeStmt {
    // C statement emitted into output, with some arbitrary nodes interspersed
    // @astgen op1 := nodesp : List[AstNode<AstNodeStmt|AstNodeExpr|AstText>]

    static AstCStmt* profExecSection(FileLine* flp, const std::string& section, bool push) {
        // Compute the label
        std::string label;
        if (v3Global.opt.hierChild()) {
            label += v3Global.opt.topModule() + ":";
        } else if (!v3Global.opt.libCreate().empty()) {
            label += v3Global.opt.libCreate() + ":";
        }
        label += section;
        // The profiler statement
        std::string pStmt = "VL_EXEC_TRACE_ADD_RECORD(vlSymsp)";
        pStmt += push ? ".sectionPush" : ".sectionPop";
        pStmt += "(";
        if (push) pStmt += "\"" + label + "\"";
        pStmt += ");";
        // The debug statement
        std::string dStmt = "VL_DEBUG_IF(VL_DBG_MSGF(\"+    --prof-exec ";
        dStmt += push ? "sectionPush " : "sectionPop ";
        dStmt += label;
        dStmt += "\\n\"););";
        // Concatenate
        return new AstCStmt{flp, push ? pStmt + "\n" + dStmt : dStmt + "\n" + pStmt};
    }

public:
    explicit AstCStmt(FileLine* fl, const std::string& text = "")
        : ASTGEN_SUPER_CStmt(fl) {
        if (!text.empty()) add(text);
    }
    ASTGEN_MEMBERS_AstCStmt;
    bool isGateOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool sameNode(const AstNode*) const override { return true; }
    // Add some text, or a node to this statement
    void add(const std::string& text) { addNodesp(new AstText{fileline(), text}); }
    void add(AstNode* nodep) { addNodesp(nodep); }
    // Static factory methods for specific cases
    static AstCStmt* profExecSectionPush(FileLine* flp, const std::string& section) {
        return profExecSection(flp, section, true);
    }
    static AstCStmt* profExecSectionPop(FileLine* flp, const std::string& section) {
        return profExecSection(flp, section, false);
    }
};
class AstCStmtUser final : public AstNodeStmt {
    // User '$c' statement, also used for handling some AstSystemCSection.
    // Same as AstCStmt, with text tracking disabled.
    //
    // Note this cannot be modelled as AstStmtExpr(AstCExprUser) because the
    // latter would have an extra semicolon emitted, which might be undesirable.
    //
    // Use AstCStmt instead, unless the text is from user input.
    //
    // @astgen op1 := nodesp : List[AstNode<AstNodeExpr|AstText>]
    const bool m_fromDollarC;  // Is from source '$c', emit decoration
public:
    explicit AstCStmtUser(FileLine* fl, bool fromDollarC = false)
        : ASTGEN_SUPER_CStmtUser(fl)
        , m_fromDollarC{fromDollarC} {}
    ASTGEN_MEMBERS_AstCStmtUser;
    // METHODS
    bool isGateOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool sameNode(const AstNode*) const override { return true; }
    bool fromDollarC() const { return m_fromDollarC; }
    // Add some text, or a node to this statement
    void add(const std::string& text) { addNodesp(new AstText{fileline(), text}); }
    void add(AstNode* nodep) { addNodesp(nodep); }
};
class AstCase final : public AstNodeStmt {
    // Case statement
    // @astgen op1 := exprp : AstNodeExpr // Condition (scurtinee) expression
    // @astgen op2 := itemsp : List[AstCaseItem]
    // @astgen op3 := notParallelp : List[AstNode] // assertion code for non-full case's
    VCaseType m_casex;  // 0=case, 1=casex, 2=casez
    bool m_fullPragma = false;  // Synthesis full_case
    bool m_parallelPragma = false;  // Synthesis parallel_case
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstCase(FileLine* fl, VCaseType casex, AstNodeExpr* exprp, AstCaseItem* itemsp)
        : ASTGEN_SUPER_Case(fl)
        , m_casex{casex} {
        this->exprp(exprp);
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstCase;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    string verilogKwd() const override { return casez() ? "casez" : casex() ? "casex" : "case"; }
    bool sameNode(const AstNode* samep) const override {
        return m_casex == VN_DBG_AS(samep, Case)->m_casex;
    }
    bool casex() const { return m_casex == VCaseType::CT_CASEX; }
    bool casez() const { return m_casex == VCaseType::CT_CASEZ; }
    bool caseInside() const { return m_casex == VCaseType::CT_CASEINSIDE; }
    bool caseSimple() const { return m_casex == VCaseType::CT_CASE; }
    void caseInsideSet() { m_casex = VCaseType::CT_CASEINSIDE; }
    bool fullPragma() const { return m_fullPragma; }
    void fullPragma(bool flag) { m_fullPragma = flag; }
    bool parallelPragma() const { return m_parallelPragma; }
    void parallelPragma(bool flag) { m_parallelPragma = flag; }
    bool uniquePragma() const { return m_uniquePragma; }
    void uniquePragma(bool flag) { m_uniquePragma = flag; }
    bool unique0Pragma() const { return m_unique0Pragma; }
    void unique0Pragma(bool flag) { m_unique0Pragma = flag; }
    bool priorityPragma() const { return m_priorityPragma; }
    void priorityPragma(bool flag) { m_priorityPragma = flag; }
    string pragmaString() const;
};
class AstComment final : public AstNodeStmt {
    // Some comment to put into the output stream
    const string m_name;  // Text of comment
    const bool m_showAt;  // Show "at <fileline>"
public:
    AstComment(FileLine* fl, const string& name, bool showAt = false)
        : ASTGEN_SUPER_Comment(fl)
        , m_name{name}
        , m_showAt{showAt} {}
    ASTGEN_MEMBERS_AstComment;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Text
    bool sameNode(const AstNode* samep) const override { return true; }  // Ignore name in comments
    virtual bool showAt() const { return m_showAt; }
};
class AstConstraintExpr final : public AstNodeStmt {
    // Constraint expression
    // @astgen op1 := exprp : AstNodeExpr
    bool m_isDisableSoft = false;  // Disable soft constraint expression
    bool m_isSoft = false;  // Soft constraint expression
public:
    AstConstraintExpr(FileLine* fl, AstNodeExpr* exprp)
        : ASTGEN_SUPER_ConstraintExpr(fl) {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstConstraintExpr;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    bool isDisableSoft() const { return m_isDisableSoft; }
    void isDisableSoft(bool flag) { m_isDisableSoft = flag; }
    bool isSoft() const { return m_isSoft; }
    void isSoft(bool flag) { m_isSoft = flag; }
};
class AstConstraintUnique final : public AstNodeStmt {
    // Constraint unique statement
    // @astgen op1 := rangesp : List[AstNode]
public:
    AstConstraintUnique(FileLine* fl, AstNode* rangesp)
        : ASTGEN_SUPER_ConstraintUnique(fl) {
        addRangesp(rangesp);
    }
    ASTGEN_MEMBERS_AstConstraintUnique;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstContinue final : public AstNodeStmt {
public:
    explicit AstContinue(FileLine* fl)
        : ASTGEN_SUPER_Continue(fl) {}
    ASTGEN_MEMBERS_AstContinue;
    string verilogKwd() const override { return "continue"; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstCoverInc final : public AstNodeStmt {
    // Coverage analysis point; increment coverage count
    // @astgen op1 := toggleExprp : Optional[AstNodeExpr]  // [After V3Clock]
    // @astgen op2 := toggleCovExprp : Optional[AstNodeExpr]  // [After V3Clock]
    // These are expressions to which the node corresponds. Used only in toggle coverage
    //
    // @astgen ptr := m_declp : AstNodeCoverDecl  // [After V3CoverageJoin] Declaration
public:
    AstCoverInc(FileLine* fl, AstNodeCoverDecl* declp)
        : ASTGEN_SUPER_CoverInc(fl)
        , m_declp{declp} {}
    ASTGEN_MEMBERS_AstCoverInc;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    bool sameNode(const AstNode* samep) const override {
        return declp() == VN_DBG_AS(samep, CoverInc)->declp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    bool isPure() override { return false; }
    AstNodeCoverDecl* declp() const { return m_declp; }  // Where defined
};
class AstCoverToggle final : public AstNodeStmt {
    // Toggle analysis of given signal
    // Parents:  MODULE
    // @astgen op1 := incp : AstCoverInc
    // @astgen op2 := origp : AstNodeExpr
    // @astgen op3 := changep : AstNodeExpr
public:
    AstCoverToggle(FileLine* fl, AstCoverInc* incp, AstNodeExpr* origp, AstNodeExpr* changep)
        : ASTGEN_SUPER_CoverToggle(fl) {
        this->incp(incp);
        this->origp(origp);
        this->changep(changep);
    }
    ASTGEN_MEMBERS_AstCoverToggle;
    int instrCount() const override { return 3 + INSTR_COUNT_BRANCH + INSTR_COUNT_LD; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return true; }
    bool isOutputter() override {
        return false;  // Though the AstCoverInc under this is an outputter
    }
    // but isPure()  true
};
class AstDelay final : public AstNodeStmt {
    // Delay statement
    // @astgen op1 := lhsp : AstNodeExpr // Delay value
    // @astgen op2 := stmtsp : List[AstNode] // Statements under delay
    VTimescale m_timeunit;  // Delay's time unit
    const bool m_isCycle;  // True if it is a cycle delay

public:
    AstDelay(FileLine* fl, AstNodeExpr* lhsp, bool isCycle)
        : ASTGEN_SUPER_Delay(fl)
        , m_isCycle{isCycle} {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstDelay;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool isTimingControl() const override { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
    bool isCycleDelay() const { return m_isCycle; }
};
class AstDisable final : public AstNodeStmt {
    // @astgen op1 := targetRefp : Optional[AstNodeExpr]  // Reference to link in V3LinkDot
    // @astgen ptr := m_targetp : Optional[AstNode]  // Task or block after V3LinkDot
public:
    AstDisable(FileLine* fl, AstNodeExpr* targetRefp)
        : ASTGEN_SUPER_Disable(fl) {
        this->targetRefp(targetRefp);
    }
    ASTGEN_MEMBERS_AstDisable;
    const char* broken() const override;
    void dump(std::ostream& str) const override;
    void targetp(AstNode* nodep) { m_targetp = nodep; }
    AstNode* targetp() const { return m_targetp; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstDisableFork final : public AstNodeStmt {
    // A "disable fork" statement
public:
    explicit AstDisableFork(FileLine* fl)
        : ASTGEN_SUPER_DisableFork(fl) {}
    ASTGEN_MEMBERS_AstDisableFork;
};
class AstDisplay final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := fmtp : AstSFormatF
    // @astgen op2 := filep : Optional[AstNodeExpr] // file (must resolve to a VarRef)
    VDisplayType m_displayType;

public:
    AstDisplay(FileLine* fl, VDisplayType dispType, const string& text, AstNodeExpr* filep,
               AstNodeExpr* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        fmtp(new AstSFormatF{fl, text, true, exprsp, missingArgChar});
        this->filep(filep);
    }
    AstDisplay(FileLine* fl, VDisplayType dispType, AstNodeExpr* filep, AstNodeExpr* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        fmtp(new AstSFormatF{fl, AstSFormatF::NoFormat{}, exprsp, missingArgChar});
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstDisplay;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    string verilogKwd() const override {
        return (filep() ? "$f"s + string{displayType().ascii()}
                        : "$"s + string{displayType().ascii()});
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* samep) const override {
        return displayType() == VN_DBG_AS(samep, Display)->displayType();
    }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    VDisplayType displayType() const { return m_displayType; }
    void displayType(VDisplayType type) { m_displayType = type; }
    // * = Add a newline for $display
    bool addNewline() const { return displayType().addNewline(); }
};
class AstDumpCtl final : public AstNodeStmt {
    // $dumpon etc
    // Parents: expr
    // @astgen op1 := exprp : Optional[AstNodeExpr] // Expression based on type of statement
    const VDumpCtlType m_ctlType;  // Type of operation
public:
    AstDumpCtl(FileLine* fl, VDumpCtlType ctlType, AstNodeExpr* exprp = nullptr)
        : ASTGEN_SUPER_DumpCtl(fl)
        , m_ctlType{ctlType} {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstDumpCtl;
    string verilogKwd() const override { return ctlType().ascii(); }
    bool isGateOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    virtual bool cleanOut() const { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    VDumpCtlType ctlType() const { return m_ctlType; }
};
class AstEventControl final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := sentreep : Optional[AstSenTree]
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstEventControl(FileLine* fl, AstSenTree* sentreep, AstNode* stmtsp)
        : ASTGEN_SUPER_EventControl(fl) {
        this->sentreep(sentreep);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstEventControl;
    string verilogKwd() const override { return "@(%l) %r"; }
    bool isTimingControl() const override { return true; }
    int instrCount() const override { return 0; }
};
class AstExecGraph final : public AstNodeStmt {
    // For parallel execution, this node contains a dependency graph. Each
    // vertex in the graph is an ExecMTask, which includes a function that
    // holds the sequential body of the mtask.
    //
    // The location where AstExecGraph appears as a procedural statement is
    // where the parallel graph will be executed. Execution proceeds after
    // the AstExecGraph when all threads have joined.
    //
    // For code analysis purposes after scheduling, we keep a call to each
    // MTask function as children of the AstExecGraph in 'stmtsp'. These
    // are in a topological order so they represent a valid sequential
    // execution of the graph. In `V3ExecGraph::implement`, we replace these
    // statements with statements that dispatch to the thread pool for
    // parallel execution.
    // @astgen op1 := stmtsp : List[AstNode]
    V3Graph* const m_depGraphp;  // contains ExecMTask vertices
    const string m_name;  // Name of this AstExecGraph (for uniqueness at code generation)

public:
    explicit AstExecGraph(FileLine* fl, const string& name) VL_MT_DISABLED;
    ~AstExecGraph() override;
    ASTGEN_MEMBERS_AstExecGraph;
    void cloneRelink() override { V3ERROR_NA; }  // Not cloneable
    const char* broken() const override;
    string name() const override VL_MT_STABLE { return m_name; }
    V3Graph* depGraphp() { return m_depGraphp; }
    const V3Graph* depGraphp() const { return m_depGraphp; }
};
class AstFClose final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := filep : AstNodeExpr // file (must be a VarRef)
public:
    AstFClose(FileLine* fl, AstNodeExpr* filep)
        : ASTGEN_SUPER_FClose(fl) {
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstFClose;
    string verilogKwd() const override { return "$fclose"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstFFlush final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := filep : Optional[AstNodeExpr] // file (must be a VarRef)
public:
    AstFFlush(FileLine* fl, AstNodeExpr* filep)
        : ASTGEN_SUPER_FFlush(fl) {
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstFFlush;
    string verilogKwd() const override { return "$fflush"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstFinish final : public AstNodeStmt {
public:
    explicit AstFinish(FileLine* fl)
        : ASTGEN_SUPER_Finish(fl) {}
    ASTGEN_MEMBERS_AstFinish;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    int instrCount() const override { return 0; }  // Rarely executes
    bool sameNode(const AstNode* samep) const override { return fileline() == samep->fileline(); }
};
class AstFinishFork final : public AstNodeStmt {
    // $finish in fork
public:
    explicit AstFinishFork(FileLine* fl)
        : ASTGEN_SUPER_FinishFork(fl) {}
    ASTGEN_MEMBERS_AstFinishFork;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    int instrCount() const override { return 0; }  // Rarely executes
    bool sameNode(const AstNode* samep) const override { return fileline() == samep->fileline(); }
};
class AstFireEvent final : public AstNodeStmt {
    // '-> _' and '->> _' event trigger statements
    // @astgen op1 := operandp : AstNodeExpr
    const bool m_delayed;  // Delayed (->>) vs non-delayed (->)
public:
    AstFireEvent(FileLine* fl, AstNodeExpr* operandp, bool delayed)
        : ASTGEN_SUPER_FireEvent(fl)
        , m_delayed{delayed} {
        this->operandp(operandp);
    }
    ASTGEN_MEMBERS_AstFireEvent;
    bool isDelayed() const { return m_delayed; }
};
class AstJumpBlock final : public AstNodeStmt {
    // Block of code that might contain AstJumpGo statements as children,
    // which when exectued branch to right after the referenced AstJumpBlock.
    // AstJumpBlocks can nest, and an AstJumpGo can reference any of the
    // enclosing AstJumpBlocks (can break out of mulitple levels).
    // Parents:  {statement list}
    // Children: {statement list, with JumpGo below}
    // @astgen op1 := stmtsp : List[AstNode]
    VIsCached m_purity;  // Pure state
public:
    // After construction must call ->labelp to associate with appropriate label
    AstJumpBlock(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_JumpBlock(fl) {
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstJumpBlock;
    int instrCount() const override { return 0; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool isPure() override;

private:
    bool getPurityRecurse() const;
};
class AstJumpGo final : public AstNodeStmt {
    // Branch to right after the referenced encloding AstJumpBlock
    // Parents:  statement, including the referenced AstJumpBlock
    // Children: none
    //
    // @astgen ptr := m_blockp : AstJumpBlock  // The AstJumpBlock we are branching after
public:
    AstJumpGo(FileLine* fl, AstJumpBlock* blockp)
        : ASTGEN_SUPER_JumpGo(fl)
        , m_blockp{blockp} {}
    ASTGEN_MEMBERS_AstJumpGo;
    const char* broken() const override;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool sameNode(const AstNode* samep) const override {
        return blockp() == VN_DBG_AS(samep, JumpGo)->blockp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
    AstJumpBlock* blockp() const { return m_blockp; }
};
class AstLoop final : public AstNodeStmt {
    // An inifinite loop, used to model all source level procedural loops.
    // Executes as:
    //  while (true) {
    //      stmtsp;
    //      // <- 'continue' inside 'stmtsp goes here
    //      contsp;
    //  }
    // 'contsp' is moved into 'stmtsp' in LinkJump when 'continue' statements are resovled.
    // @astgen op1 := stmtsp : List[AstNode]
    // @astgen op2 := contsp : List[AstNode] // Empty after LinkJump
    VOptionBool m_unroll;  // Full, none, or default unrolling
public:
    explicit AstLoop(FileLine* fl, AstNode* stmtsp = nullptr)
        : ASTGEN_SUPER_Loop(fl) {
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstLoop;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* thatp) const override {
        return m_unroll == VN_DBG_AS(thatp, Loop)->m_unroll;
    }
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    // ACCESSORS
    VOptionBool unroll() const { return m_unroll; }
    void unroll(const VOptionBool flag) { m_unroll = flag; }
};
class AstLoopTest final : public AstNodeStmt {
    // The condition test inside an AstLoop. If the condition is true,
    // execution continues after this AstLoopTest statement. If the condition
    // is false, control is transfered to after the corresponding AstLoop.
    // In other words: AstLoopTest is like a conditional 'break' statement,
    // which breaks out of the loop if the condition is false.
    // @astgen op1 := condp : AstNodeExpr  // The loop condition
    // @astgen ptr := m_loopp : AstLoop  // The corresponding AstLoop
public:
    AstLoopTest(FileLine* fl, AstLoop* loopp, AstNodeExpr* condp)
        : ASTGEN_SUPER_LoopTest(fl)
        , m_loopp{loopp} {
        this->condp(condp);
    }
    ASTGEN_MEMBERS_AstLoopTest;
    const char* broken() const override;
    void dump(std::ostream& str) const override;
    bool sameNode(const AstNode*) const override { return true; }
    bool isGateOptimizable() const override { return false; }
    bool isBrancher() const override { return true; }
    int instrCount() const override { return 0; }
    // ACCESSORS
    AstLoop* loopp() const { return m_loopp; }
};
class AstMonitorOff final : public AstNodeStmt {
    const bool m_off;  // Monitor off.  Using 0=on allows faster init and comparison

public:
    AstMonitorOff(FileLine* fl, bool off)
        : ASTGEN_SUPER_MonitorOff(fl)
        , m_off{off} {}
    ASTGEN_MEMBERS_AstMonitorOff;
    string verilogKwd() const override { return m_off ? "$monitoroff" : "$monitoron"; }
    bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    bool isPredictOptimizable() const override { return false; }  // Though deleted before opt
    bool isPure() override { return false; }  // Though deleted before opt
    bool isOutputter() override { return true; }  // Though deleted before opt
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool sameNode(const AstNode* samep) const override {
        return m_off == VN_DBG_AS(samep, MonitorOff)->m_off;
    }
    bool off() const { return m_off; }
};
class AstPExprClause final : public AstNodeStmt {
    const bool m_pass;  // True if will be replaced by passing assertion clause, false for
                        // assertion failure clause

public:
    ASTGEN_MEMBERS_AstPExprClause;
    explicit AstPExprClause(FileLine* fl, bool pass = true)
        : ASTGEN_SUPER_PExprClause(fl)
        , m_pass{pass} {}
    bool pass() const { return m_pass; }
};
class AstPrintTimeScale final : public AstNodeStmt {
    // Parents: stmtlist
    string m_name;  // Parent module name
    VTimescale m_timeunit;  // Parent module time unit
public:
    explicit AstPrintTimeScale(FileLine* fl)
        : ASTGEN_SUPER_PrintTimeScale(fl) {}
    ASTGEN_MEMBERS_AstPrintTimeScale;
    void name(const string& name) override { m_name = name; }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string verilogKwd() const override { return "$printtimescale"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstRSBreak final : public AstNodeStmt {
    // randsequence break
public:
    explicit AstRSBreak(FileLine* fl)
        : ASTGEN_SUPER_RSBreak(fl) {}
    ASTGEN_MEMBERS_AstRSBreak;
    string verilogKwd() const override { return "break"; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstRSProd final : public AstNodeStmt {
    // randomsequence production, under a AstRandSequence
    // @astgen op1 := fvarp : Optional[AstVar]
    // @astgen op2 := portsp : List[AstNode]
    // @astgen op3 := rulesp : List[AstRSRule]
    string m_name;  // Name of block, or "" to use first production
public:
    AstRSProd(FileLine* fl, const string& name, AstNode* portsp, AstRSRule* rulesp)
        : ASTGEN_SUPER_RSProd(fl)
        , m_name{name} {
        addPortsp(portsp);
        addRulesp(rulesp);
    }
    ASTGEN_MEMBERS_AstRSProd;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    string name() const override VL_MT_STABLE { return m_name; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
};
class AstRSProdItem final : public AstNodeStmt {
    // randomsquence production item
    // @astgen op1 := argsp : List[AstNodeExpr]
    // @astgen ptr := m_prodp : Optional[AstRSProd]  // Pointer to production
    string m_name;  // Name of block, or "" to use first production
public:
    AstRSProdItem(FileLine* fl, const string& name, AstNodeExpr* argsp)
        : ASTGEN_SUPER_RSProdItem(fl)
        , m_name{name} {
        addArgsp(argsp);
    }
    ASTGEN_MEMBERS_AstRSProdItem;
    string name() const override VL_MT_STABLE { return m_name; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    AstRSProd* prodp() const { return m_prodp; }
    void prodp(AstRSProd* nodep) { m_prodp = nodep; }
};
class AstRSProdList final : public AstNodeStmt {
    // randomsquence production list
    // @astgen op1 := weightp : Optional[AstNodeExpr]
    // @astgen op2 := prodsp : List[AstNode]
    bool m_randJoin = false;  // Is rand join'ed
public:
    AstRSProdList(FileLine* fl, AstNodeExpr* weightp, AstNode* prodsp)
        : ASTGEN_SUPER_RSProdList(fl) {
        this->weightp(weightp);
        addProdsp(prodsp);
    }
    ASTGEN_MEMBERS_AstRSProdList;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool randJoin() const { return m_randJoin; }
    void randJoin(bool flag) { m_randJoin = flag; }
};
class AstRSReturn final : public AstNodeStmt {
    // randsequence return
public:
    explicit AstRSReturn(FileLine* fl)
        : ASTGEN_SUPER_RSReturn(fl) {}
    ASTGEN_MEMBERS_AstRSReturn;
    string verilogKwd() const override { return "return"; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstRSRule final : public AstNodeStmt {
    // randomsquence rule
    // @astgen op1 := weightp : Optional[AstNodeExpr]
    // @astgen op2 := prodlistsp : List[AstRSProdList]
    // @astgen op3 := weightStmtsp : List[AstNode]
public:
    AstRSRule(FileLine* fl, AstNodeExpr* weightp, AstRSProdList* prodlistsp, AstNode* weightStmtsp)
        : ASTGEN_SUPER_RSRule(fl) {
        this->weightp(weightp);
        addProdlistsp(prodlistsp);
        addWeightStmtsp(weightStmtsp);
    }
    ASTGEN_MEMBERS_AstRSRule;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
};
class AstRandCase final : public AstNodeStmt {
    // @astgen op2 := itemsp : List[AstCaseItem]
public:
    AstRandCase(FileLine* fl, AstCaseItem* itemsp)
        : ASTGEN_SUPER_RandCase(fl) {
        addItemsp(itemsp);
        v3Global.useRandomizeMethods(true);
    }
    ASTGEN_MEMBERS_AstRandCase;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
};
class AstRandSequence final : public AstNodeStmt {
    // @astgen op2 := prodsp : List[AstRSProd]
    // @astgen ptr := m_prodp : Optional[AstRSProd]  // Pointer to start production (if any)
    string m_name;  // Created unique name
    string m_start;  // Name of start production, or "" to use first production
public:
    AstRandSequence(FileLine* fl, const string& start, AstRSProd* prodsp)
        : ASTGEN_SUPER_RandSequence(fl)
        , m_start{start} {
        addProdsp(prodsp);
    }
    ASTGEN_MEMBERS_AstRandSequence;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Block name
    void name(const string& name) override { m_name = name; }
    string start() const VL_MT_STABLE { return m_start; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    AstRSProd* prodp() const { return m_prodp; }
    void prodp(AstRSProd* nodep) { m_prodp = nodep; }
};
class AstRelease final : public AstNodeStmt {
    // Procedural 'release' statement
    // @astgen op1 := lhsp : AstNodeExpr
public:
    AstRelease(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_Release(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstRelease;
};
class AstRepeat final : public AstNodeStmt {
    // @astgen op1 := countp : AstNodeExpr
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstRepeat(FileLine* fl, AstNodeExpr* countp, AstNode* stmtsp)
        : ASTGEN_SUPER_Repeat(fl) {
        this->countp(countp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstRepeat;
    bool isGateOptimizable() const override { return false; }  // Not relevant - converted to FOR
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstReturn final : public AstNodeStmt {
    // @astgen op1 := lhsp : Optional[AstNodeExpr]
public:
    explicit AstReturn(FileLine* fl, AstNodeExpr* lhsp = nullptr)
        : ASTGEN_SUPER_Return(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstReturn;
    string verilogKwd() const override { return "return"; }
    bool isBrancher() const override { V3ERROR_NA_RETURN(true); }  // Node removed early
};
class AstSFormat final : public AstNodeStmt {
    // Parents: statement container
    // @astgen op1 := fmtp : AstSFormatF
    // @astgen op2 := lhsp : AstNodeExpr
public:
    AstSFormat(FileLine* fl, AstNodeExpr* lhsp, const string& text, AstNodeExpr* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        fmtp(new AstSFormatF{fl, text, true, exprsp, missingArgChar});
        this->lhsp(lhsp);
    }
    AstSFormat(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        fmtp(new AstSFormatF{fl, AstSFormatF::NoFormat{}, exprsp, missingArgChar});
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstSFormat;
    const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    string verilogKwd() const override { return "$sformat"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return true; }
    bool isPure() override { return true; }
    bool isOutputter() override { return false; }
    virtual bool cleanOut() const { return false; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstSetuphold final : public AstNodeStmt {
    // Verilog $setuphold
    // @astgen op1 := refevp : AstNodeExpr
    // @astgen op2 := dataevp : AstNodeExpr
    // @astgen op3 := delrefp : Optional[AstNodeExpr]
    // @astgen op4 := deldatap : Optional[AstNodeExpr]
public:
    AstSetuphold(FileLine* fl, AstNodeExpr* refevp, AstNodeExpr* dataevp,
                 AstNodeExpr* delrefp = nullptr, AstNodeExpr* deldatap = nullptr)
        : ASTGEN_SUPER_Setuphold(fl) {
        this->refevp(refevp);
        this->dataevp(dataevp);
        this->delrefp(delrefp);
        this->deldatap(deldatap);
    }
    ASTGEN_MEMBERS_AstSetuphold;
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstSplitPlaceholder final : public AstNodeStmt {
public:
    // Dummy node used within V3Split; never exists outside of V3Split.
    explicit AstSplitPlaceholder(FileLine* fl)
        : ASTGEN_SUPER_SplitPlaceholder(fl) {}
    ASTGEN_MEMBERS_AstSplitPlaceholder;
};
class AstStackTraceT final : public AstNodeStmt {
    // $stacktrace used as task
public:
    explicit AstStackTraceT(FileLine* fl)
        : ASTGEN_SUPER_StackTraceT(fl) {}
    ASTGEN_MEMBERS_AstStackTraceT;
    string verilogKwd() const override { return "$stacktrace"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstStmtExpr final : public AstNodeStmt {
    // Expression in statement position
    // @astgen op1 := exprp : AstNodeExpr
public:
    AstStmtExpr(FileLine* fl, AstNodeExpr* exprp)
        : ASTGEN_SUPER_StmtExpr(fl) {
        this->exprp(exprp);
    }
    ASTGEN_MEMBERS_AstStmtExpr;
    // cppcheck-suppress uselessOverride
    bool isPure() override { return exprp()->isPure(); }
};
class AstStmtPragma final : public AstNodeStmt {
    // Pragma in statement position
    // @astgen op1 := pragp : AstPragma
public:
    AstStmtPragma(FileLine* fl, AstPragma* pragp)
        : ASTGEN_SUPER_StmtPragma(fl) {
        this->pragp(pragp);
    }
    ASTGEN_MEMBERS_AstStmtPragma;
};
class AstStop final : public AstNodeStmt {
    const bool m_isFatal;  // $fatal not $stop
public:
    AstStop(FileLine* fl, bool isFatal)
        : ASTGEN_SUPER_Stop(fl)
        , m_isFatal{isFatal} {}
    ASTGEN_MEMBERS_AstStop;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    int instrCount() const override { return 0; }  // Rarely executes
    bool sameNode(const AstNode* samep) const override { return fileline() == samep->fileline(); }
    string emitVerilog() const { return m_isFatal ? "$fatal" : "$stop"; }
    bool isFatal() const { return m_isFatal; }
};
class AstSystemT final : public AstNodeStmt {
    // $system used as task
    // @astgen op1 := lhsp : AstNodeExpr
public:
    AstSystemT(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_SystemT(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstSystemT;
    string verilogKwd() const override { return "$system"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstTimeFormat final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := unitsp : Optional[AstNodeExpr]
    // @astgen op2 := precisionp : Optional[AstNodeExpr]
    // @astgen op3 := suffixp : Optional[AstNodeExpr]
    // @astgen op4 := widthp : Optional[AstNodeExpr]
public:
    AstTimeFormat(FileLine* fl, AstNodeExpr* unitsp, AstNodeExpr* precisionp, AstNodeExpr* suffixp,
                  AstNodeExpr* widthp)
        : ASTGEN_SUPER_TimeFormat(fl) {
        this->unitsp(unitsp);
        this->precisionp(precisionp);
        this->suffixp(suffixp);
        this->widthp(widthp);
    }
    ASTGEN_MEMBERS_AstTimeFormat;
    string verilogKwd() const override { return "$timeformat"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
};
class AstTraceDecl final : public AstNodeStmt {
    // Trace point declaration
    // Separate from AstTraceInc; as a declaration can't be deleted
    // Parents:  {statement list}
    // Expression being traced - Moved to AstTraceInc by V3Trace
    // @astgen op1 := valuep : Optional[AstNodeExpr]
    uint32_t m_code{0};  // Trace identifier code
    uint32_t m_fidx{0};  // Trace function index
    const string m_showname;  // Name of variable
    const VNumRange m_bitRange;  // Property of var the trace details
    const VNumRange m_arrayRange;  // Property of var the trace details
    const VVarType m_varType;  // Type of variable (for localparam vs. param)
    const VDirection m_declDirection;  // Declared direction input/output etc
public:
    AstTraceDecl(FileLine* fl, const string& showname,
                 AstVar* varp,  // For input/output state etc
                 AstNodeExpr* valuep, const VNumRange& bitRange, const VNumRange& arrayRange)
        : ASTGEN_SUPER_TraceDecl(fl)
        , m_showname{showname}
        , m_bitRange{bitRange}
        , m_arrayRange{arrayRange}
        , m_varType{varp->varType()}
        , m_declDirection{varp->declDirection()} {
        dtypeFrom(valuep);
        this->valuep(valuep);
    }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return 100; }  // Large...
    ASTGEN_MEMBERS_AstTraceDecl;
    string name() const override VL_MT_STABLE { return m_showname; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool hasDType() const override VL_MT_SAFE { return true; }
    bool sameNode(const AstNode* samep) const override { return false; }
    string showname() const { return m_showname; }  // * = Var name
    // Details on what we're tracing
    uint32_t code() const { return m_code; }
    void code(uint32_t code) { m_code = code; }
    uint32_t fidx() const { return m_fidx; }
    void fidx(uint32_t fidx) { m_fidx = fidx; }
    uint32_t codeInc() const {
        return (m_arrayRange.ranged() ? m_arrayRange.elements() : 1)
               * valuep()->dtypep()->widthWords()
               * (VL_EDATASIZE / 32);  // A code is always 32-bits
    }
    const VNumRange& bitRange() const { return m_bitRange; }
    const VNumRange& arrayRange() const { return m_arrayRange; }
    VVarType varType() const { return m_varType; }
    VDirection declDirection() const { return m_declDirection; }
};
class AstTraceInc final : public AstNodeStmt {
    // Trace point dump
    // @astgen op1 := valuep : AstNodeExpr // Expression being traced (from decl)
    //
    // @astgen ptr := m_declp : AstTraceDecl  // Pointer to declaration
    const uint32_t m_baseCode;  // Trace code base value in function containing this AstTraceInc
    const VTraceType m_traceType;  // Is this a const/full/incremental dump

public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, VTraceType traceType, uint32_t baseCode = 0)
        : ASTGEN_SUPER_TraceInc(fl)
        , m_baseCode{baseCode}
        , m_traceType{traceType}
        , m_declp{declp} {
        dtypeFrom(declp);
        // Note: A clone is necessary (instead of using declp()->valuep()),
        // for insertion of local temporaries in V3Premit
        valuep(declp->valuep()->cloneTree(true));
    }
    ASTGEN_MEMBERS_AstTraceInc;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return 10 + 2 * INSTR_COUNT_LD; }
    bool hasDType() const override VL_MT_SAFE { return true; }
    bool sameNode(const AstNode* samep) const override {
        return declp() == VN_DBG_AS(samep, TraceInc)->declp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    bool isPure() override { return false; }
    AstTraceDecl* declp() const { return m_declp; }
    VTraceType traceType() const { return m_traceType; }
    uint32_t baseCode() const { return m_baseCode; }
};
class AstTracePopPrefix final : public AstNodeStmt {
public:
    explicit AstTracePopPrefix(FileLine* fl)
        : ASTGEN_SUPER_TracePopPrefix(fl) {}
    ASTGEN_MEMBERS_AstTracePopPrefix;
    bool sameNode(const AstNode* samep) const override { return false; }
};
class AstTracePushPrefix final : public AstNodeStmt {
    const string m_prefix;  // Prefix to add to signal names
    const VTracePrefixType m_prefixType;  // Type of prefix being pushed
public:
    AstTracePushPrefix(FileLine* fl, const string& prefix, VTracePrefixType prefixType)
        : ASTGEN_SUPER_TracePushPrefix(fl)
        , m_prefix{prefix}
        , m_prefixType{prefixType} {}
    ASTGEN_MEMBERS_AstTracePushPrefix;
    bool sameNode(const AstNode* samep) const override { return false; }
    string prefix() const { return m_prefix; }
    VTracePrefixType prefixType() const { return m_prefixType; }
};
class AstWait final : public AstNodeStmt {
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstWait(FileLine* fl, AstNodeExpr* condp, AstNode* stmtsp)
        : ASTGEN_SUPER_Wait(fl) {
        this->condp(condp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstWait;
    bool isTimingControl() const override { return true; }
};
class AstWaitFork final : public AstNodeStmt {
    // A "wait fork" statement
public:
    explicit AstWaitFork(FileLine* fl)
        : ASTGEN_SUPER_WaitFork(fl) {}
    ASTGEN_MEMBERS_AstWaitFork;
    bool isTimingControl() const override { return true; }
};

// === AstNodeAssign ===
class AstAssign final : public AstNodeAssign {
public:
    AstAssign(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
              AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_Assign(fl, lhsp, rhsp, timingControlp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstAssign;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        AstNode* const controlp = timingControlp() ? timingControlp()->cloneTree(false) : nullptr;
        return new AstAssign{fileline(), lhsp, rhsp, controlp};
    }
};
class AstAssignCont final : public AstNodeAssign {
    // Continuous procedural 'assign'.  See AstAssignW for non-procedural version.
public:
    AstAssignCont(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
                  AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_AssignCont(fl, lhsp, rhsp, timingControlp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_AstAssignCont;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        AstNode* const controlp = timingControlp() ? timingControlp()->cloneTree(false) : nullptr;
        return new AstAssignCont{fileline(), lhsp, rhsp, controlp};
    }
};
class AstAssignDly final : public AstNodeAssign {
public:
    AstAssignDly(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
                 AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_AssignDly(fl, lhsp, rhsp, timingControlp) {}
    ASTGEN_MEMBERS_AstAssignDly;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        AstNode* const controlp = timingControlp() ? timingControlp()->cloneTree(false) : nullptr;
        return new AstAssignDly{fileline(), lhsp, rhsp, controlp};
    }
    bool isGateOptimizable() const override { return false; }
    string verilogKwd() const override { return "<="; }
};
class AstAssignForce final : public AstNodeAssign {
    // Procedural 'force' statement
public:
    AstAssignForce(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AssignForce(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstAssignForce;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAssignForce{fileline(), lhsp, rhsp};
    }
};
class AstAssignW final : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
    // @astgen op4 := strengthSpecp : Optional[AstStrengthSpec]
public:
    AstAssignW(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp,
               AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_AssignW(fl, lhsp, rhsp, timingControlp) {}
    ASTGEN_MEMBERS_AstAssignW;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        AstNode* const controlp = timingControlp() ? timingControlp()->cloneTree(false) : nullptr;
        return new AstAssignW{fileline(), lhsp, rhsp, controlp};
    }
    bool isTimingControl() const override {
        return timingControlp() || lhsp()->exists([](const AstNodeVarRef* refp) {
            return refp->access().isWriteOrRW() && refp->varp()->delayp();
        });
    }
    AstDelay* getLhsNetDelay() const;
};

// === AstNodeBlock ===
class AstBegin final : public AstNodeBlock {
    // A 'begin'/'end' named block.
    bool m_needProcess : 1;  // Uses VlProcess
    const bool m_implied : 1;  // Not inserted by user
public:
    AstBegin(FileLine* fl, const string& name, AstNode* stmtsp, bool implied)
        : ASTGEN_SUPER_Begin(fl, name)
        , m_needProcess{false}
        , m_implied{implied} {
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstBegin;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    void setNeedProcess() { m_needProcess = true; }
    bool needProcess() const { return m_needProcess; }
    bool implied() const { return m_implied; }
};
class AstFork final : public AstNodeBlock {
    // A 'fork'/'join*' named block. Note that this is a strict superset of
    // AstBegin, and it does contain AstNodeBlock::stmtsp(), which are
    // statements that execute sequentially before the parallel statements are
    // spawned. This is necessary to implement things like local variable
    // initializers properly. The parallel statements inside the fork must all
    // be AstBegin, as lowering stages will introduce additional statements to
    // be executed sequentially within each fork branch.
    //
    // @astgen op3 := forksp : List[AstBegin]
    // @astgen op4 := parentProcessp : Optional[AstVarRef]
    const VJoinType m_joinType;  // Join keyword type
public:
    AstFork(FileLine* fl, VJoinType joinType, const string& name = "")
        : ASTGEN_SUPER_Fork(fl, name)
        , m_joinType{joinType} {}
    ASTGEN_MEMBERS_AstFork;
    bool isTimingControl() const override { return !joinType().joinNone(); }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    VJoinType joinType() const { return m_joinType; }
};

// === AstNodeCoverOrAssert ===
class AstAssert final : public AstNodeCoverOrAssert {
    // @astgen op3 := failsp: List[AstNode] // Statements when propp is failing/falsey

public:
    ASTGEN_MEMBERS_AstAssert;
    AstAssert(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp, VAssertType type,
              VAssertDirectiveType directive, const string& name = "")
        : ASTGEN_SUPER_Assert(fl, propp, passsp, type, directive, name) {
        addFailsp(failsp);
    }
    string verilogKwd() const override {
        return directive() == VAssertDirectiveType::ASSERT ? "assert" : "assume";
    }
};
class AstAssertIntrinsic final : public AstNodeCoverOrAssert {
    // A $cast or other compiler inserted assert, that must run even without --assert option
    // @astgen op3 := failsp: List[AstNode] // Statements when propp is failing/falsey
public:
    ASTGEN_MEMBERS_AstAssertIntrinsic;
    AstAssertIntrinsic(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp,
                       const string& name = "")
        // Intrinsic asserts are always enabled thus 'type' field is set to INTERNAL.
        : ASTGEN_SUPER_AssertIntrinsic(fl, propp, passsp, VAssertType::INTERNAL,
                                       VAssertDirectiveType::INTRINSIC, name) {
        addFailsp(failsp);
    }
    string verilogKwd() const override { return "assert"; }
};
class AstCover final : public AstNodeCoverOrAssert {
    // @astgen op3 := coverincsp: List[AstNode] // Coverage node
public:
    ASTGEN_MEMBERS_AstCover;
    AstCover(FileLine* fl, AstNode* propp, AstNode* stmtsp, VAssertType type,
             const string& name = "")
        : ASTGEN_SUPER_Cover(fl, propp, stmtsp, type, VAssertDirectiveType::COVER, name) {}
    string verilogKwd() const override { return "cover"; }
};
class AstRestrict final : public AstNodeCoverOrAssert {
public:
    ASTGEN_MEMBERS_AstRestrict;
    AstRestrict(FileLine* fl, AstNode* propp)
        // Intrinsic asserts are always ignored thus 'type' field is set to INTERNAL.
        : ASTGEN_SUPER_Restrict(fl, propp, nullptr, VAssertType::INTERNAL,
                                VAssertDirectiveType::RESTRICT) {}
    string verilogKwd() const override { return "restrict"; }
};

// === AstNodeForeach ===
class AstConstraintForeach final : public AstNodeForeach {
    // Constraint foreach statement
public:
    AstConstraintForeach(FileLine* fl, AstNodeExpr* exprp, AstNode* bodysp)
        : ASTGEN_SUPER_ConstraintForeach(fl, exprp, bodysp) {}
    ASTGEN_MEMBERS_AstConstraintForeach;
};
class AstForeach final : public AstNodeForeach {
public:
    AstForeach(FileLine* fl, AstNode* arrayp, AstNode* stmtsp)
        : ASTGEN_SUPER_Foreach(fl, arrayp, stmtsp) {}
    ASTGEN_MEMBERS_AstForeach;
};

// === AstNodeIf ===
class AstConstraintIf final : public AstNodeIf {
public:
    AstConstraintIf(FileLine* fl, AstNodeExpr* condp, AstNode* thensp, AstNode* elsesp)
        : ASTGEN_SUPER_ConstraintIf(fl, condp, thensp, elsesp) {}
    ASTGEN_MEMBERS_AstConstraintIf;
};

class AstIf final : public AstNodeIf {
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstIf(FileLine* fl, AstNodeExpr* condp, AstNode* thensp = nullptr, AstNode* elsesp = nullptr)
        : ASTGEN_SUPER_If(fl, condp, thensp, elsesp) {}
    ASTGEN_MEMBERS_AstIf;
    bool uniquePragma() const { return m_uniquePragma; }
    void uniquePragma(bool flag) { m_uniquePragma = flag; }
    bool unique0Pragma() const { return m_unique0Pragma; }
    void unique0Pragma(bool flag) { m_unique0Pragma = flag; }
    bool priorityPragma() const { return m_priorityPragma; }
    void priorityPragma(bool flag) { m_priorityPragma = flag; }
};

// === AstNodeReadWriteMem ===
class AstReadMem final : public AstNodeReadWriteMem {
public:
    AstReadMem(FileLine* fl, bool hex, AstNodeExpr* filenamep, AstNodeExpr* memp,
               AstNodeExpr* lsbp, AstNodeExpr* msbp)
        : ASTGEN_SUPER_ReadMem(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTGEN_MEMBERS_AstReadMem;
    string verilogKwd() const override { return (isHex() ? "$readmemh" : "$readmemb"); }
    const char* cFuncPrefixp() const override { return "VL_READMEM_"; }
};
class AstWriteMem final : public AstNodeReadWriteMem {
public:
    AstWriteMem(FileLine* fl, bool hex, AstNodeExpr* filenamep, AstNodeExpr* memp,
                AstNodeExpr* lsbp, AstNodeExpr* msbp)
        : ASTGEN_SUPER_WriteMem(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTGEN_MEMBERS_AstWriteMem;
    string verilogKwd() const override { return (isHex() ? "$writememh" : "$writememb"); }
    const char* cFuncPrefixp() const override { return "VL_WRITEMEM_"; }
};

#endif  // Guard
