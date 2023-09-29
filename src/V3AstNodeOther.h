// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing other constructs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// This files contains all 'AstNode' sub-types that relate to other constructs
// not covered by the more specific V3AstNode*.h files.
//
//*************************************************************************

#ifndef VERILATOR_V3ASTNODES_H_
#define VERILATOR_V3ASTNODES_H_

#ifndef VERILATOR_V3AST_H_
#error "Use V3Ast.h as the include"
#include "V3Ast.h"  // This helps code analysis tools pick up symbols in V3Ast.h
#define VL_NOT_FINAL  // This #define fixes broken code folding in the CLion IDE
#endif

// === Abstract base node types (AstNode*) =====================================

class AstNodeBlock VL_NOT_FINAL : public AstNode {
    // A Begin/fork block
    // @astgen op2 := stmtsp : List[AstNode]
    // Parents: statement
private:
    string m_name;  // Name of block
    bool m_unnamed;  // Originally unnamed (name change does not affect this)
protected:
    AstNodeBlock(VNType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name} {
        addStmtsp(stmtsp);
        m_unnamed = (name == "");
    }

public:
    ASTGEN_MEMBERS_AstNodeBlock;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Block name
    void name(const string& name) override { m_name = name; }
    bool unnamed() const { return m_unnamed; }
    bool isFirstInMyListOfStatements(AstNode* nodep) const override { return nodep == stmtsp(); }
};
class AstNodeFTask VL_NOT_FINAL : public AstNode {
    // Output variable in functions, nullptr in tasks
    // @astgen op1 := fvarp : Optional[AstNode]
    // Class/package scope
    // @astgen op2 := classOrPackagep : Optional[AstNode]
    // Statements/Ports/Vars
    // @astgen op3 := stmtsp : List[AstNode]
    // Scope name
    // @astgen op4 := scopeNamep : Optional[AstScopeName]
private:
    string m_name;  // Name of task
    string m_cname;  // Name of task if DPI import
    uint64_t m_dpiOpenParent = 0;  // DPI import open array, if !=0, how many callees
    bool m_taskPublic : 1;  // Public task
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_classMethod : 1;  // Class method
    bool m_externProto : 1;  // Extern prototype
    bool m_externDef : 1;  // Extern definition
    bool m_prototype : 1;  // Just a prototype
    bool m_dpiExport : 1;  // DPI exported
    bool m_dpiImport : 1;  // DPI imported
    bool m_dpiContext : 1;  // DPI import context
    bool m_dpiOpenChild : 1;  // DPI import open array child wrapper
    bool m_dpiTask : 1;  // DPI import task (vs. void function)
    bool m_dpiTraceInit : 1;  // DPI trace_init
    bool m_isConstructor : 1;  // Class constructor
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_dpiPure : 1;  // DPI import pure (vs. virtual pure)
    bool m_pureVirtual : 1;  // Pure virtual
    bool m_recursive : 1;  // Recursive or part of recursion
    bool m_underGenerate : 1;  // Under generate (for warning)
    bool m_virtual : 1;  // Virtual method in class
    bool m_needProcess : 1;  // Implements part of a process that allocates std::process
    VLifetime m_lifetime;  // Lifetime
    VIsCached m_purity;  // Pure state

protected:
    AstNodeFTask(VNType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name}
        , m_taskPublic{false}
        , m_attrIsolateAssign{false}
        , m_classMethod{false}
        , m_externProto{false}
        , m_externDef{false}
        , m_prototype{false}
        , m_dpiExport{false}
        , m_dpiImport{false}
        , m_dpiContext{false}
        , m_dpiOpenChild{false}
        , m_dpiTask{false}
        , m_dpiTraceInit{false}
        , m_isConstructor{false}
        , m_isHideLocal{false}
        , m_isHideProtected{false}
        , m_dpiPure{false}
        , m_pureVirtual{false}
        , m_recursive{false}
        , m_underGenerate{false}
        , m_virtual{false}
        , m_needProcess{false} {
        addStmtsp(stmtsp);
        cname(name);  // Might be overridden by dpi import/export
    }

public:
    ASTGEN_MEMBERS_AstNodeFTask;
    virtual AstNodeFTask* cloneType(const string& name) = 0;
    void dump(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool maybePointedTo() const override { return true; }
    bool isGateOptimizable() const override {
        return !((m_dpiExport || m_dpiImport) && !m_dpiPure);
    }
    // {AstFunc only} op1 = Range output variable
    void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
    bool isFunction() const { return fvarp() != nullptr; }
    // MORE ACCESSORS
    void dpiOpenParentInc() { ++m_dpiOpenParent; }
    void dpiOpenParentClear() { m_dpiOpenParent = 0; }
    uint64_t dpiOpenParent() const { return m_dpiOpenParent; }
    void taskPublic(bool flag) { m_taskPublic = flag; }
    bool taskPublic() const { return m_taskPublic; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    void classMethod(bool flag) { m_classMethod = flag; }
    bool classMethod() const { return m_classMethod; }
    void isExternProto(bool flag) { m_externProto = flag; }
    bool isExternProto() const { return m_externProto; }
    void isExternDef(bool flag) { m_externDef = flag; }
    bool isExternDef() const { return m_externDef; }
    void prototype(bool flag) { m_prototype = flag; }
    bool prototype() const { return m_prototype; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
    bool dpiExport() const { return m_dpiExport; }
    void dpiImport(bool flag) { m_dpiImport = flag; }
    bool dpiImport() const { return m_dpiImport; }
    void dpiContext(bool flag) { m_dpiContext = flag; }
    bool dpiContext() const { return m_dpiContext; }
    void dpiOpenChild(bool flag) { m_dpiOpenChild = flag; }
    bool dpiOpenChild() const { return m_dpiOpenChild; }
    void dpiTask(bool flag) { m_dpiTask = flag; }
    bool dpiTask() const { return m_dpiTask; }
    void dpiTraceInit(bool flag) { m_dpiTraceInit = flag; }
    bool dpiTraceInit() const { return m_dpiTraceInit; }
    void isConstructor(bool flag) { m_isConstructor = flag; }
    bool isConstructor() const { return m_isConstructor; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    void dpiPure(bool flag) { m_dpiPure = flag; }
    bool dpiPure() const { return m_dpiPure; }
    void pureVirtual(bool flag) { m_pureVirtual = flag; }
    bool pureVirtual() const { return m_pureVirtual; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void underGenerate(bool flag) { m_underGenerate = flag; }
    bool underGenerate() const { return m_underGenerate; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool isVirtual() const { return m_virtual; }
    void setNeedProcess() { m_needProcess = true; }
    bool needProcess() const { return m_needProcess; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
    bool isPure() override;
    const char* broken() const override;
    void propagateAttrFrom(const AstNodeFTask* fromp) {
        // Creating a wrapper with e.g. cloneType(); preserve some attributes
        classMethod(fromp->classMethod());
        isHideLocal(fromp->isHideLocal());
        isHideProtected(fromp->isHideProtected());
        isVirtual(fromp->isVirtual());
        lifetime(fromp->lifetime());
        underGenerate(fromp->underGenerate());
    }

private:
    bool getPurityRecurse() const;
};
class AstNodeFile VL_NOT_FINAL : public AstNode {
    // Emitted Output file
    // Parents:  NETLIST
    // @astgen op1 := tblockp : Optional[AstTextBlock]
private:
    string m_name;  ///< Filename
public:
    AstNodeFile(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstNodeFile;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstNodeModule VL_NOT_FINAL : public AstNode {
    // A module, package, program or interface declaration;
    // something that can live directly under the TOP,
    // excluding $unit package stuff
    // @astgen op1 := inlinesp : List[AstNode]
    // @astgen op2 := stmtsp : List[AstNode]
    // @astgen op3 := activesp : List[AstActive]
private:
    string m_name;  // Name of the module
    const string m_origName;  // Name of the module, ignoring name() changes, for dot lookup
    string m_someInstanceName;  // Hierarchical name of some arbitrary instance of this module.
                                // Used for user messages only.
    int m_level = 0;  // 1=top module, 2=cell off top module, ...
    VLifetime m_lifetime;  // Lifetime
    VTimescale m_timeunit;  // Global time unit
    VOptionBool m_unconnectedDrive;  // State of `unconnected_drive

    bool m_modPublic : 1;  // Module has public references
    bool m_modTrace : 1;  // Tracing this module
    bool m_inLibrary : 1;  // From a library, no error if not used, never top level
    bool m_dead : 1;  // LinkDot believes is dead; will remove in Dead visitors
    bool m_hasGParam : 1;  // Has global parameter (for link)
    bool m_hasParameterList : 1;  // Has #() for parameter declaration
    bool m_hierBlock : 1;  // Hierarchical Block marked by HIER_BLOCK pragma
    bool m_internal : 1;  // Internally created
    bool m_recursive : 1;  // Recursive module
    bool m_recursiveClone : 1;  // If recursive, what module it clones, otherwise nullptr
protected:
    AstNodeModule(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name}
        , m_origName{name}
        , m_modPublic{false}
        , m_modTrace{false}
        , m_inLibrary{false}
        , m_dead{false}
        , m_hasGParam{false}
        , m_hasParameterList{false}
        , m_hierBlock{false}
        , m_internal{false}
        , m_recursive{false}
        , m_recursiveClone{false} {}

public:
    ASTGEN_MEMBERS_AstNodeModule;
    void dump(std::ostream& str) const override;
    bool maybePointedTo() const override { return true; }
    string name() const override VL_MT_STABLE { return m_name; }
    virtual bool timescaleMatters() const = 0;
    // ACCESSORS
    void name(const string& name) override { m_name = name; }
    string origName() const override { return m_origName; }
    string someInstanceName() const VL_MT_SAFE { return m_someInstanceName; }
    void someInstanceName(const string& name) { m_someInstanceName = name; }
    bool inLibrary() const { return m_inLibrary; }
    void inLibrary(bool flag) { m_inLibrary = flag; }
    void level(int level) { m_level = level; }
    int level() const VL_MT_SAFE { return m_level; }
    bool isTop() const VL_MT_SAFE { return level() == 1; }
    void modPublic(bool flag) { m_modPublic = flag; }
    bool modPublic() const { return m_modPublic; }
    void modTrace(bool flag) { m_modTrace = flag; }
    bool modTrace() const { return m_modTrace; }
    void dead(bool flag) { m_dead = flag; }
    bool dead() const { return m_dead; }
    void hasGParam(bool flag) { m_hasGParam = flag; }
    bool hasGParam() const { return m_hasGParam; }
    void hasParameterList(bool flag) { m_hasParameterList = flag; }
    bool hasParameterList() const { return m_hasParameterList; }
    void hierBlock(bool flag) { m_hierBlock = flag; }
    bool hierBlock() const { return m_hierBlock; }
    void internal(bool flag) { m_internal = flag; }
    bool internal() const { return m_internal; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void recursiveClone(bool flag) { m_recursiveClone = flag; }
    bool recursiveClone() const { return m_recursiveClone; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
    void unconnectedDrive(const VOptionBool flag) { m_unconnectedDrive = flag; }
    VOptionBool unconnectedDrive() const { return m_unconnectedDrive; }
};
class AstNodeProcedure VL_NOT_FINAL : public AstNode {
    // IEEE procedure: initial, final, always
    // @astgen op2 := stmtsp : List[AstNode] // Note: op1 is used in some sub-types only
    bool m_suspendable : 1;  // Is suspendable by a Delay, EventControl, etc.
    bool m_needProcess : 1;  // Implements part of a process that allocates std::process
protected:
    AstNodeProcedure(VNType t, FileLine* fl, AstNode* stmtsp)
        : AstNode{t, fl} {
        m_needProcess = false;
        m_suspendable = false;
        addStmtsp(stmtsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeProcedure;
    // METHODS
    void dump(std::ostream& str) const override;
    bool isJustOneBodyStmt() const { return stmtsp() && !stmtsp()->nextp(); }
    bool isSuspendable() const { return m_suspendable; }
    void setSuspendable() { m_suspendable = true; }
    bool needProcess() const { return m_needProcess; }
    void setNeedProcess() { m_needProcess = true; }
};
class AstNodeRange VL_NOT_FINAL : public AstNode {
    // A range, sized or unsized
protected:
    AstNodeRange(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeRange;
    void dump(std::ostream& str) const override;
};
class AstNodeStmt VL_NOT_FINAL : public AstNode {
    // Procedural statement
protected:
    AstNodeStmt(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_AstNodeStmt;
    // METHODS
    void addNextStmt(AstNode* newp,
                     AstNode* belowp) override;  // Stop statement searchback here
    void dump(std::ostream& str = std::cout) const override;
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
    bool hasDType() const override { return true; }
    virtual bool cleanRhs() const { return true; }
    int instrCount() const override { return widthInstrs(); }
    bool same(const AstNode*) const override { return true; }
    string verilogKwd() const override { return "="; }
    bool isTimingControl() const override { return timingControlp(); }
    virtual bool brokeLhsMustBeLvalue() const = 0;
};
class AstNodeCase VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := exprp : AstNodeExpr // Condition (scurtinee) expression
    // @astgen op2 := itemsp : List[AstCaseItem]
    // @astgen op3 := notParallelp : List[AstNode] // assertion code for non-full case's
protected:
    AstNodeCase(VNType t, FileLine* fl, AstNodeExpr* exprp, AstCaseItem* itemsp)
        : AstNodeStmt{t, fl} {
        this->exprp(exprp);
        this->addItemsp(itemsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeCase;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
};
class AstNodeCoverOrAssert VL_NOT_FINAL : public AstNodeStmt {
    // Cover or Assert
    // Parents:  {statement list}
    // @astgen op1 := propp : AstNode
    // @astgen op2 := sentreep : Optional[AstSenTree]
    // op3 used by some sub-types only
    // @astgen op4 := passsp: List[AstNode] // Statements when propp is passing/truthly
    string m_name;  // Name to report
    const bool m_immediate;  // Immediate assertion/cover
public:
    AstNodeCoverOrAssert(VNType t, FileLine* fl, AstNode* propp, AstNode* passsp, bool immediate,
                         const string& name = "")
        : AstNodeStmt{t, fl}
        , m_name{name}
        , m_immediate{immediate} {
        this->propp(propp);
        this->addPasssp(passsp);
    }
    ASTGEN_MEMBERS_AstNodeCoverOrAssert;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool same(const AstNode* samep) const override { return samep->name() == name(); }
    void name(const string& name) override { m_name = name; }
    void dump(std::ostream& str = std::cout) const override;
    bool immediate() const { return m_immediate; }
};
class AstNodeFor VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := initsp : List[AstNode]
    // @astgen op2 := condp : AstNodeExpr
    // @astgen op3 := incsp : List[AstNode]
    // @astgen op4 := stmtsp : List[AstNode]
protected:
    AstNodeFor(VNType t, FileLine* fl, AstNode* initsp, AstNodeExpr* condp, AstNode* incsp,
               AstNode* stmtsp)
        : AstNodeStmt{t, fl} {
        this->addInitsp(initsp);
        this->condp(condp);
        this->addIncsp(incsp);
        this->addStmtsp(stmtsp);
    }

public:
    ASTGEN_MEMBERS_AstNodeFor;
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstNodeIf VL_NOT_FINAL : public AstNodeStmt {
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := thensp : List[AstNode]
    // @astgen op3 := elsesp : List[AstNode]
private:
    VBranchPred m_branchPred;  // Branch prediction as taken/untaken?
    bool m_isBoundsCheck;  // True if this if node is for assertion/bounds checking
protected:
    AstNodeIf(VNType t, FileLine* fl, AstNodeExpr* condp, AstNode* thensp, AstNode* elsesp)
        : AstNodeStmt{t, fl} {
        this->condp(condp);
        this->addThensp(thensp);
        this->addElsesp(elsesp);
        isBoundsCheck(false);
    }

public:
    ASTGEN_MEMBERS_AstNodeIf;
    bool isGateOptimizable() const override { return false; }
    bool isGateDedupable() const override { return true; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    void branchPred(VBranchPred flag) { m_branchPred = flag; }
    VBranchPred branchPred() const { return m_branchPred; }
    void isBoundsCheck(bool flag) { m_isBoundsCheck = flag; }
    bool isBoundsCheck() const { return m_isBoundsCheck; }
    bool isFirstInMyListOfStatements(AstNode* n) const override {
        return n == thensp() || n == elsesp();
    }
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
        , m_isHex(hex) {
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
    bool same(const AstNode* samep) const override {
        return isHex() == static_cast<const AstNodeReadWriteMem*>(samep)->isHex();
    }
    bool isHex() const { return m_isHex; }
    virtual const char* cFuncPrefixp() const = 0;
};
class AstNodeText VL_NOT_FINAL : public AstNode {
private:
    string m_text;

protected:
    // Node that puts text into the output stream
    AstNodeText(VNType t, FileLine* fl, const string& text)
        : AstNode{t, fl}
        , m_text{text} {}

public:
    ASTGEN_MEMBERS_AstNodeText;
    void dump(std::ostream& str = std::cout) const override;
    bool same(const AstNode* samep) const override {
        const AstNodeText* asamep = static_cast<const AstNodeText*>(samep);
        return text() == asamep->text();
    }
    const string& text() const VL_MT_SAFE { return m_text; }
    void text(const string& value) { m_text = value; }
};
class AstNodeSimpleText VL_NOT_FINAL : public AstNodeText {
private:
    bool m_tracking;  // When emit, it's ok to parse the string to do indentation
public:
    AstNodeSimpleText(VNType t, FileLine* fl, const string& textp, bool tracking = false)
        : AstNodeText{t, fl, textp}
        , m_tracking{tracking} {}
    ASTGEN_MEMBERS_AstNodeSimpleText;
    void tracking(bool flag) { m_tracking = flag; }
    bool tracking() const { return m_tracking; }
};

// === Concrete node types =====================================================

// === AstNode ===
class AstActive final : public AstNode {
    // Block of code with sensitivity activation
    // Parents:  MODULE | CFUNC
    // @astgen op1 := sensesStorep : Optional[AstSenTree] // Moved into m_sensesp in V3Active
    // @astgen op2 := stmtsp : List[AstNode] // Logic
private:
    string m_name;
    AstSenTree* m_sensesp;

public:
    AstActive(FileLine* fl, const string& name, AstSenTree* sensesp)
        : ASTGEN_SUPER_Active(fl)
        , m_name{name}
        , m_sensesp{sensesp} {
        UASSERT(sensesp, "Sensesp required arg");
    }
    ASTGEN_MEMBERS_AstActive;
    void dump(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    const char* broken() const override;
    void cloneRelink() override;
    // Statements are broken into pieces, as some must come before others.
    void sensesp(AstSenTree* nodep) { m_sensesp = nodep; }
    AstSenTree* sensesp() const { return m_sensesp; }
    // METHODS
    inline bool hasClocked() const;
    inline bool hasCombo() const;
};
class AstBind final : public AstNode {
    // Parents: MODULE
    // Children: CELL
    // @astgen op1 := cellsp : List[AstNode]
private:
    string m_name;  // Binding to name
public:
    AstBind(FileLine* fl, const string& name, AstNode* cellsp)
        : ASTGEN_SUPER_Bind(fl)
        , m_name{name} {
        UASSERT_OBJ(VN_IS(cellsp, Cell), cellsp, "Only instances allowed to be bound");
        this->addCellsp(cellsp);
    }
    ASTGEN_MEMBERS_AstBind;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Bind Target name
    void name(const string& name) override { m_name = name; }
};
class AstCFunc final : public AstNode {
    // C++ function
    // Parents:  MODULE/SCOPE
    // If adding node accessors, see below emptyBody
    // @astgen op1 := argsp : List[AstNode]
    // @astgen op2 := initsp : List[AstNode]
    // @astgen op3 := stmtsp : List[AstNode]
    // @astgen op4 := finalsp : List[AstNode]
private:
    AstScope* m_scopep;
    string m_name;
    string m_cname;  // C name, for dpiExports
    string m_rtnType;  // void, bool, or other return type
    string m_argTypes;  // Argument types
    string m_baseCtors;  // Base class constructor
    string m_ifdef;  // #ifdef symbol around this function
    VBoolOrUnknown m_isConst;  // Function is declared const (*this not changed)
    bool m_isStatic : 1;  // Function is static (no need for a 'this' pointer)
    bool m_isTrace : 1;  // Function is related to tracing
    bool m_dontCombine : 1;  // V3Combine shouldn't compare this func tree, it's special
    bool m_declPrivate : 1;  // Declare it private
    bool m_slow : 1;  // Slow routine, called once or just at init time
    bool m_funcPublic : 1;  // From user public task/function
    bool m_isConstructor : 1;  // Is C class constructor
    bool m_isDestructor : 1;  // Is C class destructor
    bool m_isMethod : 1;  // Is inside a class definition
    bool m_isLoose : 1;  // Semantically this is a method, but is implemented as a function
                         // with an explicitly passed 'self' pointer as the first argument
    bool m_isInline : 1;  // Inline function
    bool m_isVirtual : 1;  // Virtual function
    bool m_entryPoint : 1;  // User may call into this top level function
    bool m_dpiPure : 1;  // Pure DPI function
    bool m_dpiContext : 1;  // Declared as 'context' DPI import/export function
    bool m_dpiExportDispatcher : 1;  // This is the DPI export entry point (i.e.: called by user)
    bool m_dpiExportImpl : 1;  // DPI export implementation (called from DPI dispatcher via lookup)
    bool m_dpiImportPrototype : 1;  // This is the DPI import prototype (i.e.: provided by user)
    bool m_dpiImportWrapper : 1;  // Wrapper for invoking DPI import prototype from generated code
    bool m_dpiTraceInit : 1;  // DPI trace_init
    bool m_needProcess : 1;  // Implements part of a process that allocates std::process
public:
    AstCFunc(FileLine* fl, const string& name, AstScope* scopep, const string& rtnType = "")
        : ASTGEN_SUPER_CFunc(fl) {
        m_isConst = VBoolOrUnknown::BU_UNKNOWN;  // Unknown until analyzed
        m_scopep = scopep;
        m_name = name;
        m_rtnType = rtnType;
        m_isStatic = false;
        m_isTrace = false;
        m_dontCombine = false;
        m_declPrivate = false;
        m_slow = false;
        m_funcPublic = false;
        m_isConstructor = false;
        m_isDestructor = false;
        m_isMethod = true;
        m_isLoose = false;
        m_isInline = false;
        m_isVirtual = false;
        m_needProcess = false;
        m_entryPoint = false;
        m_dpiPure = false;
        m_dpiContext = false;
        m_dpiExportDispatcher = false;
        m_dpiExportImpl = false;
        m_dpiImportPrototype = false;
        m_dpiImportWrapper = false;
        m_dpiTraceInit = false;
    }
    ASTGEN_MEMBERS_AstCFunc;
    string name() const override VL_MT_STABLE { return m_name; }
    const char* broken() const override;
    void cloneRelink() override;
    bool maybePointedTo() const override { return true; }
    void dump(std::ostream& str = std::cout) const override;
    bool same(const AstNode* samep) const override {
        const AstCFunc* const asamep = static_cast<const AstCFunc*>(samep);
        return ((isTrace() == asamep->isTrace()) && (rtnTypeVoid() == asamep->rtnTypeVoid())
                && (argTypes() == asamep->argTypes()) && (baseCtors() == asamep->baseCtors())
                && isLoose() == asamep->isLoose()
                && (!(dpiImportPrototype() || dpiExportImpl()) || name() == asamep->name()));
    }
    //
    void name(const string& name) override { m_name = name; }
    int instrCount() const override {
        return dpiImportPrototype() ? v3Global.opt.instrCountDpi() : 0;
    }
    VBoolOrUnknown isConst() const { return m_isConst; }
    void isConst(bool flag) { m_isConst.setTrueOrFalse(flag); }
    void isConst(VBoolOrUnknown flag) { m_isConst = flag; }
    bool isStatic() const { return m_isStatic; }
    void isStatic(bool flag) { m_isStatic = flag; }
    bool isTrace() const VL_MT_SAFE { return m_isTrace; }
    void isTrace(bool flag) { m_isTrace = flag; }
    void cname(const string& name) { m_cname = name; }
    string cname() const { return m_cname; }
    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    string rtnTypeVoid() const { return ((m_rtnType == "") ? "void" : m_rtnType); }
    void rtnType(const string& rtnType) { m_rtnType = rtnType; }
    bool dontCombine() const { return m_dontCombine || isTrace() || entryPoint(); }
    void dontCombine(bool flag) { m_dontCombine = flag; }
    bool dontInline() const { return dontCombine() || slow() || funcPublic(); }
    bool declPrivate() const { return m_declPrivate; }
    void declPrivate(bool flag) { m_declPrivate = flag; }
    bool slow() const VL_MT_SAFE { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool funcPublic() const { return m_funcPublic; }
    void funcPublic(bool flag) { m_funcPublic = flag; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
    void baseCtors(const string& str) { m_baseCtors = str; }
    string baseCtors() const { return m_baseCtors; }
    void ifdef(const string& str) { m_ifdef = str; }
    string ifdef() const { return m_ifdef; }
    bool isConstructor() const { return m_isConstructor; }
    void isConstructor(bool flag) { m_isConstructor = flag; }
    bool isDestructor() const { return m_isDestructor; }
    void isDestructor(bool flag) { m_isDestructor = flag; }
    bool isMethod() const { return m_isMethod; }
    void isMethod(bool flag) { m_isMethod = flag; }
    bool isLoose() const { return m_isLoose; }
    void isLoose(bool flag) { m_isLoose = flag; }
    bool isProperMethod() const { return isMethod() && !isLoose(); }
    bool isInline() const { return m_isInline; }
    void isInline(bool flag) { m_isInline = flag; }
    bool isVirtual() const { return m_isVirtual; }
    void isVirtual(bool flag) { m_isVirtual = flag; }
    bool needProcess() const { return m_needProcess; }
    void setNeedProcess() { m_needProcess = true; }
    bool entryPoint() const { return m_entryPoint; }
    void entryPoint(bool flag) { m_entryPoint = flag; }
    bool dpiPure() const { return m_dpiPure; }
    void dpiPure(bool flag) { m_dpiPure = flag; }
    bool dpiContext() const { return m_dpiContext; }
    void dpiContext(bool flag) { m_dpiContext = flag; }
    bool dpiExportDispatcher() const VL_MT_SAFE { return m_dpiExportDispatcher; }
    void dpiExportDispatcher(bool flag) { m_dpiExportDispatcher = flag; }
    bool dpiExportImpl() const { return m_dpiExportImpl; }
    void dpiExportImpl(bool flag) { m_dpiExportImpl = flag; }
    bool dpiImportPrototype() const VL_MT_SAFE { return m_dpiImportPrototype; }
    void dpiImportPrototype(bool flag) { m_dpiImportPrototype = flag; }
    bool dpiImportWrapper() const { return m_dpiImportWrapper; }
    void dpiImportWrapper(bool flag) { m_dpiImportWrapper = flag; }
    void dpiTraceInit(bool flag) { m_dpiTraceInit = flag; }
    bool dpiTraceInit() const { return m_dpiTraceInit; }
    bool isCoroutine() const { return m_rtnType == "VlCoroutine"; }
    // Special methods
    bool emptyBody() const {
        return argsp() == nullptr && initsp() == nullptr && stmtsp() == nullptr
               && finalsp() == nullptr;
    }
};
class AstCLocalScope final : public AstNode {
    // Pack statements into an unnamed scope when generating C++
    // @astgen op1 := stmtsp : List[AstNode]
public:
    AstCLocalScope(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_CLocalScope(fl) {
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstCLocalScope;
};
class AstCUse final : public AstNode {
    // C++ use of a class or #include; indicates need of forward declaration
    // Parents:  NODEMODULE
private:
    const string m_name;
    const VUseType m_useType;  // What sort of use this is

public:
    AstCUse(FileLine* fl, VUseType useType, const string& name)
        : ASTGEN_SUPER_CUse(fl)
        , m_name{name}
        , m_useType{useType} {}
    ASTGEN_MEMBERS_AstCUse;
    void dump(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    VUseType useType() const { return m_useType; }
};
class AstCaseItem final : public AstNode {
    // Single item of a case statement
    // @astgen op1 := condsp : List[AstNodeExpr]
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstCaseItem(FileLine* fl, AstNodeExpr* condsp, AstNode* stmtsp)
        : ASTGEN_SUPER_CaseItem(fl) {
        this->addCondsp(condsp);
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstCaseItem;
    int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
    bool isDefault() const { return condsp() == nullptr; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
};
class AstCell final : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
    // @astgen op1 := pinsp : List[AstPin] // List of port assignments
    // @astgen op2 := paramsp : List[AstPin] // List of parameter assignments
    // @astgen op3 := rangep : Optional[AstRange] // Range for arrayed instances
    // @astgen op4 := intfRefsp : List[AstIntfRef] // List of interface references
    FileLine* m_modNameFileline;  // Where module the cell instances token was
    string m_name;  // Cell name
    string m_origName;  // Original name before dot addition
    string m_modName;  // Module the cell instances
    AstNodeModule* m_modp = nullptr;  // [AfterLink] Pointer to module instanced
    bool m_hasIfaceVar : 1;  // True if a Var has been created for this cell
    bool m_hasNoParens : 1;  // Instantiation has no parenthesis
    bool m_recursive : 1;  // Self-recursive module
    bool m_trace : 1;  // Trace this cell
public:
    AstCell(FileLine* fl, FileLine* mfl, const string& instName, const string& modName,
            AstPin* pinsp, AstPin* paramsp, AstRange* rangep)
        : ASTGEN_SUPER_Cell(fl)
        , m_modNameFileline{mfl}
        , m_name{instName}
        , m_origName{instName}
        , m_modName{modName}
        , m_hasIfaceVar{false}
        , m_hasNoParens{false}
        , m_recursive{false}
        , m_trace{true} {
        this->addPinsp(pinsp);
        this->addParamsp(paramsp);
        this->rangep(rangep);
    }
    ASTGEN_MEMBERS_AstCell;
    // No cloneRelink, we presume cloneee's want the same module linkages
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    bool maybePointedTo() const override { return true; }
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Cell name
    void name(const string& name) override { m_name = name; }
    string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    string modName() const { return m_modName; }  // * = Instance name
    void modName(const string& name) { m_modName = name; }
    FileLine* modNameFileline() const { return m_modNameFileline; }
    AstNodeModule* modp() const { return m_modp; }  // [AfterLink] = Pointer to module instantiated
    void modp(AstNodeModule* nodep) { m_modp = nodep; }
    bool hasIfaceVar() const { return m_hasIfaceVar; }
    void hasIfaceVar(bool flag) { m_hasIfaceVar = flag; }
    bool hasNoParens() const { return m_hasNoParens; }
    void hasNoParens(bool flag) { m_hasNoParens = flag; }
    void trace(bool flag) { m_trace = flag; }
    bool isTrace() const { return m_trace; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
};
class AstCellInline final : public AstNode {
    // A instantiation cell that was removed by inlining
    // For communication between V3Inline and V3LinkDot,
    // except for VPI runs where it exists until the end.
    // It is augmented with the scope in V3Scope for VPI.
    // Children: When 2 levels inlined, other CellInline under this
private:
    string m_name;  // Cell name, possibly {a}__DOT__{b}...
    const string
        m_origModName;  // Original name of the module, ignoring name() changes, for dot lookup
    AstScope* m_scopep = nullptr;  // The scope that the cell is inlined into
    VTimescale m_timeunit;  // Parent module time unit
public:
    AstCellInline(FileLine* fl, const string& name, const string& origModName,
                  const VTimescale& timeunit)
        : ASTGEN_SUPER_CellInline(fl)
        , m_name{name}
        , m_origModName{origModName}
        , m_timeunit{timeunit} {}
    ASTGEN_MEMBERS_AstCellInline;
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Cell name
    string origModName() const { return m_origModName; }  // * = modp()->origName() before inlining
    void name(const string& name) override { m_name = name; }
    void scopep(AstScope* scp) { m_scopep = scp; }
    AstScope* scopep() const { return m_scopep; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstClassExtends final : public AstNode {
    // class extends class name, or class implements class name
    // Children: List of AstParseRef for packages/classes
    // during early parse, then moves to dtype
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := classOrPkgsp : Optional[AstNode]
    const bool m_isImplements = false;  // class implements
    bool m_parameterized = false;  // has parameters in its statement

public:
    AstClassExtends(FileLine* fl, AstNode* classOrPkgsp, bool isImplements)
        : ASTGEN_SUPER_ClassExtends(fl)
        , m_isImplements{isImplements} {
        this->classOrPkgsp(classOrPkgsp);  // Only for parser
    }
    ASTGEN_MEMBERS_AstClassExtends;
    void dump(std::ostream& str) const override;
    bool hasDType() const override { return true; }
    string verilogKwd() const override { return isImplements() ? "implements" : "extends"; }
    // Class being extended (after link and instantiation if needed)
    AstClass* classOrNullp() const;
    AstClass* classp() const;  // Like above, but throws error if nulll
    bool isImplements() const { return m_isImplements; }
    void parameterized(bool flag) { m_parameterized = flag; }
    bool parameterized() const { return m_parameterized; }
};
class AstClocking final : public AstNode {
    // Parents:  MODULE
    // Children: SENITEM, CLOCKING ITEMs, VARs
    // @astgen op1 := sensesp : AstSenItem
    // @astgen op2 := itemsp : List[AstClockingItem]
    // @astgen op3 := varsp : List[AstVar]
    // @astgen op4 := eventp : Optional[AstVar]
    std::string m_name;  // Clocking block name
    const bool m_isDefault = false;  // True if default clocking
    const bool m_isGlobal = false;  // True if global clocking

public:
    AstClocking(FileLine* fl, const std::string& name, AstSenItem* sensesp,
                AstClockingItem* itemsp, bool isDefault, bool isGlobal)
        : ASTGEN_SUPER_Clocking(fl)
        , m_isDefault{isDefault}
        , m_isGlobal{isGlobal} {
        m_name = name;
        this->sensesp(sensesp);
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstClocking;
    void dump(std::ostream& str) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    bool isDefault() const { return m_isDefault; }
    bool isGlobal() const { return m_isGlobal; }
};
class AstClockingItem final : public AstNode {
    // Parents:  CLOCKING
    // Children: EXPRs, ASSIGNs, VARs
    // @astgen op1 := skewp : Optional[AstNodeExpr]
    // @astgen op2 := exprp : Optional[AstNodeExpr]
    // @astgen op3 := assignp : Optional[AstAssign]
    // @astgen op4 := varp : Optional[AstVar]
    VDirection m_direction;

public:
    AstClockingItem(FileLine* fl, VDirection direction, AstNodeExpr* skewp, AstNode* clockingDeclp)
        : ASTGEN_SUPER_ClockingItem(fl) {
        m_direction = direction;
        this->skewp(skewp);
        if (AstAssign* const clkAssignp = VN_CAST(clockingDeclp, Assign)) {
            this->assignp(clkAssignp);
        } else {
            exprp(VN_AS(clockingDeclp, NodeExpr));
        }
    }
    ASTGEN_MEMBERS_AstClockingItem;
    VDirection direction() const { return m_direction; }
};
class AstConstPool final : public AstNode {
    // Container for const static data
    // @astgen op1 := modulep : AstModule // m_modp below TODO: fix this mess
    std::unordered_multimap<uint32_t, AstVarScope*> m_tables;  // Constant tables (unpacked arrays)
    std::unordered_multimap<uint32_t, AstVarScope*> m_consts;  // Constant tables (scalars)
    AstModule* const m_modp;  // The Module holding the Scope below ...
    AstScope* const m_scopep;  // Scope holding the constant variables

    AstVarScope* createNewEntry(const string& name, AstNodeExpr* initp);

public:
    explicit AstConstPool(FileLine* fl);
    ASTGEN_MEMBERS_AstConstPool;
    bool maybePointedTo() const override { return true; }
    const char* broken() const override;
    void cloneRelink() override { V3ERROR_NA; }
    AstModule* modp() const { return m_modp; }

    // Find a table (unpacked array) within the constant pool which is initialized with the
    // given value, or create one if one does not already exists. The returned VarScope *might*
    // have a different dtype than the given initp->dtypep(), including a different element type,
    // but it will always have the same size and element width. In contexts where this matters,
    // the caller must handle the dtype difference as appropriate.
    AstVarScope* findTable(AstInitArray* initp);
    // Find a constant within the constant pool which is initialized with the given value, or
    // create one if one does not already exists. If 'mergeDType' is true, then the returned
    // VarScope *might* have a different type than the given initp->dtypep(). In contexts where
    // this matters, the caller must handle the dtype difference as appropriate. If 'mergeDType' is
    // false, the returned VarScope will have _->dtypep()->sameTree(initp->dtypep()) return true.
    AstVarScope* findConst(AstConst* initp, bool mergeDType);
};
class AstDefParam final : public AstNode {
    // A defparam assignment
    // Parents: MODULE
    // @astgen op1 := rhsp : AstNodeExpr
    string m_name;  // Name of variable getting set
    string m_path;  // Dotted cellname to set parameter of
public:
    AstDefParam(FileLine* fl, const string& path, const string& name, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_DefParam(fl)
        , m_name{name}
        , m_path{path} {
        this->rhsp(rhsp);
    }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Scope name
    ASTGEN_MEMBERS_AstDefParam;
    bool same(const AstNode*) const override { return true; }
    string path() const { return m_path; }
};
class AstDpiExport final : public AstNode {
    // We could put an AstNodeFTaskRef instead of the verilog function name,
    // however we're not *calling* it, so that seems somehow wrong.
    // (Probably AstNodeFTaskRef should be renamed AstNodeFTaskCall and have-a AstNodeFTaskRef)
private:
    string m_name;  // Name of function
    string m_cname;  // Name of function on c side
public:
    AstDpiExport(FileLine* fl, const string& vname, const string& cname)
        : ASTGEN_SUPER_DpiExport(fl)
        , m_name{vname}
        , m_cname{cname} {}
    ASTGEN_MEMBERS_AstDpiExport;
    string name() const override VL_MT_STABLE { return m_name; }
    void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
};
class AstElabDisplay final : public AstNode {
    // Parents: stmtlist
    // @astgen op1 := fmtp : List[AstSFormatF]
private:
    VDisplayType m_displayType;

public:
    inline AstElabDisplay(FileLine* fl, VDisplayType dispType, AstNodeExpr* exprsp);
    ASTGEN_MEMBERS_AstElabDisplay;
    const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    string verilogKwd() const override { return string{"$"} + string{displayType().ascii()}; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstElabDisplay*>(samep)->displayType();
    }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    VDisplayType displayType() const { return m_displayType; }
    void displayType(VDisplayType type) { m_displayType = type; }
};
class AstEmpty final : public AstNode {
    // Represents something missing, e.g. a missing argument in FOREACH
public:
    explicit AstEmpty(FileLine* fl)
        : ASTGEN_SUPER_Empty(fl) {}
    ASTGEN_MEMBERS_AstEmpty;
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstExecGraph final : public AstNode {
    // For parallel execution, this node contains a dependency graph.  Each
    // vertex in the graph is an ExecMTask, which contains a body for the
    // mtask (an AstMTaskBody), which contains sequentially executed statements.
    //
    // The AstMTaskBody nodes are also children of this node, so we can visit
    // them without traversing the graph.
    //
    // @astgen op1 := mTaskBodiesp : List[AstMTaskBody]
    // In later phases, the statements that start the parallel execution
    // @astgen op2 := stmtsp : List[AstNode]
    V3Graph* const m_depGraphp;  // contains ExecMTask vertices
    const string m_name;  // Name of this AstExecGraph (for uniqueness at code generation)

public:
    explicit AstExecGraph(FileLine* fl, const string& name) VL_MT_DISABLED;
    ASTGEN_MEMBERS_AstExecGraph;
    ~AstExecGraph() override;
    const char* broken() const override {
        BROKEN_RTN(!m_depGraphp);
        return nullptr;
    }
    string name() const override VL_MT_STABLE { return m_name; }
    V3Graph* depGraphp() { return m_depGraphp; }
    const V3Graph* depGraphp() const { return m_depGraphp; }
};
class AstImplicit final : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
    // @astgen op1 := exprsp : List[AstNode]
public:
    AstImplicit(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_Implicit(fl) {
        this->addExprsp(exprsp);
    }
    ASTGEN_MEMBERS_AstImplicit;
};
class AstInitItem final : public AstNode {
    // Container for a item in an init array
    // This container is present so that the value underneath may get replaced with a new nodep
    // and the upper AstInitArray's map will remain correct (pointing to this InitItem)
    // @astgen op1 := valuep : AstNodeExpr
public:
    // Parents: INITARRAY
    AstInitItem(FileLine* fl, AstNodeExpr* valuep)
        : ASTGEN_SUPER_InitItem(fl) {
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstInitItem;
    bool maybePointedTo() const override { return true; }
    bool hasDType() const override { return false; }  // See valuep()'s dtype instead
};
class AstIntfRef final : public AstNode {
    // An interface reference
private:
    string m_name;  // Name of the reference
public:
    AstIntfRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER_IntfRef(fl)
        , m_name{name} {}
    string name() const override VL_MT_STABLE { return m_name; }
    ASTGEN_MEMBERS_AstIntfRef;
};
class AstMTaskBody final : public AstNode {
    // Hold statements for each MTask
    // @astgen op1 := stmtsp : List[AstNode]
    ExecMTask* m_execMTaskp = nullptr;

public:
    explicit AstMTaskBody(FileLine* fl)
        : ASTGEN_SUPER_MTaskBody(fl) {}
    ASTGEN_MEMBERS_AstMTaskBody;
    const char* broken() const override {
        BROKEN_RTN(!m_execMTaskp);
        return nullptr;
    }
    void addStmtsFirstp(AstNode* nodep) {
        if (stmtsp()) {
            stmtsp()->addHereThisAsNext(nodep);
        } else {
            addStmtsp(nodep);
        }
    }
    ExecMTask* execMTaskp() const { return m_execMTaskp; }
    void execMTaskp(ExecMTask* execMTaskp) { m_execMTaskp = execMTaskp; }
    void dump(std::ostream& str = std::cout) const override;
};
class AstModport final : public AstNode {
    // A modport in an interface
    // @astgen op1 := varsp : List[AstNode]
    string m_name;  // Name of the modport
public:
    AstModport(FileLine* fl, const string& name, AstNode* varsp)
        : ASTGEN_SUPER_Modport(fl)
        , m_name{name} {
        this->addVarsp(varsp);
    }
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override { return true; }
    ASTGEN_MEMBERS_AstModport;
};
class AstModportFTaskRef final : public AstNode {
    // An import/export referenced under a modport
    // The storage for the function itself is inside the
    // interface/instantiator, thus this is a reference
    // PARENT: AstModport
private:
    string m_name;  // Name of the variable referenced
    AstNodeFTask* m_ftaskp = nullptr;  // Link to the function
    bool m_export;  // Type of the function (import/export)
public:
    AstModportFTaskRef(FileLine* fl, const string& name, bool isExport)
        : ASTGEN_SUPER_ModportFTaskRef(fl)
        , m_name{name}
        , m_export{isExport} {}
    ASTGEN_MEMBERS_AstModportFTaskRef;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    bool isImport() const { return !m_export; }
    bool isExport() const { return m_export; }
    AstNodeFTask* ftaskp() const { return m_ftaskp; }  // [After Link] Pointer to variable
    void ftaskp(AstNodeFTask* ftaskp) { m_ftaskp = ftaskp; }
};
class AstModportVarRef final : public AstNode {
    // A input/output/etc variable referenced under a modport
    // The storage for the variable itself is inside the interface, thus this is a reference
    // PARENT: AstModport
private:
    string m_name;  // Name of the variable referenced
    AstVar* m_varp = nullptr;  // Link to the actual Var
    VDirection m_direction;  // Direction of the variable (in/out)
public:
    AstModportVarRef(FileLine* fl, const string& name, VDirection::en direction)
        : ASTGEN_SUPER_ModportVarRef(fl)
        , m_name{name}
        , m_direction{direction} {}
    ASTGEN_MEMBERS_AstModportVarRef;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    void direction(const VDirection& flag) { m_direction = flag; }
    VDirection direction() const { return m_direction; }
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp = varp; }
};
class AstNetlist final : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
    // @astgen op1 := modulesp : List[AstNodeModule]
    // @astgen op2 := filesp : List[AstNodeFile]
    // @astgen op3 := miscsp : List[AstNode]

    AstTypeTable* const m_typeTablep;  // Reference to top type table, for faster lookup
    AstConstPool* const m_constPoolp;  // Reference to constant pool, for faster lookup
    AstPackage* m_dollarUnitPkgp = nullptr;  // $unit
    AstPackage* m_stdPackagep = nullptr;  // SystemVerilog std package
    AstCFunc* m_evalp = nullptr;  // The '_eval' function
    AstCFunc* m_evalNbap = nullptr;  // The '_eval__nba' function
    AstVarScope* m_dpiExportTriggerp = nullptr;  // The DPI export trigger variable
    AstVar* m_delaySchedulerp = nullptr;  // The delay scheduler variable
    AstTopScope* m_topScopep = nullptr;  // The singleton AstTopScope under the top module
    VTimescale m_timeunit;  // Global time unit
    VTimescale m_timeprecision;  // Global time precision
    bool m_timescaleSpecified = false;  // Input HDL specified timescale
    uint32_t m_nextFreeMTaskID = 1;  // Next unique MTask ID within netlist
                                     // starts at 1 so 0 means no MTask ID
    uint32_t m_nextFreeMTaskProfilingID = 0;  // Next unique ID to use for PGO
public:
    AstNetlist();
    ASTGEN_MEMBERS_AstNetlist;
    const char* broken() const override;
    void cloneRelink() override { V3ERROR_NA; }
    string name() const override VL_MT_STABLE { return "$root"; }
    void dump(std::ostream& str) const override;
    AstNodeModule* topModulep() const VL_MT_STABLE {  // Top module in hierarchy
        return modulesp();  // First one in the list, for now
    }
    AstTypeTable* typeTablep() { return m_typeTablep; }
    AstConstPool* constPoolp() { return m_constPoolp; }
    AstPackage* dollarUnitPkgp() const { return m_dollarUnitPkgp; }
    AstPackage* dollarUnitPkgAddp();
    AstCFunc* evalp() const { return m_evalp; }
    void evalp(AstCFunc* funcp) { m_evalp = funcp; }
    AstCFunc* evalNbap() const { return m_evalNbap; }
    void evalNbap(AstCFunc* funcp) { m_evalNbap = funcp; }
    AstVarScope* dpiExportTriggerp() const { return m_dpiExportTriggerp; }
    void dpiExportTriggerp(AstVarScope* varScopep) { m_dpiExportTriggerp = varScopep; }
    AstVar* delaySchedulerp() const { return m_delaySchedulerp; }
    void delaySchedulerp(AstVar* const varScopep) { m_delaySchedulerp = varScopep; }
    void stdPackagep(AstPackage* const packagep) { m_stdPackagep = packagep; }
    AstPackage* stdPackagep() const { return m_stdPackagep; }
    AstTopScope* topScopep() const { return m_topScopep; }
    void createTopScope(AstScope* scopep);
    VTimescale timeunit() const { return m_timeunit; }
    void timeunit(const VTimescale& value) { m_timeunit = value; }
    VTimescale timeprecision() const { return m_timeprecision; }
    void timeInit() {
        m_timeunit = v3Global.opt.timeDefaultUnit();
        m_timeprecision = v3Global.opt.timeDefaultPrec();
    }
    void timeprecisionMerge(FileLine*, const VTimescale& value);
    void timescaleSpecified(bool specified) { m_timescaleSpecified = specified; }
    bool timescaleSpecified() const { return m_timescaleSpecified; }
    uint32_t allocNextMTaskID() { return m_nextFreeMTaskID++; }
    uint32_t allocNextMTaskProfilingID() { return m_nextFreeMTaskProfilingID++; }
    uint32_t usedMTaskProfilingIDs() const { return m_nextFreeMTaskProfilingID; }
};
class AstPackageExport final : public AstNode {
private:
    // A package export declaration
    string m_name;
    AstPackage* m_packagep;  // Package hierarchy
public:
    AstPackageExport(FileLine* fl, AstPackage* packagep, const string& name)
        : ASTGEN_SUPER_PackageExport(fl)
        , m_name{name}
        , m_packagep{packagep} {}
    ASTGEN_MEMBERS_AstPackageExport;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};
class AstPackageExportStarStar final : public AstNode {
    // A package export *::* declaration
public:
    // cppcheck-suppress noExplicitConstructor
    AstPackageExportStarStar(FileLine* fl)
        : ASTGEN_SUPER_PackageExportStarStar(fl) {}
    ASTGEN_MEMBERS_AstPackageExportStarStar;
};
class AstPackageImport final : public AstNode {
private:
    // A package import declaration
    string m_name;
    AstPackage* m_packagep;  // Package hierarchy
public:
    AstPackageImport(FileLine* fl, AstPackage* packagep, const string& name)
        : ASTGEN_SUPER_PackageImport(fl)
        , m_name{name}
        , m_packagep{packagep} {}
    ASTGEN_MEMBERS_AstPackageImport;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};
class AstPin final : public AstNode {
    // A port or parameter assignment on an instantiation
    // @astgen op1 := exprp : Optional[AstNode] // NodeExpr or NodeDType (nullptr if unconnected)
private:
    int m_pinNum;  // Pin number
    string m_name;  // Pin name, or "" for number based interconnect
    AstVar* m_modVarp = nullptr;  // Input/output this pin connects to on submodule.
    AstParamTypeDType* m_modPTypep = nullptr;  // Param type this pin connects to on submodule.
    bool m_param = false;  // Pin connects to parameter
    bool m_svDotName = false;  // Pin is SystemVerilog .name'ed
    bool m_svImplicit = false;  // Pin is SystemVerilog .name'ed, allow implicit
public:
    AstPin(FileLine* fl, int pinNum, const string& name, AstNode* exprp)
        : ASTGEN_SUPER_Pin(fl)
        , m_pinNum{pinNum}
        , m_name{name} {
        this->exprp(exprp);
    }
    inline AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp);
    ASTGEN_MEMBERS_AstPin;
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Pin name, ""=go by number
    void name(const string& name) override { m_name = name; }
    string prettyOperatorName() const override;
    bool dotStar() const { return name() == ".*"; }  // Fake name for .* connections until linked
    int pinNum() const { return m_pinNum; }
    AstVar* modVarp() const { return m_modVarp; }  // [After Link] Pointer to variable
    void modVarp(AstVar* nodep) { m_modVarp = nodep; }
    // [After Link] Pointer to variable
    AstParamTypeDType* modPTypep() const { return m_modPTypep; }
    void modPTypep(AstParamTypeDType* nodep) { m_modPTypep = nodep; }
    bool param() const { return m_param; }
    void param(bool flag) { m_param = flag; }
    bool svDotName() const { return m_svDotName; }
    void svDotName(bool flag) { m_svDotName = flag; }
    bool svImplicit() const { return m_svImplicit; }
    void svImplicit(bool flag) { m_svImplicit = flag; }
};
class AstPort final : public AstNode {
    // A port (in/out/inout) on a module
    // @astgen op1 := exprp : Optional[AstNodeExpr] // Expression connected to port
    const int m_pinNum;  // Pin number
    const string m_name;  // Name of pin
public:
    AstPort(FileLine* fl, int pinnum, const string& name)
        : ASTGEN_SUPER_Port(fl)
        , m_pinNum{pinnum}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstPort;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Port name
    int pinNum() const { return m_pinNum; }  // * = Pin number, for order based instantiation
};
class AstPragma final : public AstNode {
    const VPragmaType m_pragType;  // Type of pragma
public:
    // Pragmas don't result in any output code, they're just flags that affect
    // other processing in verilator.
    AstPragma(FileLine* fl, VPragmaType pragType)
        : ASTGEN_SUPER_Pragma(fl)
        , m_pragType{pragType} {}
    ASTGEN_MEMBERS_AstPragma;
    VPragmaType pragType() const { return m_pragType; }  // *=type of the pragma
    bool isPredictOptimizable() const override { return false; }
    bool same(const AstNode* samep) const override {
        return pragType() == static_cast<const AstPragma*>(samep)->pragType();
    }
};
class AstPropSpec final : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
    // @astgen op1 := sensesp : Optional[AstSenItem]
    // @astgen op2 := disablep : Optional[AstNodeExpr]
    // @astgen op3 := propp : AstNode
public:
    AstPropSpec(FileLine* fl, AstSenItem* sensesp, AstNodeExpr* disablep, AstNode* propp)
        : ASTGEN_SUPER_PropSpec(fl) {
        this->sensesp(sensesp);
        this->disablep(disablep);
        this->propp(propp);
    }
    ASTGEN_MEMBERS_AstPropSpec;
    bool hasDType() const override {
        return true;
    }  // Used under Cover, which expects a bool child
};
class AstPull final : public AstNode {
    // @astgen op1 := lhsp : AstNodeExpr

    const bool m_direction;

public:
    AstPull(FileLine* fl, AstNodeExpr* lhsp, bool direction)
        : ASTGEN_SUPER_Pull(fl)
        , m_direction{direction} {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstPull;
    bool same(const AstNode* samep) const override {
        return direction() == static_cast<const AstPull*>(samep)->direction();
    }
    uint32_t direction() const { return (uint32_t)m_direction; }
};
class AstScope final : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
    // @astgen op1 := varsp : List[AstVarScope]
    // @astgen op2 := blocksp : List[AstNode] // Logic blocks/AstActive/AstCFunc

    // An AstScope->name() is special: . indicates an uninlined scope, __DOT__ an inlined scope
    string m_name;  // Name
    AstScope* const m_aboveScopep;  // Scope above this one in the hierarchy (nullptr if top)
    AstCell* const m_aboveCellp;  // Cell above this in the hierarchy (nullptr if top)
    AstNodeModule* const m_modp;  // Module scope corresponds to
public:
    AstScope(FileLine* fl, AstNodeModule* modp, const string& name, AstScope* aboveScopep,
             AstCell* aboveCellp)
        : ASTGEN_SUPER_Scope(fl)
        , m_name{name}
        , m_aboveScopep{aboveScopep}
        , m_aboveCellp{aboveCellp}
        , m_modp{modp} {}
    ASTGEN_MEMBERS_AstScope;
    void cloneRelink() override;
    const char* broken() const override;
    bool maybePointedTo() const override { return true; }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Scope name
    void name(const string& name) override { m_name = name; }
    void dump(std::ostream& str) const override;
    bool same(const AstNode* samep) const override;
    string nameDotless() const;
    AstNodeModule* modp() const { return m_modp; }
    //
    AstScope* aboveScopep() const VL_MT_SAFE { return m_aboveScopep; }
    AstCell* aboveCellp() const { return m_aboveCellp; }
    bool isTop() const VL_MT_SAFE { return aboveScopep() == nullptr; }  // At top of hierarchy
    // Create new MODULETEMP variable under this scope
    AstVarScope* createTemp(const string& name, unsigned width);
    AstVarScope* createTemp(const string& name, AstNodeDType* dtypep);
    AstVarScope* createTempLike(const string& name, AstVarScope* vscp);
};
class AstSenItem final : public AstNode {
    // Parents:  SENTREE
    // @astgen op1 := sensp : Optional[AstNodeExpr] // Sensitivity expression
    VEdgeType m_edgeType;  // Edge type
public:
    class Combo {};  // for constructor type-overload selection
    class Illegal {};  // for constructor type-overload selection
    class Static {};  // for constructor type-overload selection
    class Initial {};  // for constructor type-overload selection
    class Final {};  // for constructor type-overload selection
    class Never {};  // for constructor type-overload selection
    AstSenItem(FileLine* fl, VEdgeType edgeType, AstNodeExpr* senp)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{edgeType} {
        this->sensp(senp);
    }
    AstSenItem(FileLine* fl, Combo)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_COMBO} {}
    AstSenItem(FileLine* fl, Illegal)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_ILLEGAL} {}
    AstSenItem(FileLine* fl, Static)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_STATIC} {}
    AstSenItem(FileLine* fl, Initial)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_INITIAL} {}
    AstSenItem(FileLine* fl, Final)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_FINAL} {}
    AstSenItem(FileLine* fl, Never)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_NEVER} {}
    ASTGEN_MEMBERS_AstSenItem;
    void dump(std::ostream& str) const override;
    bool same(const AstNode* samep) const override {
        return edgeType() == static_cast<const AstSenItem*>(samep)->edgeType();
    }
    VEdgeType edgeType() const { return m_edgeType; }
    void edgeType(VEdgeType type) {
        m_edgeType = type;
        editCountInc();
    }
    AstNodeVarRef* varrefp() const { return VN_CAST(sensp(), NodeVarRef); }
    //
    bool isClocked() const { return edgeType().clockedStmt(); }
    bool isCombo() const { return edgeType() == VEdgeType::ET_COMBO; }
    bool isHybrid() const { return edgeType() == VEdgeType::ET_HYBRID; }
    bool isStatic() const { return edgeType() == VEdgeType::ET_STATIC; }
    bool isInitial() const { return edgeType() == VEdgeType::ET_INITIAL; }
    bool isFinal() const { return edgeType() == VEdgeType::ET_FINAL; }
    bool isIllegal() const { return edgeType() == VEdgeType::ET_ILLEGAL; }
    bool isNever() const { return edgeType() == VEdgeType::ET_NEVER; }
};
class AstSenTree final : public AstNode {
    // A sensitivity list
    // @astgen op1 := sensesp : List[AstSenItem]
    bool m_multi = false;  // Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstSenItem* sensesp)
        : ASTGEN_SUPER_SenTree(fl) {
        this->addSensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstSenTree;
    void dump(std::ostream& str) const override;
    bool maybePointedTo() const override { return true; }
    bool isMulti() const { return m_multi; }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    bool hasClocked() const;  // Includes a clocked statement
    bool hasStatic() const;  // Includes a STATIC SenItem
    bool hasInitial() const;  // Includes a INITIAL SenItem
    bool hasFinal() const;  // Includes a FINAL SenItem
    bool hasCombo() const;  // Includes a COMBO SenItem
    bool hasHybrid() const;  // Includes a HYBRID SenItem
};
class AstSplitPlaceholder final : public AstNode {
public:
    // Dummy node used within V3Split; never exists outside of V3Split.
    explicit AstSplitPlaceholder(FileLine* fl)
        : ASTGEN_SUPER_SplitPlaceholder(fl) {}
    ASTGEN_MEMBERS_AstSplitPlaceholder;
};
class AstStrengthSpec final : public AstNode {
private:
    VStrength m_s0;  // Drive 0 strength
    VStrength m_s1;  // Drive 1 strength

public:
    AstStrengthSpec(FileLine* fl, VStrength s0, VStrength s1)
        : ASTGEN_SUPER_StrengthSpec(fl)
        , m_s0{s0}
        , m_s1{s1} {}

    ASTGEN_MEMBERS_AstStrengthSpec;
    VStrength strength0() { return m_s0; }
    VStrength strength1() { return m_s1; }
    void dump(std::ostream& str) const override;
};
class AstTopScope final : public AstNode {
    // A singleton, held under the top level AstModule. Holds the top level
    // AstScope, and after V3ActiveTop, the global list of AstSenTrees (list of
    // unique sensitivity lists).
    //
    // @astgen op1 := senTreesp : List[AstSenTree] // Globally unique sensitivity lists
    // @astgen op2 := scopep : AstScope // The AstScope of the top-leveL

    friend class AstNetlist;  // Only the AstNetlist can create one
    AstTopScope(FileLine* fl, AstScope* ascopep)
        : ASTGEN_SUPER_TopScope(fl) {
        this->scopep(ascopep);
    }

public:
    ASTGEN_MEMBERS_AstTopScope;
    bool maybePointedTo() const override { return true; }
};
class AstTypeTable final : public AstNode {
    // Container for hash of standard data types
    // @astgen op1 := typesp : List[AstNodeDType]
    AstEmptyQueueDType* m_emptyQueuep = nullptr;
    AstQueueDType* m_queueIndexp = nullptr;
    AstVoidDType* m_voidp = nullptr;
    AstStreamDType* m_streamp = nullptr;
    AstBasicDType* m_basicps[VBasicDTypeKwd::_ENUM_MAX]{};
    //
    using DetailedMap = std::map<VBasicTypeKey, AstBasicDType*>;
    DetailedMap m_detailedMap;

public:
    explicit AstTypeTable(FileLine* fl);
    ASTGEN_MEMBERS_AstTypeTable;
    bool maybePointedTo() const override { return true; }
    const char* broken() const override {
        BROKEN_RTN(m_emptyQueuep && !m_emptyQueuep->brokeExists());
        BROKEN_RTN(m_queueIndexp && !m_queueIndexp->brokeExists());
        BROKEN_RTN(m_voidp && !m_voidp->brokeExists());
        return nullptr;
    }
    void cloneRelink() override { V3ERROR_NA; }
    AstBasicDType* findBasicDType(FileLine* fl, VBasicDTypeKwd kwd);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, int width, int widthMin,
                                     VSigning numeric);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, const VNumRange& range,
                                     int widthMin, VSigning numeric);
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);
    AstEmptyQueueDType* findEmptyQueueDType(FileLine* fl);
    AstQueueDType* findQueueIndexDType(FileLine* fl);
    AstVoidDType* findVoidDType(FileLine* fl);
    AstStreamDType* findStreamDType(FileLine* fl);
    void clearCache();
    void repairCache();
    void dump(std::ostream& str = std::cout) const override;
};
class AstTypedef final : public AstNode {
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op4 := attrsp : List[AstNode] // Attributes during early parse

    string m_name;
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
    bool m_attrPublic = false;

public:
    AstTypedef(FileLine* fl, const string& name, AstNode* attrsp, VFlagChildDType,
               AstNodeDType* dtp)
        : ASTGEN_SUPER_Typedef(fl)
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        addAttrsp(attrsp);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_AstTypedef;
    void dump(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* subDTypep() const VL_MT_STABLE {
        return dtypep() ? dtypep() : childDTypep();
    }
    // METHODS
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override { return true; }
    bool hasDType() const override { return true; }
    void name(const string& flag) override { m_name = flag; }
    bool attrPublic() const { return m_attrPublic; }
    void attrPublic(bool flag) { m_attrPublic = flag; }
    void tag(const string& text) override { m_tag = text; }
    string tag() const override { return m_tag; }
};
class AstTypedefFwd final : public AstNode {
    // Forward declaration of a type; stripped after netlist parsing is complete
private:
    string m_name;

public:
    AstTypedefFwd(FileLine* fl, const string& name)
        : ASTGEN_SUPER_TypedefFwd(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstTypedefFwd;
    // METHODS
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override { return true; }
};
class AstUdpTable final : public AstNode {
    // @astgen op1 := linesp : List[AstUdpTableLine]
public:
    AstUdpTable(FileLine* fl, AstUdpTableLine* linesp)
        : ASTGEN_SUPER_UdpTable(fl) {
        this->addLinesp(linesp);
    }
    ASTGEN_MEMBERS_AstUdpTable;
};
class AstUdpTableLine final : public AstNode {
    string m_text;

public:
    AstUdpTableLine(FileLine* fl, const string& text)
        : ASTGEN_SUPER_UdpTableLine(fl)
        , m_text{text} {}
    ASTGEN_MEMBERS_AstUdpTableLine;
    string name() const override VL_MT_STABLE { return m_text; }
    string text() const { return m_text; }
};
class AstVar final : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
    //
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := delayp : Optional[AstDelay] // Net delay
    // Initial value that never changes (static const), or constructor argument for
    // MTASKSTATE variables
    // @astgen op3 := valuep : Optional[AstNode] // May be a DType for type parameter defaults
    // @astgen op4 := attrsp : List[AstNode] // Attributes during early parse

    string m_name;  // Name of variable
    string m_origName;  // Original name before dot addition
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
    VVarType m_varType;  // Type of variable
    VDirection m_direction;  // Direction input/output etc
    VDirection m_declDirection;  // Declared direction input/output etc
    VBasicDTypeKwd m_declKwd;  // Keyword at declaration time
    VLifetime m_lifetime;  // Lifetime
    VVarAttrClocker m_attrClocker;
    MTaskIdSet m_mtaskIds;  // MTaskID's that read or write this var
    int m_pinNum = 0;  // For XML, if non-zero the connection pin number
    bool m_ansi : 1;  // Params or pins declared in the module header, rather than the body
    bool m_declTyped : 1;  // Declared as type (for dedup check)
    bool m_tristate : 1;  // Inout or triwire or trireg
    bool m_primaryIO : 1;  // In/out to top level (or directly assigned from same)
    bool m_sc : 1;  // SystemC variable
    bool m_scClocked : 1;  // SystemC sc_clk<> needed
    bool m_scSensitive : 1;  // SystemC sensitive() needed
    bool m_sigPublic : 1;  // User C code accesses this signal or is top signal
    bool m_sigModPublic : 1;  // User C code accesses this signal and module
    bool m_sigUserRdPublic : 1;  // User C code accesses this signal, read only
    bool m_sigUserRWPublic : 1;  // User C code accesses this signal, read-write
    bool m_usedClock : 1;  // Signal used as a clock
    bool m_usedParam : 1;  // Parameter is referenced (on link; later signals not setup)
    bool m_usedLoopIdx : 1;  // Variable subject of for unrolling
    bool m_usedVirtIface : 1;  // Signal used through a virtual interface
    bool m_funcLocal : 1;  // Local variable for a function
    bool m_funcLocalSticky : 1;  // As m_funcLocal but remains set if var is moved to a static
    bool m_funcReturn : 1;  // Return variable for a function
    bool m_attrScBv : 1;  // User force bit vector attribute
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_attrSFormat : 1;  // User sformat attribute
    bool m_attrSplitVar : 1;  // declared with split_var metacomment
    bool m_fileDescr : 1;  // File descriptor
    bool m_isRand : 1;  // Random variable
    bool m_isRandC : 1;  // Random cyclic variable (isRand also set)
    bool m_isConst : 1;  // Table contains constant data
    bool m_isContinuously : 1;  // Ever assigned continuously (for force/release)
    bool m_hasStrengthAssignment : 1;  // Is on LHS of assignment with strength specifier
    bool m_isStatic : 1;  // Static C variable (for Verilog see instead isAutomatic)
    bool m_isPulldown : 1;  // Tri0
    bool m_isPullup : 1;  // Tri1
    bool m_isIfaceParent : 1;  // dtype is reference to interface present in this module
    bool m_isInternal : 1;  // Internal state, don't add to method pinter
    bool m_isDpiOpenArray : 1;  // DPI import open array
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_noReset : 1;  // Do not do automated reset/randomization
    bool m_noSubst : 1;  // Do not substitute out references
    bool m_overridenParam : 1;  // Overridden parameter by #(...) or defparam
    bool m_trace : 1;  // Trace this variable
    bool m_isLatched : 1;  // Not assigned in all control paths of combo always
    bool m_isForceable : 1;  // May be forced/released externally from user C code
    bool m_isWrittenByDpi : 1;  // This variable can be written by a DPI Export
    bool m_isWrittenBySuspendable : 1;  // This variable can be written by a suspendable process

    void init() {
        m_ansi = false;
        m_declTyped = false;
        m_tristate = false;
        m_primaryIO = false;
        m_sc = false;
        m_scClocked = false;
        m_scSensitive = false;
        m_usedClock = false;
        m_usedParam = false;
        m_usedLoopIdx = false;
        m_usedVirtIface = false;
        m_sigPublic = false;
        m_sigModPublic = false;
        m_sigUserRdPublic = false;
        m_sigUserRWPublic = false;
        m_funcLocal = false;
        m_funcLocalSticky = false;
        m_funcReturn = false;
        m_attrScBv = false;
        m_attrIsolateAssign = false;
        m_attrSFormat = false;
        m_attrSplitVar = false;
        m_fileDescr = false;
        m_isRand = false;
        m_isRandC = false;
        m_isConst = false;
        m_isContinuously = false;
        m_hasStrengthAssignment = false;
        m_isStatic = false;
        m_isPulldown = false;
        m_isPullup = false;
        m_isIfaceParent = false;
        m_isInternal = false;
        m_isDpiOpenArray = false;
        m_isHideLocal = false;
        m_isHideProtected = false;
        m_noReset = false;
        m_noSubst = false;
        m_overridenParam = false;
        m_trace = false;
        m_isLatched = false;
        m_isForceable = false;
        m_isWrittenByDpi = false;
        m_isWrittenBySuspendable = false;
        m_attrClocker = VVarAttrClocker::CLOCKER_UNKNOWN;
    }

public:
    AstVar(FileLine* fl, VVarType type, const string& name, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        childDTypep(dtp);  // Only for parser
        dtypep(nullptr);  // V3Width will resolve
        if (dtp->basicp()) {
            m_declKwd = dtp->basicp()->keyword();
        } else {
            m_declKwd = VBasicDTypeKwd::LOGIC;
        }
    }
    AstVar(FileLine* fl, VVarType type, const string& name, AstNodeDType* dtp)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        UASSERT(dtp, "AstVar created with no dtype");
        dtypep(dtp);
        if (dtp->basicp()) {
            m_declKwd = dtp->basicp()->keyword();
        } else {
            m_declKwd = VBasicDTypeKwd::LOGIC;
        }
    }
    AstVar(FileLine* fl, VVarType type, const string& name, VFlagLogicPacked, int wantwidth)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetLogicSized(wantwidth, VSigning::UNSIGNED);
        m_declKwd = VBasicDTypeKwd::LOGIC;
    }
    AstVar(FileLine* fl, VVarType type, const string& name, VFlagBitPacked, int wantwidth)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetBitSized(wantwidth, VSigning::UNSIGNED);
        m_declKwd = VBasicDTypeKwd::BIT;
    }
    AstVar(FileLine* fl, VVarType type, const string& name, AstVar* examplep)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        if (examplep->childDTypep()) childDTypep(examplep->childDTypep()->cloneTree(true));
        dtypeFrom(examplep);
        m_declKwd = examplep->declKwd();
    }
    ASTGEN_MEMBERS_AstVar;
    void dump(std::ostream& str) const override;
    bool same(const AstNode* samep) const override;
    string name() const override VL_MT_STABLE VL_MT_SAFE { return m_name; }  // * = Var name
    bool hasDType() const override { return true; }
    bool maybePointedTo() const override { return true; }
    string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    VVarType varType() const VL_MT_SAFE { return m_varType; }  // * = Type of variable
    void direction(const VDirection& flag) {
        m_direction = flag;
        if (m_direction == VDirection::INOUT) m_tristate = true;
    }
    VDirection direction() const VL_MT_SAFE { return m_direction; }
    bool isIO() const VL_MT_SAFE { return m_direction != VDirection::NONE; }
    void declDirection(const VDirection& flag) { m_declDirection = flag; }
    VDirection declDirection() const { return m_declDirection; }
    void varType(VVarType type) { m_varType = type; }
    void varType2Out() {
        m_tristate = false;
        m_direction = VDirection::OUTPUT;
    }
    void varType2In() {
        m_tristate = false;
        m_direction = VDirection::INPUT;
    }
    VBasicDTypeKwd declKwd() const { return m_declKwd; }
    string scType() const;  // Return SysC type: bool, uint32_t, uint64_t, sc_bv
    // Return C /*public*/ type for argument: bool, uint32_t, uint64_t, etc.
    string cPubArgType(bool named, bool forReturn) const;
    string dpiArgType(bool named, bool forReturn) const;  // Return DPI-C type for argument
    string dpiTmpVarType(const string& varName) const;
    // Return Verilator internal type for argument: CData, SData, IData, WData
    string vlArgType(bool named, bool forReturn, bool forFunc, const string& namespc = "",
                     bool asRef = false) const;
    string vlEnumType() const;  // Return VerilatorVarType: VLVT_UINT32, etc
    string vlEnumDir() const;  // Return VerilatorVarDir: VLVD_INOUT, etc
    string vlPropDecl(const string& propName) const;  // Return VerilatorVarProps declaration
    void combineType(VVarType type);
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* dtypeSkipRefp() const VL_MT_STABLE { return subDTypep()->skipRefp(); }
    // (Slow) recurse down to find basic data type (Note don't need virtual -
    // AstVar isn't a NodeDType)
    AstBasicDType* basicp() const VL_MT_STABLE { return subDTypep()->basicp(); }
    virtual AstNodeDType* subDTypep() const VL_MT_STABLE {
        return dtypep() ? dtypep() : childDTypep();
    }
    void ansi(bool flag) { m_ansi = flag; }
    void declTyped(bool flag) { m_declTyped = flag; }
    void attrClocker(VVarAttrClocker flag) { m_attrClocker = flag; }
    void attrFileDescr(bool flag) { m_fileDescr = flag; }
    void attrScClocked(bool flag) { m_scClocked = flag; }
    void attrScBv(bool flag) { m_attrScBv = flag; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    void attrSFormat(bool flag) { m_attrSFormat = flag; }
    void attrSplitVar(bool flag) { m_attrSplitVar = flag; }
    void usedClock(bool flag) { m_usedClock = flag; }
    void usedParam(bool flag) { m_usedParam = flag; }
    void usedLoopIdx(bool flag) { m_usedLoopIdx = flag; }
    void usedVirtIface(bool flag) { m_usedVirtIface = flag; }
    void sigPublic(bool flag) { m_sigPublic = flag; }
    void sigModPublic(bool flag) { m_sigModPublic = flag; }
    void sigUserRdPublic(bool flag) {
        m_sigUserRdPublic = flag;
        if (flag) sigPublic(true);
    }
    void sigUserRWPublic(bool flag) {
        m_sigUserRWPublic = flag;
        if (flag) sigUserRdPublic(true);
    }
    void sc(bool flag) { m_sc = flag; }
    void scSensitive(bool flag) { m_scSensitive = flag; }
    void primaryIO(bool flag) { m_primaryIO = flag; }
    void isRand(bool flag) { m_isRand = flag; }
    void isRandC(bool flag) {
        m_isRandC = flag;
        if (flag) isRand(true);
    }
    void isConst(bool flag) { m_isConst = flag; }
    void isContinuously(bool flag) { m_isContinuously = flag; }
    void isStatic(bool flag) { m_isStatic = flag; }
    void isIfaceParent(bool flag) { m_isIfaceParent = flag; }
    void isInternal(bool flag) { m_isInternal = flag; }
    void funcLocal(bool flag) {
        m_funcLocal = flag;
        if (flag) m_funcLocalSticky = true;
    }
    void funcReturn(bool flag) { m_funcReturn = flag; }
    void hasStrengthAssignment(bool flag) { m_hasStrengthAssignment = flag; }
    bool hasStrengthAssignment() { return m_hasStrengthAssignment; }
    void isDpiOpenArray(bool flag) { m_isDpiOpenArray = flag; }
    bool isDpiOpenArray() const VL_MT_SAFE { return m_isDpiOpenArray; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    void noReset(bool flag) { m_noReset = flag; }
    bool noReset() const { return m_noReset; }
    void noSubst(bool flag) { m_noSubst = flag; }
    bool noSubst() const { return m_noSubst; }
    void overriddenParam(bool flag) { m_overridenParam = flag; }
    bool overriddenParam() const { return m_overridenParam; }
    void trace(bool flag) { m_trace = flag; }
    void isLatched(bool flag) { m_isLatched = flag; }
    bool isForceable() const { return m_isForceable; }
    void setForceable() { m_isForceable = true; }
    bool isWrittenByDpi() const { return m_isWrittenByDpi; }
    void setWrittenByDpi() { m_isWrittenByDpi = true; }
    bool isWrittenBySuspendable() const { return m_isWrittenBySuspendable; }
    void setWrittenBySuspendable() { m_isWrittenBySuspendable = true; }

    // METHODS
    void name(const string& name) override { m_name = name; }
    void tag(const string& text) override { m_tag = text; }
    string tag() const override { return m_tag; }
    bool isAnsi() const { return m_ansi; }
    bool isContinuously() const { return m_isContinuously; }
    bool isDeclTyped() const { return m_declTyped; }
    bool isInoutish() const { return m_direction.isInoutish(); }
    bool isNonOutput() const { return m_direction.isNonOutput(); }
    bool isReadOnly() const VL_MT_SAFE { return m_direction.isReadOnly(); }
    bool isConstRef() const VL_MT_SAFE { return m_direction.isConstRef(); }
    bool isRef() const VL_MT_SAFE { return m_direction.isRef(); }
    bool isWritable() const VL_MT_SAFE { return m_direction.isWritable(); }
    bool isTristate() const { return m_tristate; }
    bool isPrimaryIO() const { return m_primaryIO; }
    bool isPrimaryInish() const { return isPrimaryIO() && isNonOutput(); }
    bool isIfaceRef() const { return (varType() == VVarType::IFACEREF); }
    bool isIfaceParent() const { return m_isIfaceParent; }
    bool isInternal() const { return m_isInternal; }
    bool isSignal() const { return varType().isSignal(); }
    bool isNet() const { return varType().isNet(); }
    bool isTemp() const { return varType().isTemp(); }
    bool isToggleCoverable() const {
        return ((isIO() || isSignal())
                && (isIO() || isBitLogic())
                // Wrapper would otherwise duplicate wrapped module's coverage
                && !isSc() && !isPrimaryIO() && !isConst() && !isDouble() && !isString());
    }
    bool isClassMember() const { return varType() == VVarType::MEMBER; }
    bool isStatementTemp() const { return (varType() == VVarType::STMTTEMP); }
    bool isXTemp() const { return (varType() == VVarType::XTEMP); }
    bool isParam() const { return varType().isParam(); }
    bool isGParam() const { return (varType() == VVarType::GPARAM); }
    bool isGenVar() const { return (varType() == VVarType::GENVAR); }
    bool isBitLogic() const {
        AstBasicDType* bdtypep = basicp();
        return bdtypep && bdtypep->isBitLogic();
    }
    bool isUsedClock() const { return m_usedClock; }
    bool isUsedParam() const { return m_usedParam; }
    bool isUsedLoopIdx() const { return m_usedLoopIdx; }
    bool isUsedVirtIface() const { return m_usedVirtIface; }
    bool isSc() const VL_MT_SAFE { return m_sc; }
    bool isScQuad() const;
    bool isScBv() const;
    bool isScUint() const;
    bool isScBigUint() const;
    bool isScSensitive() const { return m_scSensitive; }
    bool isSigPublic() const;
    bool isSigModPublic() const { return m_sigModPublic; }
    bool isSigUserRdPublic() const { return m_sigUserRdPublic; }
    bool isSigUserRWPublic() const { return m_sigUserRWPublic; }
    bool isTrace() const { return m_trace; }
    bool isRand() const { return m_isRand; }
    bool isRandC() const { return m_isRandC; }
    bool isConst() const VL_MT_SAFE { return m_isConst; }
    bool isStatic() const VL_MT_SAFE { return m_isStatic; }
    bool isLatched() const { return m_isLatched; }
    bool isFuncLocal() const { return m_funcLocal; }
    bool isFuncLocalSticky() const { return m_funcLocalSticky; }
    bool isFuncReturn() const { return m_funcReturn; }
    bool isPullup() const { return m_isPullup; }
    bool isPulldown() const { return m_isPulldown; }
    bool attrScBv() const { return m_attrScBv; }
    bool attrFileDescr() const { return m_fileDescr; }
    bool attrScClocked() const { return m_scClocked; }
    bool attrSFormat() const { return m_attrSFormat; }
    bool attrSplitVar() const { return m_attrSplitVar; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    VVarAttrClocker attrClocker() const { return m_attrClocker; }
    string verilogKwd() const override;
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void propagateAttrFrom(const AstVar* fromp) {
        // This is getting connected to fromp; keep attributes
        // Note the method below too
        if (fromp->attrFileDescr()) attrFileDescr(true);
        if (fromp->attrIsolateAssign()) attrIsolateAssign(true);
        if (fromp->isContinuously()) isContinuously(true);
    }
    void propagateWrapAttrFrom(const AstVar* fromp) {
        // Creating a function wrapper; keep attributes
        propagateAttrFrom(fromp);
        direction(fromp->direction());
        declDirection(fromp->declDirection());
        lifetime(fromp->lifetime());
    }
    bool gateMultiInputOptimizable() const {
        // Ok to gate optimize; must return false if propagateAttrFrom would do anything
        return !isUsedClock();
    }
    void combineType(const AstVar* typevarp) {
        // This is same as typevarp (for combining input & reg decls)
        // "this" is the input var. typevarp is the reg var.
        propagateAttrFrom(typevarp);
        combineType(typevarp->varType());
        if (typevarp->isSigPublic()) sigPublic(true);
        if (typevarp->isSigModPublic()) sigModPublic(true);
        if (typevarp->isSigUserRdPublic()) sigUserRdPublic(true);
        if (typevarp->isSigUserRWPublic()) sigUserRWPublic(true);
        if (typevarp->attrScClocked()) attrScClocked(true);
    }
    void inlineAttrReset(const string& name) {
        if (direction() == VDirection::INOUT && varType() == VVarType::WIRE) {
            m_varType = VVarType::TRIWIRE;
        }
        m_direction = VDirection::NONE;
        m_name = name;
    }
    static AstVar* scVarRecurse(AstNode* nodep);
    void addProducingMTaskId(int id) { m_mtaskIds.insert(id); }
    void addConsumingMTaskId(int id) { m_mtaskIds.insert(id); }
    const MTaskIdSet& mtaskIds() const { return m_mtaskIds; }
    void pinNum(int id) { m_pinNum = id; }
    int pinNum() const { return m_pinNum; }
};
class AstVarScope final : public AstNode {
    // A particular scoped usage of a variable
    // That is, as a module is used under multiple cells, we get a different
    // varscope for each var in the module
    // Parents: MODULE
    // Children: none
private:
    AstScope* m_scopep;  // Scope variable is underneath
    AstVar* m_varp;  // [AfterLink] Pointer to variable itself
    bool m_trace : 1;  // Tracing is turned on for this scope
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
        : ASTGEN_SUPER_VarScope(fl)
        , m_scopep{scopep}
        , m_varp{varp} {
        UASSERT_OBJ(scopep, fl, "Scope must be non-null");
        UASSERT_OBJ(varp, fl, "Var must be non-null");
        m_trace = true;
        dtypeFrom(varp);
    }
    ASTGEN_MEMBERS_AstVarScope;
    void cloneRelink() override {
        if (m_varp && m_varp->clonep()) {
            m_varp = m_varp->clonep();
            UASSERT(m_scopep->clonep(), "No clone cross link: " << this);
            m_scopep = m_scopep->clonep();
        }
    }
    const char* broken() const override {
        BROKEN_RTN(m_varp && !m_varp->brokeExists());
        BROKEN_RTN(m_scopep && !m_scopep->brokeExists());
        return nullptr;
    }
    bool maybePointedTo() const override { return true; }
    string name() const override VL_MT_STABLE { return scopep()->name() + "->" + varp()->name(); }
    void dump(std::ostream& str) const override;
    bool same(const AstNode* samep) const override;
    bool hasDType() const override { return true; }
    AstVar* varp() const VL_MT_STABLE { return m_varp; }  // [After Link] Pointer to variable
    AstScope* scopep() const VL_MT_STABLE { return m_scopep; }  // Pointer to scope it's under
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    bool isTrace() const { return m_trace; }
    void trace(bool flag) { m_trace = flag; }
};

// === AstNodeBlock ===
class AstBegin final : public AstNodeBlock {
    // A Begin/end named block, only exists shortly after parsing until linking
    // Parents: statement
    // @astgen op1 := genforp : Optional[AstNode]

    bool m_generate;  // Underneath a generate
    const bool m_implied;  // Not inserted by user
public:
    // Node that puts name into the output stream
    AstBegin(FileLine* fl, const string& name, AstNode* stmtsp, bool generate = false,
             bool implied = false)
        : ASTGEN_SUPER_Begin(fl, name, stmtsp)
        , m_generate{generate}
        , m_implied{implied} {}
    ASTGEN_MEMBERS_AstBegin;
    void dump(std::ostream& str) const override;
    void generate(bool flag) { m_generate = flag; }
    bool generate() const { return m_generate; }
    bool implied() const { return m_implied; }
};
class AstFork final : public AstNodeBlock {
    // A fork named block
    // @astgen op1 := initsp : List[AstNode]
    // Parents: statement
    // Children: statements
private:
    VJoinType m_joinType;  // Join keyword type
public:
    // Node that puts name into the output stream
    AstFork(FileLine* fl, const string& name, AstNode* stmtsp)
        : ASTGEN_SUPER_Fork(fl, name, stmtsp) {}
    ASTGEN_MEMBERS_AstFork;
    bool isTimingControl() const override { return !joinType().joinNone(); }
    void dump(std::ostream& str) const override;
    VJoinType joinType() const { return m_joinType; }
    void joinType(const VJoinType& flag) { m_joinType = flag; }
};

// === AstNodeFTask ===
class AstFunc final : public AstNodeFTask {
    // A function inside a module
public:
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarp)
        : ASTGEN_SUPER_Func(fl, name, stmtp) {
        this->fvarp(fvarp);
    }
    ASTGEN_MEMBERS_AstFunc;
    bool hasDType() const override { return true; }
    AstNodeFTask* cloneType(const string& name) override {
        return new AstFunc{fileline(), name, nullptr, nullptr};
    }
};
class AstLet final : public AstNodeFTask {
    // Verilog "let" statement
    // Parents: MODULE
    // stmtp is always a StmtExpr as Let always returns AstNodeExpr
public:
    AstLet(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Let(fl, name, nullptr) {}
    ASTGEN_MEMBERS_AstLet;
    bool hasDType() const override { return true; }
    const char* broken() const override {
        BROKEN_RTN(!VN_IS(stmtsp(), StmtExpr));
        return nullptr;
    }
    AstNodeFTask* cloneType(const string& name) override { return new AstLet{fileline(), name}; }
};
class AstProperty final : public AstNodeFTask {
    // A property inside a module
public:
    AstProperty(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER_Property(fl, name, stmtp) {}
    ASTGEN_MEMBERS_AstProperty;
    bool hasDType() const override { return true; }
    AstNodeFTask* cloneType(const string& name) override {
        return new AstProperty{fileline(), name, nullptr};
    }
};
class AstTask final : public AstNodeFTask {
    // A task inside a module
public:
    AstTask(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER_Task(fl, name, stmtp) {}
    ASTGEN_MEMBERS_AstTask;
    AstNodeFTask* cloneType(const string& name) override {
        return new AstTask{fileline(), name, nullptr};
    }
};

// === AstNodeFile ===
class AstCFile final : public AstNodeFile {
    // C++ output file
    // Parents:  NETLIST
private:
    bool m_slow : 1;  ///< Compile w/o optimization
    bool m_source : 1;  ///< Source file (vs header file)
    bool m_support : 1;  ///< Support file (non systemc)
public:
    AstCFile(FileLine* fl, const string& name)
        : ASTGEN_SUPER_CFile(fl, name)
        , m_slow{false}
        , m_source{false}
        , m_support{false} {}
    ASTGEN_MEMBERS_AstCFile;
    void dump(std::ostream& str = std::cout) const override;
    bool slow() const { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool source() const { return m_source; }
    void source(bool flag) { m_source = flag; }
    bool support() const { return m_support; }
    void support(bool flag) VL_MT_SAFE { m_support = flag; }
};
class AstVFile final : public AstNodeFile {
    // Verilog output file
    // Parents:  NETLIST
public:
    AstVFile(FileLine* fl, const string& name)
        : ASTGEN_SUPER_VFile(fl, name) {}
    ASTGEN_MEMBERS_AstVFile;
    void dump(std::ostream& str = std::cout) const override;
};

// === AstNodeModule ===
class AstClass final : public AstNodeModule {
    // @astgen op4 := extendsp : List[AstClassExtends]
    // MEMBERS
    AstClassPackage* m_classOrPackagep = nullptr;  // Package it will be emitted with
    bool m_extended = false;  // Is extension or extended by other classes
    bool m_interfaceClass = false;  // Interface class
    bool m_needRNG = false;  // Need RNG, uses srandom/randomize
    bool m_virtual = false;  // Virtual class
    bool m_parameterized = false;  // Parameterized class

public:
    AstClass(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Class(fl, name) {}
    ASTGEN_MEMBERS_AstClass;
    string verilogKwd() const override { return "class"; }
    bool maybePointedTo() const override { return true; }
    void dump(std::ostream& str) const override;
    const char* broken() const override;
    void cloneRelink() override;
    bool timescaleMatters() const override { return false; }
    AstClassPackage* classOrPackagep() const VL_MT_SAFE { return m_classOrPackagep; }
    void classOrPackagep(AstClassPackage* classpackagep) { m_classOrPackagep = classpackagep; }
    AstNode* membersp() const { return stmtsp(); }
    void addMembersp(AstNode* nodep) { addStmtsp(nodep); }
    bool isExtended() const { return m_extended; }
    void isExtended(bool flag) { m_extended = flag; }
    bool isInterfaceClass() const { return m_interfaceClass; }
    void isInterfaceClass(bool flag) { m_interfaceClass = flag; }
    bool isVirtual() const { return m_virtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool needRNG() const { return m_needRNG; }
    void needRNG(bool flag) { m_needRNG = flag; }
    bool isParameterized() const { return m_parameterized; }
    void isParameterized(bool flag) { m_parameterized = flag; }
    // Return true if this class is an extension of base class (SLOW)
    // Accepts nullptrs
    static bool isClassExtendedFrom(const AstClass* refClassp, const AstClass* baseClassp);
    // Return the lowest class extended from, or this class
    AstClass* baseMostClassp();
    static bool isCacheableChild(const AstNode* nodep);
};
class AstClassPackage final : public AstNodeModule {
    // The static information portion of a class (treated similarly to a package)
    AstClass* m_classp
        = nullptr;  // Class package this is under (weak pointer, hard link is other way)
public:
    AstClassPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER_ClassPackage(fl, name) {}
    ASTGEN_MEMBERS_AstClassPackage;
    string verilogKwd() const override { return "classpackage"; }
    const char* broken() const override;
    void cloneRelink() override;
    bool timescaleMatters() const override { return false; }
    AstClass* classp() const VL_MT_SAFE { return m_classp; }
    void classp(AstClass* classp) { m_classp = classp; }
};
class AstIface final : public AstNodeModule {
    // A module declaration
public:
    AstIface(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Iface(fl, name) {}
    ASTGEN_MEMBERS_AstIface;
    // Interfaces have `timescale applicability but lots of code seems to
    // get false warnings if we enable this
    string verilogKwd() const override { return "interface"; }
    bool timescaleMatters() const override { return false; }
};
class AstModule final : public AstNodeModule {
    // A module declaration
private:
    const bool m_isProgram;  // Module represents a program
public:
    AstModule(FileLine* fl, const string& name, bool program = false)
        : ASTGEN_SUPER_Module(fl, name)
        , m_isProgram{program} {}
    ASTGEN_MEMBERS_AstModule;
    string verilogKwd() const override { return m_isProgram ? "program" : "module"; }
    bool timescaleMatters() const override { return true; }
};
class AstNotFoundModule final : public AstNodeModule {
    // A missing module declaration
public:
    AstNotFoundModule(FileLine* fl, const string& name)
        : ASTGEN_SUPER_NotFoundModule(fl, name) {}
    ASTGEN_MEMBERS_AstNotFoundModule;
    string verilogKwd() const override { return "/*not-found-*/ module"; }
    bool timescaleMatters() const override { return false; }
};
class AstPackage final : public AstNodeModule {
    // A package declaration
public:
    AstPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Package(fl, name) {}
    ASTGEN_MEMBERS_AstPackage;
    string verilogKwd() const override { return "package"; }
    bool timescaleMatters() const override { return !isDollarUnit(); }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};
class AstPrimitive final : public AstNodeModule {
    // A primitive declaration
public:
    AstPrimitive(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Primitive(fl, name) {}
    ASTGEN_MEMBERS_AstPrimitive;
    string verilogKwd() const override { return "primitive"; }
    bool timescaleMatters() const override { return false; }
};

// === AstNodeProcedure ===
class AstAlways final : public AstNodeProcedure {
    // @astgen op1 := sensesp : Optional[AstSenTree] // Sensitivity list iff clocked
    const VAlwaysKwd m_keyword;

public:
    AstAlways(FileLine* fl, VAlwaysKwd keyword, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER_Always(fl, stmtsp)
        , m_keyword{keyword} {
        this->sensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstAlways;
    //
    void dump(std::ostream& str) const override;
    VAlwaysKwd keyword() const { return m_keyword; }
};
class AstAlwaysObserved final : public AstNodeProcedure {
    // Like always but Observed scheduling region
    // @astgen op1 := sensesp : Optional[AstSenTree] // Sensitivity list, removed in V3Active

public:
    AstAlwaysObserved(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysObserved(fl, bodysp) {
        this->sensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstAlwaysObserved;
};
class AstAlwaysPost final : public AstNodeProcedure {
    // Like always but post assignments for memory assignment IFs
    // @astgen op1 := sensesp : Optional[AstSenTree] // Sensitivity list iff clocked
public:
    AstAlwaysPost(FileLine* fl, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER_AlwaysPost(fl, stmtsp) {
        this->sensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstAlwaysPost;
};
class AstAlwaysPostponed final : public AstNodeProcedure {
    // Like always but Postponed scheduling region

public:
    AstAlwaysPostponed(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_AlwaysPostponed(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstAlwaysPostponed;
};
class AstAlwaysReactive final : public AstNodeProcedure {
    // Like always but Reactive scheduling region
    // @astgen op1 := sensesp : Optional[AstSenTree] // Sensitivity list, removed in V3Active

public:
    AstAlwaysReactive(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysReactive(fl, bodysp) {
        this->sensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstAlwaysReactive;
};
class AstFinal final : public AstNodeProcedure {
public:
    AstFinal(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_Final(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstFinal;
};
class AstInitial final : public AstNodeProcedure {
public:
    AstInitial(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_Initial(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstInitial;
};
class AstInitialAutomatic final : public AstNodeProcedure {
    // Automatic variable initialization
    // That is, it runs every function start, or class construction
public:
    AstInitialAutomatic(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_InitialAutomatic(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstInitialAutomatic;
};
class AstInitialStatic final : public AstNodeProcedure {
    // Static variable initialization
    // That is, it runs at the beginning of simulation, before 'initial' blocks
public:
    AstInitialStatic(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_InitialStatic(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstInitialStatic;
};

// === AstNodeRange ===
class AstBracketRange final : public AstNodeRange {
    // Parser only concept "[lhsp]", an AstUnknownRange, QueueRange or Range,
    // unknown until lhsp type is determined
    // @astgen op1 := elementsp : AstNode // Expr or DType
public:
    AstBracketRange(FileLine* fl, AstNode* elementsp)
        : ASTGEN_SUPER_BracketRange(fl) {
        this->elementsp(elementsp);
    }
    ASTGEN_MEMBERS_AstBracketRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { V3ERROR_NA_RETURN(""); }
    bool same(const AstNode* /*samep*/) const override { return true; }
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    bool maybePointedTo() const override { return false; }
};
class AstRange final : public AstNodeRange {
    // Range specification, for use under variables and cells
    // @astgen op1 := leftp : AstNodeExpr
    // @astgen op2 := rightp : AstNodeExpr
public:
    AstRange(FileLine* fl, AstNodeExpr* leftp, AstNodeExpr* rightp)
        : ASTGEN_SUPER_Range(fl) {
        this->leftp(leftp);
        this->rightp(rightp);
    }
    inline AstRange(FileLine* fl, int left, int right);
    inline AstRange(FileLine* fl, const VNumRange& range);
    ASTGEN_MEMBERS_AstRange;
    inline int leftConst() const VL_MT_STABLE;
    inline int rightConst() const VL_MT_STABLE;
    int hiConst() const VL_MT_STABLE {
        const int l = leftConst();
        const int r = rightConst();
        return l > r ? l : r;
    }
    int loConst() const VL_MT_STABLE {
        const int l = leftConst();
        const int r = rightConst();
        return l > r ? r : l;
    }
    int elementsConst() const VL_MT_STABLE { return hiConst() - loConst() + 1; }
    bool ascending() const { return leftConst() < rightConst(); }
    void dump(std::ostream& str) const override;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstUnsizedRange final : public AstNodeRange {
    // Unsized range specification, for open arrays
public:
    explicit AstUnsizedRange(FileLine* fl)
        : ASTGEN_SUPER_UnsizedRange(fl) {}
    ASTGEN_MEMBERS_AstUnsizedRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[]"; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstWildcardRange final : public AstNodeRange {
    // Wildcard range specification, for wildcard index type associative arrays
public:
    explicit AstWildcardRange(FileLine* fl)
        : ASTGEN_SUPER_WildcardRange(fl) {}
    ASTGEN_MEMBERS_AstWildcardRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[*]"; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};

// === AstNodeStmt ===
class AstAlwaysPublic final : public AstNodeStmt {
    // "Fake" sensitivity created by /*verilator public_flat_rw @(edgelist)*/
    // Body statements are just AstVarRefs to the public signals
    // @astgen op1 := sensesp : List[AstSenTree]
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstAlwaysPublic(FileLine* fl, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER_AlwaysPublic(fl) {
        addSensesp(sensesp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstAlwaysPublic;
    bool same(const AstNode* /*samep*/) const override { return true; }
    // Special accessors
    bool isJustOneBodyStmt() const { return stmtsp() && !stmtsp()->nextp(); }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
};
class AstBreak final : public AstNodeStmt {
public:
    explicit AstBreak(FileLine* fl)
        : ASTGEN_SUPER_Break(fl) {}
    ASTGEN_MEMBERS_AstBreak;
    string verilogKwd() const override { return "break"; }
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstCReset final : public AstNodeStmt {
    // Reset variable at startup
    // @astgen op1 := varrefp : AstVarRef
public:
    AstCReset(FileLine* fl, AstVarRef* varrefp)
        : ASTGEN_SUPER_CReset(fl) {
        this->varrefp(varrefp);
    }
    ASTGEN_MEMBERS_AstCReset;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstCStmt final : public AstNodeStmt {
    // Emit C statement
    // @astgen op1 := exprsp : List[AstNode]
public:
    AstCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_CStmt(fl) {
        this->addExprsp(exprsp);
    }
    inline AstCStmt(FileLine* fl, const string& textStmt);
    ASTGEN_MEMBERS_AstCStmt;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* samep) const override { return true; }  // Ignore name in comments
    virtual bool showAt() const { return m_showAt; }
};
class AstContinue final : public AstNodeStmt {
public:
    explicit AstContinue(FileLine* fl)
        : ASTGEN_SUPER_Continue(fl) {}
    ASTGEN_MEMBERS_AstContinue;
    string verilogKwd() const override { return "continue"; }
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstCoverDecl final : public AstNodeStmt {
    // Coverage analysis point declaration
    AstCoverDecl* m_dataDeclp = nullptr;  // [After V3CoverageJoin] Pointer to duplicate
                                          // declaration to get data from instead
    string m_page;
    string m_text;
    string m_hier;
    string m_linescov;
    int m_offset;  // Offset column numbers to uniq-ify IFs
    int m_binNum = 0;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    AstCoverDecl(FileLine* fl, const string& page, const string& comment, const string& linescov,
                 int offset)
        : ASTGEN_SUPER_CoverDecl(fl)
        , m_page{page}
        , m_text{comment}
        , m_linescov{linescov}
        , m_offset{offset} {}
    ASTGEN_MEMBERS_AstCoverDecl;
    const char* broken() const override {
        BROKEN_RTN(m_dataDeclp && !m_dataDeclp->brokeExists());
        if (m_dataDeclp && m_dataDeclp->m_dataDeclp) {  // Avoid O(n^2) accessing
            v3fatalSrc("dataDeclp should point to real data, not be a list");
        }
        return nullptr;
    }
    void cloneRelink() override {
        if (m_dataDeclp && m_dataDeclp->clonep()) m_dataDeclp = m_dataDeclp->clonep();
    }
    void dump(std::ostream& str) const override;
    int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    bool maybePointedTo() const override { return true; }
    void binNum(int flag) { m_binNum = flag; }
    int binNum() const { return m_binNum; }
    int offset() const { return m_offset; }
    const string& comment() const { return m_text; }  // text to insert in code
    const string& linescov() const { return m_linescov; }
    const string& page() const { return m_page; }
    const string& hier() const { return m_hier; }
    void hier(const string& flag) { m_hier = flag; }
    void comment(const string& flag) { m_text = flag; }
    bool same(const AstNode* samep) const override {
        const AstCoverDecl* const asamep = static_cast<const AstCoverDecl*>(samep);
        return (fileline() == asamep->fileline() && linescov() == asamep->linescov()
                && hier() == asamep->hier() && comment() == asamep->comment());
    }
    bool isPredictOptimizable() const override { return false; }
    void dataDeclp(AstCoverDecl* nodep) { m_dataDeclp = nodep; }
    // dataDecl nullptr means "use this one", but often you want "this" to
    // indicate to get data from here
    AstCoverDecl* dataDeclNullp() const { return m_dataDeclp; }
    AstCoverDecl* dataDeclThisp() { return dataDeclNullp() ? dataDeclNullp() : this; }
};
class AstCoverInc final : public AstNodeStmt {
    // Coverage analysis point; increment coverage count
    AstCoverDecl* m_declp;  // [After V3Coverage] Pointer to declaration
public:
    AstCoverInc(FileLine* fl, AstCoverDecl* declp)
        : ASTGEN_SUPER_CoverInc(fl)
        , m_declp{declp} {}
    ASTGEN_MEMBERS_AstCoverInc;
    const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    void dump(std::ostream& str) const override;
    int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstCoverInc*>(samep)->declp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    // but isPure()  true
    AstCoverDecl* declp() const { return m_declp; }  // Where defined
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
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    const bool m_isCycle;  // True if it is a cycle delay

public:
    AstDelay(FileLine* fl, AstNodeExpr* lhsp, bool isCycle)
        : ASTGEN_SUPER_Delay(fl)
        , m_isCycle{isCycle} {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstDelay;
    void dump(std::ostream& str) const override;
    bool isTimingControl() const override { return true; }
    bool isCycleDelay() const { return m_isCycle; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstDisable final : public AstNodeStmt {
    string m_name;  // Name of block
public:
    AstDisable(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Disable(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstDisable;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Block name
    void name(const string& flag) override { m_name = flag; }
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
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
private:
    VDisplayType m_displayType;

public:
    AstDisplay(FileLine* fl, VDisplayType dispType, const string& text, AstNodeExpr* filep,
               AstNodeExpr* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        this->fmtp(new AstSFormatF{fl, text, true, exprsp, missingArgChar});
        this->filep(filep);
    }
    AstDisplay(FileLine* fl, VDisplayType dispType, AstNodeExpr* filep, AstNodeExpr* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        this->fmtp(new AstSFormatF{fl, AstSFormatF::NoFormat{}, exprsp, missingArgChar});
        this->filep(filep);
    }
    ASTGEN_MEMBERS_AstDisplay;
    void dump(std::ostream& str) const override;
    const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    string verilogKwd() const override {
        return (filep() ? string{"$f"} + string{displayType().ascii()}
                        : string{"$"} + string{displayType().ascii()});
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstDisplay*>(samep)->displayType();
    }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    VDisplayType displayType() const { return m_displayType; }
    void displayType(VDisplayType type) { m_displayType = type; }
    // * = Add a newline for $display
    bool addNewline() const { return displayType().addNewline(); }
};
class AstDoWhile final : public AstNodeStmt {
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstDoWhile(FileLine* fl, AstNodeExpr* conditionp, AstNode* stmtsp = nullptr)
        : ASTGEN_SUPER_DoWhile(fl) {
        condp(conditionp);
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstDoWhile;
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    // Stop statement searchback here
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
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
    bool isPredictOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    virtual bool cleanOut() const { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    VDumpCtlType ctlType() const { return m_ctlType; }
};
class AstEventControl final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := sensesp : Optional[AstSenTree]
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstEventControl(FileLine* fl, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER_EventControl(fl) {
        this->sensesp(sensesp);
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstEventControl;
    string verilogKwd() const override { return "@(%l) %r"; }
    bool isTimingControl() const override { return true; }
    int instrCount() const override { return 0; }
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
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* samep) const override { return fileline() == samep->fileline(); }
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
class AstForeach final : public AstNodeStmt {
    // @astgen op1 := arrayp : AstNode
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstForeach(FileLine* fl, AstNode* arrayp, AstNode* stmtsp)
        : ASTGEN_SUPER_Foreach(fl) {
        this->arrayp(arrayp);
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstForeach;
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
};
class AstJumpBlock final : public AstNodeStmt {
    // Block of code including a single JumpLabel, and 0+ JumpGo's to that label
    // Parents:  {statement list}
    // Children: {statement list, with JumpGo and JumpLabel below}
    // @astgen op1 := stmtsp : List[AstNode]
    // @astgen op2 := endStmtsp : List[AstNode]
private:
    AstJumpLabel* m_labelp = nullptr;  // [After V3Jump] Pointer to declaration
    int m_labelNum = 0;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    // After construction must call ->labelp to associate with appropriate label
    AstJumpBlock(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_JumpBlock(fl) {
        this->addStmtsp(stmtsp);
    }
    const char* broken() const override;
    void cloneRelink() override;
    ASTGEN_MEMBERS_AstJumpBlock;
    int instrCount() const override { return 0; }
    bool maybePointedTo() const override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    int labelNum() const { return m_labelNum; }
    void labelNum(int flag) { m_labelNum = flag; }
    AstJumpLabel* labelp() const { return m_labelp; }
    void labelp(AstJumpLabel* labelp) { m_labelp = labelp; }
};
class AstJumpGo final : public AstNodeStmt {
    // Jump point; branch down to a JumpLabel
    // No support for backward jumps at present
    // Parents:  {statement list with JumpBlock above}
    // Children: none
private:
    AstJumpLabel* m_labelp;  // [After V3Jump] Pointer to declaration
public:
    AstJumpGo(FileLine* fl, AstJumpLabel* labelp)
        : ASTGEN_SUPER_JumpGo(fl)
        , m_labelp{labelp} {}
    ASTGEN_MEMBERS_AstJumpGo;
    const char* broken() const override;
    void cloneRelink() override;
    void dump(std::ostream& str) const override;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* samep) const override {
        return labelp() == static_cast<const AstJumpGo*>(samep)->labelp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
    AstJumpLabel* labelp() const { return m_labelp; }
};
class AstJumpLabel final : public AstNodeStmt {
    // Jump point declaration
    // Parents:  {statement list with JumpBlock above}
    // Children: none
private:
    AstJumpBlock* m_blockp;  // [After V3Jump] Pointer to declaration
public:
    AstJumpLabel(FileLine* fl, AstJumpBlock* blockp)
        : ASTGEN_SUPER_JumpLabel(fl)
        , m_blockp{blockp} {}
    ASTGEN_MEMBERS_AstJumpLabel;
    bool maybePointedTo() const override { return true; }
    const char* broken() const override {
        BROKEN_RTN(!blockp()->brokeExistsAbove());
        BROKEN_RTN(blockp()->labelp() != this);
        return nullptr;
    }
    void cloneRelink() override {
        if (m_blockp->clonep()) m_blockp = m_blockp->clonep();
    }
    void dump(std::ostream& str) const override;
    int instrCount() const override { return 0; }
    bool same(const AstNode* samep) const override {
        return blockp() == static_cast<const AstJumpLabel*>(samep)->blockp();
    }
    AstJumpBlock* blockp() const { return m_blockp; }
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
    bool same(const AstNode* samep) const override {
        return m_off == static_cast<const AstMonitorOff*>(samep)->m_off;
    }
    bool off() const { return m_off; }
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
    string verilogKwd() const override { return "$printtimescale"; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    int instrCount() const override { return INSTR_COUNT_PLI; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstRandCase final : public AstNodeStmt {
    // @astgen op2 := itemsp : List[AstCaseItem]
public:
    AstRandCase(FileLine* fl, AstCaseItem* itemsp)
        : ASTGEN_SUPER_RandCase(fl) {
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstRandCase;
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
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
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstRepeat;
    bool isGateOptimizable() const override { return false; }  // Not relevant - converted to FOR
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
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
    bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstSFormat final : public AstNodeStmt {
    // Parents: statement container
    // @astgen op1 := fmtp : AstSFormatF
    // @astgen op2 := lhsp : AstNodeExpr
public:
    AstSFormat(FileLine* fl, AstNodeExpr* lhsp, const string& text, AstNodeExpr* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        this->fmtp(new AstSFormatF{fl, text, true, exprsp, missingArgChar});
        this->lhsp(lhsp);
    }
    AstSFormat(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        this->fmtp(new AstSFormatF{fl, AstSFormatF::NoFormat{}, exprsp, missingArgChar});
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
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* /*samep*/) const override { return true; }
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
};
class AstStop final : public AstNodeStmt {
public:
    AstStop(FileLine* fl, bool maybe)
        : ASTGEN_SUPER_Stop(fl) {}
    ASTGEN_MEMBERS_AstStop;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    int instrCount() const override { return 0; }  // Rarely executes
    bool same(const AstNode* samep) const override { return fileline() == samep->fileline(); }
};
class AstSysFuncAsTask final : public AstNodeStmt {
    // TODO: This is superseded by AstStmtExpr, remove
    // Call what is normally a system function (with a return) in a non-return context
    // @astgen op1 := lhsp : AstNodeExpr
public:
    AstSysFuncAsTask(FileLine* fl, AstNodeExpr* lhsp)
        : ASTGEN_SUPER_SysFuncAsTask(fl) {
        this->lhsp(lhsp);
    }
    ASTGEN_MEMBERS_AstSysFuncAsTask;
    string verilogKwd() const override { return ""; }
    bool isGateOptimizable() const override { return true; }
    bool isPredictOptimizable() const override { return true; }
    bool isPure() override { return true; }
    bool isOutputter() override { return false; }
    int instrCount() const override { return 0; }
    bool same(const AstNode* /*samep*/) const override { return true; }
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
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstTimeFormat final : public AstNodeStmt {
    // Parents: stmtlist
    // @astgen op1 := unitsp : AstNodeExpr
    // @astgen op2 := precisionp : AstNodeExpr
    // @astgen op3 := suffixp : AstNodeExpr
    // @astgen op4 := widthp : AstNodeExpr
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
private:
    uint32_t m_code = 0;  // Trace identifier code; converted to ASCII by trace routines
    const string m_showname;  // Name of variable
    const VNumRange m_bitRange;  // Property of var the trace details
    const VNumRange m_arrayRange;  // Property of var the trace details
    const uint32_t m_codeInc;  // Code increment
    const VVarType m_varType;  // Type of variable (for localparam vs. param)
    const VBasicDTypeKwd m_declKwd;  // Keyword at declaration time
    const VDirection m_declDirection;  // Declared direction input/output etc
public:
    AstTraceDecl(FileLine* fl, const string& showname,
                 AstVar* varp,  // For input/output state etc
                 AstNodeExpr* valuep, const VNumRange& bitRange, const VNumRange& arrayRange)
        : ASTGEN_SUPER_TraceDecl(fl)
        , m_showname{showname}
        , m_bitRange{bitRange}
        , m_arrayRange{arrayRange}
        , m_codeInc(
              ((arrayRange.ranged() ? arrayRange.elements() : 1) * valuep->dtypep()->widthWords()
               * (VL_EDATASIZE / 32)))  // A code is always 32-bits
        , m_varType{varp->varType()}
        , m_declKwd{varp->declKwd()}
        , m_declDirection{varp->declDirection()} {
        dtypeFrom(valuep);
        this->valuep(valuep);
    }
    void dump(std::ostream& str) const override;
    int instrCount() const override { return 100; }  // Large...
    ASTGEN_MEMBERS_AstTraceDecl;
    string name() const override VL_MT_STABLE { return m_showname; }
    bool maybePointedTo() const override { return true; }
    bool hasDType() const override { return true; }
    bool same(const AstNode* samep) const override { return false; }
    string showname() const { return m_showname; }  // * = Var name
    // Details on what we're tracing
    uint32_t code() const { return m_code; }
    void code(uint32_t code) { m_code = code; }
    uint32_t codeInc() const { return m_codeInc; }
    const VNumRange& bitRange() const { return m_bitRange; }
    const VNumRange& arrayRange() const { return m_arrayRange; }
    VVarType varType() const { return m_varType; }
    VBasicDTypeKwd declKwd() const { return m_declKwd; }
    VDirection declDirection() const { return m_declDirection; }
};
class AstTraceInc final : public AstNodeStmt {
    // Trace point dump
    // @astgen op1 := precondsp : List[AstNode] // Statements to emit before this node
    // @astgen op2 := valuep : AstNodeExpr // Expression being traced (from decl)

private:
    AstTraceDecl* m_declp;  // Pointer to declaration
    const uint32_t m_baseCode;  // Trace code base value in function containing this AstTraceInc
    const bool m_full;  // Is this a full vs incremental dump

public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, bool full, uint32_t baseCode = 0)
        : ASTGEN_SUPER_TraceInc(fl)
        , m_declp{declp}
        , m_baseCode{baseCode}
        , m_full{full} {
        dtypeFrom(declp);
        this->valuep(
            declp->valuep()->cloneTree(true));  // TODO: maybe use reference to TraceDecl instead?
    }
    ASTGEN_MEMBERS_AstTraceInc;
    const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    void dump(std::ostream& str) const override;
    int instrCount() const override { return 10 + 2 * INSTR_COUNT_LD; }
    bool hasDType() const override { return true; }
    bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstTraceInc*>(samep)->declp();
    }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isOutputter() override { return true; }
    // but isPure()  true
    AstTraceDecl* declp() const { return m_declp; }
    bool full() const { return m_full; }
    uint32_t baseCode() const { return m_baseCode; }
};
class AstTracePopNamePrefix final : public AstNodeStmt {
    const unsigned m_count;  // How many levels to pop
public:
    AstTracePopNamePrefix(FileLine* fl, unsigned count)
        : ASTGEN_SUPER_TracePopNamePrefix(fl)
        , m_count{count} {}
    ASTGEN_MEMBERS_AstTracePopNamePrefix;
    bool same(const AstNode* samep) const override { return false; }
    unsigned count() const { return m_count; }
};
class AstTracePushNamePrefix final : public AstNodeStmt {
    const string m_prefix;  // Prefix to add to signal names
public:
    AstTracePushNamePrefix(FileLine* fl, const string& prefix)
        : ASTGEN_SUPER_TracePushNamePrefix(fl)
        , m_prefix{prefix} {}
    ASTGEN_MEMBERS_AstTracePushNamePrefix;
    bool same(const AstNode* samep) const override { return false; }
    string prefix() const { return m_prefix; }
};
class AstUCStmt final : public AstNodeStmt {
    // User $c statement
    // @astgen op1 := exprsp : List[AstNode] // (some are AstText)
public:
    AstUCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_UCStmt(fl) {
        this->addExprsp(exprsp);
    }
    ASTGEN_MEMBERS_AstUCStmt;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
    bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstWait final : public AstNodeStmt {
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := stmtsp : List[AstNode]
public:
    AstWait(FileLine* fl, AstNodeExpr* condp, AstNode* stmtsp)
        : ASTGEN_SUPER_Wait(fl) {
        this->condp(condp);
        this->addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstWait;
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
    bool isTimingControl() const override { return true; }
};
class AstWaitFork final : public AstNodeStmt {
    // A "wait fork" statement
public:
    explicit AstWaitFork(FileLine* fl)
        : ASTGEN_SUPER_WaitFork(fl) {}
    ASTGEN_MEMBERS_AstWaitFork;
};
class AstWhile final : public AstNodeStmt {
    // @astgen op1 := precondsp : List[AstNode]
    // @astgen op2 := condp : AstNodeExpr
    // @astgen op3 := stmtsp : List[AstNode]
    // @astgen op4 := incsp : List[AstNode]
public:
    AstWhile(FileLine* fl, AstNodeExpr* condp, AstNode* stmtsp = nullptr, AstNode* incsp = nullptr)
        : ASTGEN_SUPER_While(fl) {
        this->condp(condp);
        this->addStmtsp(stmtsp);
        this->addIncsp(incsp);
    }
    ASTGEN_MEMBERS_AstWhile;
    bool isGateOptimizable() const override { return false; }
    int instrCount() const override { return INSTR_COUNT_BRANCH; }
    bool same(const AstNode* /*samep*/) const override { return true; }
    // Stop statement searchback here
    void addNextStmt(AstNode* newp, AstNode* belowp) override;
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
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
    bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignAlias final : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
public:
    AstAssignAlias(FileLine* fl, AstVarRef* lhsp, AstVarRef* rhsp)
        : ASTGEN_SUPER_AssignAlias(fl, (AstNodeExpr*)lhsp, (AstNodeExpr*)rhsp) {}
    ASTGEN_MEMBERS_AstAssignAlias;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        V3ERROR_NA_RETURN(nullptr);
    }
    bool brokeLhsMustBeLvalue() const override { return false; }
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
    bool brokeLhsMustBeLvalue() const override { return true; }
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
    bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignPost final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPost(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AssignPost(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstAssignPost;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAssignPost{fileline(), lhsp, rhsp};
    }
    bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignPre final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPre(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AssignPre(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AstAssignPre;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAssignPre{fileline(), lhsp, rhsp};
    }
    bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignVarScope final : public AstNodeAssign {
    // Assign two VarScopes to each other
public:
    AstAssignVarScope(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AssignVarScope(fl, lhsp, rhsp) {
        dtypeFrom(rhsp);
    }
    ASTGEN_MEMBERS_AstAssignVarScope;
    AstNodeAssign* cloneType(AstNodeExpr* lhsp, AstNodeExpr* rhsp) override {
        return new AstAssignVarScope{fileline(), lhsp, rhsp};
    }
    bool brokeLhsMustBeLvalue() const override { return false; }
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
    bool brokeLhsMustBeLvalue() const override { return true; }
    AstAlways* convertToAlways();
};

// === AstNodeCase ===
class AstCase final : public AstNodeCase {
    // Case statement
    VCaseType m_casex;  // 0=case, 1=casex, 2=casez
    bool m_fullPragma = false;  // Synthesis full_case
    bool m_parallelPragma = false;  // Synthesis parallel_case
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstCase(FileLine* fl, VCaseType casex, AstNodeExpr* exprp, AstCaseItem* itemsp)
        : ASTGEN_SUPER_Case(fl, exprp, itemsp)
        , m_casex{casex} {}
    ASTGEN_MEMBERS_AstCase;
    string verilogKwd() const override { return casez() ? "casez" : casex() ? "casex" : "case"; }
    bool same(const AstNode* samep) const override {
        return m_casex == static_cast<const AstCase*>(samep)->m_casex;
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
};
class AstGenCase final : public AstNodeCase {
    // Generate Case statement
public:
    AstGenCase(FileLine* fl, AstNodeExpr* exprp, AstCaseItem* itemsp)
        : ASTGEN_SUPER_GenCase(fl, exprp, itemsp) {}
    ASTGEN_MEMBERS_AstGenCase;
};

// === AstNodeCoverOrAssert ===
class AstAssert final : public AstNodeCoverOrAssert {
    // @astgen op3 := failsp: List[AstNode] // Statements when propp is failing/falsey
public:
    ASTGEN_MEMBERS_AstAssert;
    AstAssert(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp, bool immediate,
              const string& name = "")
        : ASTGEN_SUPER_Assert(fl, propp, passsp, immediate, name) {
        this->addFailsp(failsp);
    }
};
class AstAssertIntrinsic final : public AstNodeCoverOrAssert {
    // A $cast or other compiler inserted assert, that must run even without --assert option
    // @astgen op3 := failsp: List[AstNode] // Statements when propp is failing/falsey
public:
    ASTGEN_MEMBERS_AstAssertIntrinsic;
    AstAssertIntrinsic(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp,
                       bool immediate, const string& name = "")
        : ASTGEN_SUPER_AssertIntrinsic(fl, propp, passsp, immediate, name) {
        this->addFailsp(failsp);
    }
};
class AstCover final : public AstNodeCoverOrAssert {
    // @astgen op3 := coverincsp: List[AstNode] // Coverage node
public:
    ASTGEN_MEMBERS_AstCover;
    AstCover(FileLine* fl, AstNode* propp, AstNode* stmtsp, bool immediate,
             const string& name = "")
        : ASTGEN_SUPER_Cover(fl, propp, stmtsp, immediate, name) {}
    virtual bool immediate() const { return false; }
};
class AstRestrict final : public AstNodeCoverOrAssert {
public:
    ASTGEN_MEMBERS_AstRestrict;
    AstRestrict(FileLine* fl, AstNode* propp)
        : ASTGEN_SUPER_Restrict(fl, propp, nullptr, false, "") {}
};

// === AstNodeFor ===
class AstGenFor final : public AstNodeFor {
public:
    AstGenFor(FileLine* fl, AstNode* initsp, AstNodeExpr* condp, AstNode* incsp, AstNode* stmtsp)
        : ASTGEN_SUPER_GenFor(fl, initsp, condp, incsp, stmtsp) {}
    ASTGEN_MEMBERS_AstGenFor;
};

// === AstNodeIf ===
class AstGenIf final : public AstNodeIf {
public:
    AstGenIf(FileLine* fl, AstNodeExpr* condp, AstNode* thensp, AstNode* elsesp)
        : ASTGEN_SUPER_GenIf(fl, condp, thensp, elsesp) {}
    ASTGEN_MEMBERS_AstGenIf;
};
class AstIf final : public AstNodeIf {
private:
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

// === AstNodeText ===
class AstScCtor final : public AstNodeText {
public:
    AstScCtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScCtor(fl, textp) {}
    ASTGEN_MEMBERS_AstScCtor;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};
class AstScDtor final : public AstNodeText {
public:
    AstScDtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScDtor(fl, textp) {}
    ASTGEN_MEMBERS_AstScDtor;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};
class AstScHdr final : public AstNodeText {
public:
    AstScHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScHdr(fl, textp) {}
    ASTGEN_MEMBERS_AstScHdr;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};
class AstScImp final : public AstNodeText {
public:
    AstScImp(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScImp(fl, textp) {}
    ASTGEN_MEMBERS_AstScImp;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};
class AstScImpHdr final : public AstNodeText {
public:
    AstScImpHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScImpHdr(fl, textp) {}
    ASTGEN_MEMBERS_AstScImpHdr;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};
class AstScInt final : public AstNodeText {
public:
    AstScInt(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScInt(fl, textp) {}
    ASTGEN_MEMBERS_AstScInt;
    bool isPure() override { return false; }  // SPECIAL: User may order w/other sigs
    bool isOutputter() override { return true; }
};

// === AstNodeSimpleText ===
class AstText final : public AstNodeSimpleText {
public:
    AstText(FileLine* fl, const string& textp, bool tracking = false)
        : ASTGEN_SUPER_Text(fl, textp, tracking) {}
    ASTGEN_MEMBERS_AstText;
};
class AstTextBlock final : public AstNodeSimpleText {
    // @astgen op1 := nodesp : List[AstNode]
    bool m_commas;  // Comma separate emitted children
public:
    explicit AstTextBlock(FileLine* fl, const string& textp = "", bool tracking = false,
                          bool commas = false)
        : ASTGEN_SUPER_TextBlock(fl, textp, tracking)
        , m_commas(commas) {}
    ASTGEN_MEMBERS_AstTextBlock;
    void commas(bool flag) { m_commas = flag; }
    bool commas() const { return m_commas; }
    void addText(FileLine* fl, const string& textp, bool tracking = false) {
        addNodesp(new AstText{fl, textp, tracking});
    }
};

#endif  // Guard
