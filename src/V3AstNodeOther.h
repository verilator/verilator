// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing other constructs
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
// This files contains all 'AstNode' sub-types that relate to other constructs
// not covered by the more speficic V3AstNode*.h files.
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
    // Parents: statement
    // Children: statements
private:
    string m_name;  // Name of block
    bool m_unnamed;  // Originally unnamed (name change does not affect this)
protected:
    AstNodeBlock(VNType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name} {
        addNOp1p(stmtsp);
        m_unnamed = (name == "");
    }

public:
    ASTGEN_MEMBERS_NodeBlock;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Block name
    virtual void name(const string& name) override { m_name = name; }
    // op1 = Statements
    AstNode* stmtsp() const { return op1p(); }  // op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    bool unnamed() const { return m_unnamed; }
    bool isFirstInMyListOfStatements(AstNode* nodep) const override { return nodep == stmtsp(); }
};
class AstNodeFTask VL_NOT_FINAL : public AstNode {
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
    bool m_pure : 1;  // DPI import pure (vs. virtual pure)
    bool m_pureVirtual : 1;  // Pure virtual
    bool m_recursive : 1;  // Recusive or part of recursion
    bool m_underGenerate : 1;  // Under generate (for warning)
    bool m_virtual : 1;  // Virtual method in class
    VLifetime m_lifetime;  // Lifetime
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
        , m_pure{false}
        , m_pureVirtual{false}
        , m_recursive{false}
        , m_underGenerate{false}
        , m_virtual{false} {
        addNOp3p(stmtsp);
        cname(name);  // Might be overridden by dpi import/export
    }

public:
    ASTGEN_MEMBERS_NodeFTask;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool maybePointedTo() const override { return true; }
    virtual bool isGateOptimizable() const override {
        return !((m_dpiExport || m_dpiImport) && !m_pure);
    }
    // {AstFunc only} op1 = Range output variable
    virtual void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
    // op1 = Output variable (functions only, nullptr for tasks)
    AstNode* fvarp() const { return op1p(); }
    void addFvarp(AstNode* nodep) { addNOp1p(nodep); }
    bool isFunction() const { return fvarp() != nullptr; }
    // op2 = Class/package scope
    AstNode* classOrPackagep() const { return op2p(); }
    void classOrPackagep(AstNode* nodep) { setNOp2p(nodep); }
    // op3 = Statements/Ports/Vars
    AstNode* stmtsp() const { return op3p(); }  // op3 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp3p(nodep); }
    // op4 = scope name
    AstScopeName* scopeNamep() const { return VN_AS(op4p(), ScopeName); }
    // MORE ACCESSORS
    void dpiOpenParentInc() { ++m_dpiOpenParent; }
    void dpiOpenParentClear() { m_dpiOpenParent = 0; }
    uint64_t dpiOpenParent() const { return m_dpiOpenParent; }
    void scopeNamep(AstNode* nodep) { setNOp4p(nodep); }
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
    void pure(bool flag) { m_pure = flag; }
    bool pure() const { return m_pure; }
    void pureVirtual(bool flag) { m_pureVirtual = flag; }
    bool pureVirtual() const { return m_pureVirtual; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void underGenerate(bool flag) { m_underGenerate = flag; }
    bool underGenerate() const { return m_underGenerate; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool isVirtual() const { return m_virtual; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == stmtsp(); }
};
class AstNodeFile VL_NOT_FINAL : public AstNode {
    // Emitted Otput file
    // Parents:  NETLIST
    // Children: AstTextBlock
private:
    string m_name;  ///< Filename
public:
    AstNodeFile(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name} {}
    ASTGEN_MEMBERS_NodeFile;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    void tblockp(AstTextBlock* tblockp) { setOp1p((AstNode*)tblockp); }
    AstTextBlock* tblockp() { return VN_AS(op1p(), TextBlock); }
};
class AstNodeModule VL_NOT_FINAL : public AstNode {
    // A module, package, program or interface declaration;
    // something that can live directly under the TOP,
    // excluding $unit package stuff
private:
    string m_name;  // Name of the module
    const string m_origName;  // Name of the module, ignoring name() changes, for dot lookup
    string m_someInstanceName;  // Hierarchical name of some arbitrary instance of this module.
                                // Used for user messages only.
    bool m_modPublic : 1;  // Module has public references
    bool m_modTrace : 1;  // Tracing this module
    bool m_inLibrary : 1;  // From a library, no error if not used, never top level
    bool m_dead : 1;  // LinkDot believes is dead; will remove in Dead visitors
    bool m_hierBlock : 1;  // Hiearchical Block marked by HIER_BLOCK pragma
    bool m_internal : 1;  // Internally created
    bool m_recursive : 1;  // Recursive module
    bool m_recursiveClone : 1;  // If recursive, what module it clones, otherwise nullptr
    int m_level = 0;  // 1=top module, 2=cell off top module, ...
    VLifetime m_lifetime;  // Lifetime
    VTimescale m_timeunit;  // Global time unit
    VOptionBool m_unconnectedDrive;  // State of `unconnected_drive
protected:
    AstNodeModule(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name}
        , m_origName{name}
        , m_modPublic{false}
        , m_modTrace{false}
        , m_inLibrary{false}
        , m_dead{false}
        , m_hierBlock{false}
        , m_internal{false}
        , m_recursive{false}
        , m_recursiveClone{false} {}

public:
    ASTGEN_MEMBERS_NodeModule;
    virtual void dump(std::ostream& str) const override;
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return m_name; }
    virtual bool timescaleMatters() const = 0;
    AstNode* stmtsp() const { return op2p(); }  // op2 = List of statements
    AstActive* activesp() const { return VN_AS(op3p(), Active); }  // op3 = List of i/sblocks
    // METHODS
    void addInlinesp(AstNode* nodep) { addOp1p(nodep); }
    void addStmtp(AstNode* nodep) { addNOp2p(nodep); }
    void addActivep(AstNode* nodep) { addOp3p(nodep); }
    // ACCESSORS
    virtual void name(const string& name) override { m_name = name; }
    virtual string origName() const override { return m_origName; }
    string someInstanceName() const { return m_someInstanceName; }
    void someInstanceName(const string& name) { m_someInstanceName = name; }
    bool inLibrary() const { return m_inLibrary; }
    void inLibrary(bool flag) { m_inLibrary = flag; }
    void level(int level) { m_level = level; }
    int level() const { return m_level; }
    bool isTop() const { return level() == 1; }
    void modPublic(bool flag) { m_modPublic = flag; }
    bool modPublic() const { return m_modPublic; }
    void modTrace(bool flag) { m_modTrace = flag; }
    bool modTrace() const { return m_modTrace; }
    void dead(bool flag) { m_dead = flag; }
    bool dead() const { return m_dead; }
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
class AstNodePreSel VL_NOT_FINAL : public AstNode {
    // Something that becomes an AstSel
protected:
    AstNodePreSel(VNType t, FileLine* fl, AstNode* fromp, AstNode* rhs, AstNode* ths)
        : AstNode{t, fl} {
        setOp1p(fromp);
        setOp2p(rhs);
        setNOp3p(ths);
    }

public:
    ASTGEN_MEMBERS_NodePreSel;
    AstNode* fromp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    AstNode* thsp() const { return op3p(); }
    AstAttrOf* attrp() const { return VN_AS(op4p(), AttrOf); }
    void fromp(AstNode* nodep) { return setOp1p(nodep); }
    void rhsp(AstNode* nodep) { return setOp2p(nodep); }
    void thsp(AstNode* nodep) { return setOp3p(nodep); }
    void attrp(AstAttrOf* nodep) { return setOp4p(reinterpret_cast<AstNode*>(nodep)); }
    // METHODS
    virtual bool same(const AstNode*) const override { return true; }
};
class AstNodeProcedure VL_NOT_FINAL : public AstNode {
    // IEEE procedure: initial, final, always
protected:
    AstNodeProcedure(VNType t, FileLine* fl, AstNode* bodysp)
        : AstNode{t, fl} {
        addNOp2p(bodysp);
    }

public:
    ASTGEN_MEMBERS_NodeProcedure;
    // METHODS
    virtual void dump(std::ostream& str) const override;
    AstNode* bodysp() const { return op2p(); }  // op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
};
class AstNodeRange VL_NOT_FINAL : public AstNode {
    // A range, sized or unsized
protected:
    AstNodeRange(VNType t, FileLine* fl)
        : AstNode{t, fl} {}

public:
    ASTGEN_MEMBERS_NodeRange;
    virtual void dump(std::ostream& str) const override;
};
class AstNodeStmt VL_NOT_FINAL : public AstNode {
    // Statement -- anything that's directly under a function
    bool m_statement;  // Really a statement (e.g. not a function with return)
protected:
    AstNodeStmt(VNType t, FileLine* fl, bool statement = true)
        : AstNode{t, fl}
        , m_statement{statement} {}

public:
    ASTGEN_MEMBERS_NodeStmt;
    // METHODS
    bool isStatement() const { return m_statement; }  // Really a statement
    void statement(bool flag) { m_statement = flag; }
    virtual void addNextStmt(AstNode* newp,
                             AstNode* belowp) override;  // Stop statement searchback here
    virtual void addBeforeStmt(AstNode* newp,
                               AstNode* belowp) override;  // Stop statement searchback here
    virtual void dump(std::ostream& str = std::cout) const override;
};
class AstNodeAssign VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeAssign(VNType t, FileLine* fl, AstNode* lhsp, AstNode* rhsp,
                  AstNode* timingControlp = nullptr)
        : AstNodeStmt{t, fl} {
        setOp1p(rhsp);
        setOp2p(lhsp);
        addNOp3p(timingControlp);
        dtypeFrom(lhsp);
    }

public:
    ASTGEN_MEMBERS_NodeAssign;
    // Clone single node, just get same type back.
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) = 0;
    // So iteration hits the RHS which is "earlier" in execution order, it's op1, not op2
    AstNode* rhsp() const { return op1p(); }  // op1 = Assign from
    AstNode* lhsp() const { return op2p(); }  // op2 = Assign to
    // op3 = Timing controls (delays, event controls)
    AstNode* timingControlp() const { return op3p(); }
    void addTimingControlp(AstNode* const np) { addNOp3p(np); }
    void rhsp(AstNode* np) { setOp1p(np); }
    void lhsp(AstNode* np) { setOp2p(np); }
    virtual bool hasDType() const override { return true; }
    virtual bool cleanRhs() const { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode*) const override { return true; }
    virtual string verilogKwd() const override { return "="; }
    virtual bool brokeLhsMustBeLvalue() const = 0;
};
class AstNodeCCall VL_NOT_FINAL : public AstNodeStmt {
    // A call of a C++ function, perhaps a AstCFunc or perhaps globally named
    // Functions are not statements, while tasks are. AstNodeStmt needs isStatement() to deal.
    AstCFunc* m_funcp;
    string m_argTypes;

protected:
    AstNodeCCall(VNType t, FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : AstNodeStmt{t, fl, true}
        , m_funcp{funcp} {
        addNOp2p(argsp);
    }

public:
    ASTGEN_MEMBERS_NodeCCall;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual void cloneRelink() override;
    virtual const char* broken() const override;
    virtual int instrCount() const override { return INSTR_COUNT_CALL; }
    virtual bool same(const AstNode* samep) const override {
        const AstNodeCCall* const asamep = static_cast<const AstNodeCCall*>(samep);
        return (funcp() == asamep->funcp() && argTypes() == asamep->argTypes());
    }
    AstNode* exprsp() const { return op2p(); }  // op2 = expressions to print
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override;
    virtual bool isOutputter() const override { return !isPure(); }
    AstCFunc* funcp() const { return m_funcp; }
    void funcp(AstCFunc* funcp) { m_funcp = funcp; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
    // op1p reserved for AstCMethodCall
    AstNode* argsp() const { return op2p(); }
    void addArgsp(AstNode* nodep) { addOp2p(nodep); }
};
class AstNodeCase VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeCase(VNType t, FileLine* fl, AstNode* exprp, AstNode* casesp)
        : AstNodeStmt{t, fl} {
        setOp1p(exprp);
        addNOp2p(casesp);
    }

public:
    ASTGEN_MEMBERS_NodeCase;
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    AstNode* exprp() const { return op1p(); }  // op1 = case condition <expression>
    AstCaseItem* itemsp() const {
        return VN_AS(op2p(), CaseItem);
    }  // op2 = list of case expressions
    AstNode* notParallelp() const { return op3p(); }  // op3 = assertion code for non-full case's
    void addItemsp(AstNode* nodep) { addOp2p(nodep); }
    void addNotParallelp(AstNode* nodep) { setOp3p(nodep); }
};
class AstNodeCoverOrAssert VL_NOT_FINAL : public AstNodeStmt {
    // Cover or Assert
    // Parents:  {statement list}
    // Children: expression, report string
private:
    const bool m_immediate;  // Immediate assertion/cover
    string m_name;  // Name to report
public:
    AstNodeCoverOrAssert(VNType t, FileLine* fl, AstNode* propp, AstNode* passsp, bool immediate,
                         const string& name = "")
        : AstNodeStmt{t, fl}
        , m_immediate{immediate}
        , m_name{name} {
        addOp1p(propp);
        addNOp4p(passsp);
    }
    ASTGEN_MEMBERS_NodeCoverOrAssert;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool same(const AstNode* samep) const override { return samep->name() == name(); }
    virtual void name(const string& name) override { m_name = name; }
    virtual void dump(std::ostream& str = std::cout) const override;
    AstNode* propp() const { return op1p(); }  // op1 = property
    AstSenTree* sentreep() const { return VN_AS(op2p(), SenTree); }  // op2 = clock domain
    void sentreep(AstSenTree* sentreep) { addOp2p((AstNode*)sentreep); }  // op2 = clock domain
    AstNode* passsp() const { return op4p(); }  // op4 = statements (assert/cover passes)
    bool immediate() const { return m_immediate; }
};
class AstNodeFTaskRef VL_NOT_FINAL : public AstNodeStmt {
    // A reference to a task (or function)
    // Functions are not statements, while tasks are. AstNodeStmt needs isStatement() to deal.
private:
    AstNodeFTask* m_taskp = nullptr;  // [AfterLink] Pointer to task referenced
    AstNodeModule* m_classOrPackagep = nullptr;  // Package hierarchy
    string m_name;  // Name of variable
    string m_dotted;  // Dotted part of scope the name()ed task/func is under or ""
    string m_inlinedDots;  // Dotted hierarchy flattened out
    bool m_pli = false;  // Pli system call ($name)
protected:
    AstNodeFTaskRef(VNType t, FileLine* fl, bool statement, AstNode* namep, AstNode* pinsp)
        : AstNodeStmt{t, fl, statement} {
        setOp1p(namep);
        addNOp3p(pinsp);
    }
    AstNodeFTaskRef(VNType t, FileLine* fl, bool statement, const string& name, AstNode* pinsp)
        : AstNodeStmt{t, fl, statement}
        , m_name{name} {
        addNOp3p(pinsp);
    }

public:
    ASTGEN_MEMBERS_NodeFTaskRef;
    virtual const char* broken() const override;
    virtual void cloneRelink() override;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool isGateOptimizable() const override {
        return m_taskp && m_taskp->isGateOptimizable();
    }
    string dotted() const { return m_dotted; }  // * = Scope name or ""
    string inlinedDots() const { return m_inlinedDots; }
    void inlinedDots(const string& flag) { m_inlinedDots = flag; }
    AstNodeFTask* taskp() const { return m_taskp; }  // [After Link] Pointer to variable
    void taskp(AstNodeFTask* taskp) { m_taskp = taskp; }
    virtual void name(const string& name) override { m_name = name; }
    void dotted(const string& name) { m_dotted = name; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackagep = nodep; }
    bool pli() const { return m_pli; }
    void pli(bool flag) { m_pli = flag; }
    // op1 = namep
    AstNode* namep() const { return op1p(); }
    // op2 = reserved for AstMethodCall
    // op3 = Pin interconnection list
    AstNode* pinsp() const { return op3p(); }
    void addPinsp(AstNode* nodep) { addOp3p(nodep); }
    // op4 = scope tracking
    AstScopeName* scopeNamep() const { return VN_AS(op4p(), ScopeName); }
    void scopeNamep(AstNode* nodep) { setNOp4p(nodep); }
};
class AstNodeFor VL_NOT_FINAL : public AstNodeStmt {
protected:
    AstNodeFor(VNType t, FileLine* fl, AstNode* initsp, AstNode* condp, AstNode* incsp,
               AstNode* bodysp)
        : AstNodeStmt{t, fl} {
        addNOp1p(initsp);
        setOp2p(condp);
        addNOp3p(incsp);
        addNOp4p(bodysp);
    }

public:
    ASTGEN_MEMBERS_NodeFor;
    AstNode* initsp() const { return op1p(); }  // op1 = initial statements
    AstNode* condp() const { return op2p(); }  // op2 = condition to continue
    AstNode* incsp() const { return op3p(); }  // op3 = increment statements
    AstNode* bodysp() const { return op4p(); }  // op4 = body of loop
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstNodeIf VL_NOT_FINAL : public AstNodeStmt {
private:
    VBranchPred m_branchPred;  // Branch prediction as taken/untaken?
    bool m_isBoundsCheck;  // True if this if node was inserted for array bounds checking
protected:
    AstNodeIf(VNType t, FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
        : AstNodeStmt{t, fl} {
        setOp1p(condp);
        addNOp2p(ifsp);
        addNOp3p(elsesp);
        isBoundsCheck(false);
    }

public:
    ASTGEN_MEMBERS_NodeIf;
    AstNode* condp() const { return op1p(); }  // op1 = condition
    AstNode* ifsp() const { return op2p(); }  // op2 = list of true statements
    AstNode* elsesp() const { return op3p(); }  // op3 = list of false statements
    void condp(AstNode* newp) { setOp1p(newp); }
    void addIfsp(AstNode* newp) { addOp2p(newp); }
    void addElsesp(AstNode* newp) { addOp3p(newp); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isGateDedupable() const override { return true; }
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    void branchPred(VBranchPred flag) { m_branchPred = flag; }
    VBranchPred branchPred() const { return m_branchPred; }
    void isBoundsCheck(bool flag) { m_isBoundsCheck = flag; }
    bool isBoundsCheck() const { return m_isBoundsCheck; }
    bool isFirstInMyListOfStatements(AstNode* n) const override {
        return n == ifsp() || n == elsesp();
    }
};
class AstNodeReadWriteMem VL_NOT_FINAL : public AstNodeStmt {
private:
    const bool m_isHex;  // readmemh, not readmemb
public:
    AstNodeReadWriteMem(VNType t, FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp,
                        AstNode* lsbp, AstNode* msbp)
        : AstNodeStmt(t, fl)
        , m_isHex(hex) {
        setOp1p(filenamep);
        setOp2p(memp);
        setNOp3p(lsbp);
        setNOp4p(msbp);
    }
    ASTGEN_MEMBERS_NodeReadWriteMem;
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return isHex() == static_cast<const AstNodeReadWriteMem*>(samep)->isHex();
    }
    bool isHex() const { return m_isHex; }
    AstNode* filenamep() const { return op1p(); }
    AstNode* memp() const { return op2p(); }
    AstNode* lsbp() const { return op3p(); }
    AstNode* msbp() const { return op4p(); }
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
    ASTGEN_MEMBERS_NodeText;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual bool same(const AstNode* samep) const override {
        const AstNodeText* asamep = static_cast<const AstNodeText*>(samep);
        return text() == asamep->text();
    }
    const string& text() const { return m_text; }
};
class AstNodeSimpleText VL_NOT_FINAL : public AstNodeText {
private:
    bool m_tracking;  // When emit, it's ok to parse the string to do indentation
public:
    AstNodeSimpleText(VNType t, FileLine* fl, const string& textp, bool tracking = false)
        : AstNodeText(t, fl, textp)
        , m_tracking(tracking) {}
    ASTGEN_MEMBERS_NodeSimpleText;
    void tracking(bool flag) { m_tracking = flag; }
    bool tracking() const { return m_tracking; }
};

// === Concrete node types =====================================================

// === AstNode ===
class AstActive final : public AstNode {
    // Block of code with sensitivity activation
    // Parents:  MODULE | CFUNC
    // Children: SENTREE, statements
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
    ASTGEN_MEMBERS_Active;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }
    const char* broken() const override;
    void cloneRelink() override;
    // Statements are broken into pieces, as some must come before others.
    void sensesp(AstSenTree* nodep) { m_sensesp = nodep; }
    AstSenTree* sensesp() const { return m_sensesp; }
    // op1 = Sensitivity tree, if a clocked block in early stages
    void sensesStorep(AstSenTree* nodep) { addOp1p((AstNode*)nodep); }
    AstSenTree* sensesStorep() const { return VN_AS(op1p(), SenTree); }
    // op2 = Combo logic
    AstNode* stmtsp() const { return op2p(); }
    void addStmtsp(AstNode* nodep) { addOp2p(nodep); }
    // METHODS
    inline bool hasInitial() const;
    inline bool hasSettle() const;
    inline bool hasClocked() const;
};
class AstArg final : public AstNode {
    // An argument to a function/task
private:
    string m_name;  // Pin name, or "" for number based interconnect
public:
    AstArg(FileLine* fl, const string& name, AstNode* exprp)
        : ASTGEN_SUPER_Arg(fl)
        , m_name{name} {
        setNOp1p(exprp);
    }
    ASTGEN_MEMBERS_Arg;
    virtual string name() const override { return m_name; }  // * = Pin name, ""=go by number
    virtual void name(const string& name) override { m_name = name; }
    void exprp(AstNode* nodep) { addOp1p(nodep); }
    // op1 = Expression connected to pin, nullptr if unconnected
    AstNode* exprp() const { return op1p(); }
    bool emptyConnectNoNext() const { return !exprp() && name() == "" && !nextp(); }
};
class AstAttrOf final : public AstNode {
private:
    // Return a value of a attribute, for example a LSB or array LSB of a signal
    VAttrType m_attrType;  // What sort of extraction
public:
    AstAttrOf(FileLine* fl, VAttrType attrtype, AstNode* fromp = nullptr, AstNode* dimp = nullptr)
        : ASTGEN_SUPER_AttrOf(fl) {
        setNOp1p(fromp);
        setNOp2p(dimp);
        m_attrType = attrtype;
    }
    ASTGEN_MEMBERS_AttrOf;
    AstNode* fromp() const { return op1p(); }
    AstNode* dimp() const { return op2p(); }
    VAttrType attrType() const { return m_attrType; }
    virtual void dump(std::ostream& str = std::cout) const override;
};
class AstBind final : public AstNode {
    // Parents: MODULE
    // Children: CELL
private:
    string m_name;  // Binding to name
public:
    AstBind(FileLine* fl, const string& name, AstNode* cellsp)
        : ASTGEN_SUPER_Bind(fl)
        , m_name{name} {
        UASSERT_OBJ(VN_IS(cellsp, Cell), cellsp, "Only instances allowed to be bound");
        addNOp1p(cellsp);
    }
    ASTGEN_MEMBERS_Bind;
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Bind Target name
    virtual void name(const string& name) override { m_name = name; }
    AstNode* cellsp() const { return op1p(); }  // op1 = cells
};
class AstCFunc final : public AstNode {
    // C++ function
    // Parents:  MODULE/SCOPE
    // Children: VAR/statements
private:
    AstScope* m_scopep;
    string m_name;
    string m_cname;  // C name, for dpiExports
    string m_rtnType;  // void, bool, or other return type
    string m_argTypes;  // Argument types
    string m_ctorInits;  // Constructor sub-class inits
    string m_ifdef;  // #ifdef symbol around this function
    VBoolOrUnknown m_isConst;  // Function is declared const (*this not changed)
    bool m_isStatic : 1;  // Function is static (no need for a 'this' pointer)
    bool m_isTrace : 1;  // Function is related to tracing
    bool m_dontCombine : 1;  // V3Combine shouldn't compare this func tree, it's special
    bool m_declPrivate : 1;  // Declare it private
    bool m_isFinal : 1;  // This is a function corresponding to a SystemVerilog 'final' block
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
    bool m_pure : 1;  // Pure function
    bool m_dpiContext : 1;  // Declared as 'context' DPI import/export function
    bool m_dpiExportDispatcher : 1;  // This is the DPI export entry point (i.e.: called by user)
    bool m_dpiExportImpl : 1;  // DPI export implementation (called from DPI dispatcher via lookup)
    bool m_dpiImportPrototype : 1;  // This is the DPI import prototype (i.e.: provided by user)
    bool m_dpiImportWrapper : 1;  // Wrapper for invoking DPI import prototype from generated code
    bool m_dpiTraceInit : 1;  // DPI trace_init
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
        m_isFinal = false;
        m_slow = false;
        m_funcPublic = false;
        m_isConstructor = false;
        m_isDestructor = false;
        m_isMethod = true;
        m_isLoose = false;
        m_isInline = false;
        m_isVirtual = false;
        m_entryPoint = false;
        m_pure = false;
        m_dpiContext = false;
        m_dpiExportDispatcher = false;
        m_dpiExportImpl = false;
        m_dpiImportPrototype = false;
        m_dpiImportWrapper = false;
        m_dpiTraceInit = false;
    }
    ASTGEN_MEMBERS_CFunc;
    virtual string name() const override { return m_name; }
    const char* broken() const override;
    void cloneRelink() override;
    virtual bool maybePointedTo() const override { return true; }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual bool same(const AstNode* samep) const override {
        const AstCFunc* const asamep = static_cast<const AstCFunc*>(samep);
        return ((isTrace() == asamep->isTrace()) && (rtnTypeVoid() == asamep->rtnTypeVoid())
                && (argTypes() == asamep->argTypes()) && (ctorInits() == asamep->ctorInits())
                && isLoose() == asamep->isLoose()
                && (!(dpiImportPrototype() || dpiExportImpl()) || name() == asamep->name()));
    }
    //
    virtual void name(const string& name) override { m_name = name; }
    virtual int instrCount() const override {
        return dpiImportPrototype() ? v3Global.opt.instrCountDpi() : 0;
    }
    VBoolOrUnknown isConst() const { return m_isConst; }
    void isConst(bool flag) { m_isConst.setTrueOrFalse(flag); }
    void isConst(VBoolOrUnknown flag) { m_isConst = flag; }
    bool isStatic() const { return m_isStatic; }
    void isStatic(bool flag) { m_isStatic = flag; }
    bool isTrace() const { return m_isTrace; }
    void isTrace(bool flag) { m_isTrace = flag; }
    void cname(const string& name) { m_cname = name; }
    string cname() const { return m_cname; }
    AstScope* scopep() const { return m_scopep; }
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    string rtnTypeVoid() const { return ((m_rtnType == "") ? "void" : m_rtnType); }
    bool dontCombine() const { return m_dontCombine || isTrace() || entryPoint(); }
    void dontCombine(bool flag) { m_dontCombine = flag; }
    bool dontInline() const { return dontCombine() || slow() || funcPublic(); }
    bool declPrivate() const { return m_declPrivate; }
    void declPrivate(bool flag) { m_declPrivate = flag; }
    bool isFinal() const { return m_isFinal; }
    void isFinal(bool flag) { m_isFinal = flag; }
    bool slow() const { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool funcPublic() const { return m_funcPublic; }
    void funcPublic(bool flag) { m_funcPublic = flag; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
    void ctorInits(const string& str) { m_ctorInits = str; }
    string ctorInits() const { return m_ctorInits; }
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
    bool entryPoint() const { return m_entryPoint; }
    void entryPoint(bool flag) { m_entryPoint = flag; }
    bool pure() const { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
    bool dpiContext() const { return m_dpiContext; }
    void dpiContext(bool flag) { m_dpiContext = flag; }
    bool dpiExportDispatcher() const { return m_dpiExportDispatcher; }
    void dpiExportDispatcher(bool flag) { m_dpiExportDispatcher = flag; }
    bool dpiExportImpl() const { return m_dpiExportImpl; }
    void dpiExportImpl(bool flag) { m_dpiExportImpl = flag; }
    bool dpiImportPrototype() const { return m_dpiImportPrototype; }
    void dpiImportPrototype(bool flag) { m_dpiImportPrototype = flag; }
    bool dpiImportWrapper() const { return m_dpiImportWrapper; }
    void dpiImportWrapper(bool flag) { m_dpiImportWrapper = flag; }
    void dpiTraceInit(bool flag) { m_dpiTraceInit = flag; }
    bool dpiTraceInit() const { return m_dpiTraceInit; }
    //
    // If adding node accessors, see below emptyBody
    AstNode* argsp() const { return op1p(); }
    void addArgsp(AstNode* nodep) { addOp1p(nodep); }
    AstNode* initsp() const { return op2p(); }
    void addInitsp(AstNode* nodep) { addOp2p(nodep); }
    AstNode* stmtsp() const { return op3p(); }
    void addStmtsp(AstNode* nodep) { addOp3p(nodep); }
    AstNode* finalsp() const { return op4p(); }
    void addFinalsp(AstNode* nodep) { addOp4p(nodep); }
    // Special methods
    bool emptyBody() const {
        return argsp() == nullptr && initsp() == nullptr && stmtsp() == nullptr
               && finalsp() == nullptr;
    }
};
class AstCUse final : public AstNode {
    // C++ use of a class or #include; indicates need of forward declaration
    // Parents:  NODEMODULE
private:
    const VUseType m_useType;  // What sort of use this is
    const string m_name;

public:
    AstCUse(FileLine* fl, VUseType useType, const string& name)
        : ASTGEN_SUPER_CUse(fl)
        , m_useType{useType}
        , m_name{name} {}
    ASTGEN_MEMBERS_CUse;
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }
    VUseType useType() const { return m_useType; }
};
class AstCaseItem final : public AstNode {
    // Single item of a case statement
    // Parents:  CASE
    // condsp Children: MATH  (Null condition used for default block)
    // bodysp Children: Statements
public:
    AstCaseItem(FileLine* fl, AstNode* condsp, AstNode* bodysp)
        : ASTGEN_SUPER_CaseItem(fl) {
        addNOp1p(condsp);
        addNOp2p(bodysp);
    }
    ASTGEN_MEMBERS_CaseItem;
    virtual int instrCount() const override { return widthInstrs() + INSTR_COUNT_BRANCH; }
    AstNode* condsp() const { return op1p(); }  // op1 = list of possible matching expressions
    AstNode* bodysp() const { return op2p(); }  // op2 = what to do
    void condsp(AstNode* nodep) { setOp1p(nodep); }
    void addBodysp(AstNode* newp) { addOp2p(newp); }
    bool isDefault() const { return condsp() == nullptr; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstCast final : public AstNode {
    // Cast to appropriate data type - note lhsp is value, to match AstTypedef, AstCCast, etc
public:
    AstCast(FileLine* fl, AstNode* lhsp, VFlagChildDType, AstNodeDType* dtp)
        : ASTGEN_SUPER_Cast(fl) {
        setOp1p(lhsp);
        setOp2p(dtp);
        dtypeFrom(dtp);
    }
    AstCast(FileLine* fl, AstNode* lhsp, AstNodeDType* dtp)
        : ASTGEN_SUPER_Cast(fl) {
        setOp1p(lhsp);
        dtypeFrom(dtp);
    }
    ASTGEN_MEMBERS_Cast;
    virtual bool hasDType() const override { return true; }
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* fromp() const { return lhsp(); }
    void lhsp(AstNode* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    AstNodeDType* childDTypep() const { return VN_AS(op2p(), NodeDType); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
};
class AstCastParse final : public AstNode {
    // Cast to appropriate type, where we haven't determined yet what the data type is
public:
    AstCastParse(FileLine* fl, AstNode* lhsp, AstNode* dtp)
        : ASTGEN_SUPER_CastParse(fl) {
        setOp1p(lhsp);
        setOp2p(dtp);
    }
    ASTGEN_MEMBERS_CastParse;
    virtual string emitVerilog() { return "((%d)'(%l))"; }
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* dtp() const { return op2p(); }
};
class AstCastSize final : public AstNode {
    // Cast to specific size; signed/twostate inherited from lower element per IEEE
public:
    AstCastSize(FileLine* fl, AstNode* lhsp, AstConst* rhsp)
        : ASTGEN_SUPER_CastSize(fl) {
        setOp1p(lhsp);
        setOp2p((AstNode*)rhsp);
    }
    ASTGEN_MEMBERS_CastSize;
    // No hasDType because widthing removes this node before the hasDType check
    virtual string emitVerilog() { return "((%r)'(%l))"; }
    virtual bool cleanOut() const { V3ERROR_NA_RETURN(true); }
    virtual bool cleanLhs() const { return true; }
    virtual bool sizeMattersLhs() const { return false; }
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
};
class AstCell final : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
private:
    FileLine* m_modNameFileline;  // Where module the cell instances token was
    string m_name;  // Cell name
    string m_origName;  // Original name before dot addition
    string m_modName;  // Module the cell instances
    AstNodeModule* m_modp = nullptr;  // [AfterLink] Pointer to module instanced
    bool m_hasIfaceVar : 1;  // True if a Var has been created for this cell
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
        , m_recursive{false}
        , m_trace{true} {
        addNOp1p((AstNode*)pinsp);
        addNOp2p((AstNode*)paramsp);
        setNOp3p((AstNode*)rangep);
    }
    ASTGEN_MEMBERS_Cell;
    // No cloneRelink, we presume cloneee's want the same module linkages
    virtual void dump(std::ostream& str) const override;
    const char* broken() const override;
    virtual bool maybePointedTo() const override { return true; }
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Cell name
    virtual void name(const string& name) override { m_name = name; }
    virtual string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    string modName() const { return m_modName; }  // * = Instance name
    void modName(const string& name) { m_modName = name; }
    FileLine* modNameFileline() const { return m_modNameFileline; }
    AstPin* pinsp() const { return VN_AS(op1p(), Pin); }  // op1 = List of cell ports
    // op2 = List of parameter #(##) values
    AstPin* paramsp() const { return VN_AS(op2p(), Pin); }
    // op3 = Range of arrayed instants (nullptr=not ranged)
    AstRange* rangep() const { return VN_AS(op3p(), Range); }
    // op4 = List of interface references
    AstIntfRef* intfRefp() const { return VN_AS(op4p(), IntfRef); }
    AstNodeModule* modp() const { return m_modp; }  // [AfterLink] = Pointer to module instantiated
    void addPinsp(AstPin* nodep) { addOp1p((AstNode*)nodep); }
    void addParamsp(AstPin* nodep) { addOp2p((AstNode*)nodep); }
    void addIntfRefp(AstIntfRef* nodep) { addOp4p((AstNode*)nodep); }
    void modp(AstNodeModule* nodep) { m_modp = nodep; }
    bool hasIfaceVar() const { return m_hasIfaceVar; }
    void hasIfaceVar(bool flag) { m_hasIfaceVar = flag; }
    void trace(bool flag) { m_trace = flag; }
    bool isTrace() const { return m_trace; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
};
class AstCellArrayRef final : public AstNode {
    // As-of-yet unlinkable reference into an array of cells
private:
    string m_name;  // Array name
public:
    AstCellArrayRef(FileLine* fl, const string& name, AstNode* selectExprp)
        : ASTGEN_SUPER_CellArrayRef(fl)
        , m_name{name} {
        addNOp1p(selectExprp);
    }
    ASTGEN_MEMBERS_CellArrayRef;
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Array name
    AstNode* selp() const { return op1p(); }  // op1 = Select expression
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
    ASTGEN_MEMBERS_CellInline;
    virtual void dump(std::ostream& str) const override;
    const char* broken() const override;
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Cell name
    string origModName() const { return m_origModName; }  // * = modp()->origName() before inlining
    virtual void name(const string& name) override { m_name = name; }
    void scopep(AstScope* scp) { m_scopep = scp; }
    AstScope* scopep() const { return m_scopep; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstCellRef final : public AstNode {
    // As-of-yet unlinkable reference into a cell
private:
    string m_name;  // Cell name
public:
    AstCellRef(FileLine* fl, const string& name, AstNode* cellp, AstNode* exprp)
        : ASTGEN_SUPER_CellRef(fl)
        , m_name{name} {
        addNOp1p(cellp);
        addNOp2p(exprp);
    }
    ASTGEN_MEMBERS_CellRef;
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Array name
    AstNode* cellp() const { return op1p(); }  // op1 = Cell
    AstNode* exprp() const { return op2p(); }  // op2 = Expression
};
class AstClassExtends final : public AstNode {
    // Children: List of AstParseRef for packages/classes
    // during early parse, then moves to dtype
public:
    AstClassExtends(FileLine* fl, AstNode* classOrPkgsp)
        : ASTGEN_SUPER_ClassExtends(fl) {
        setNOp2p(classOrPkgsp);  // Only for parser
    }
    ASTGEN_MEMBERS_ClassExtends;
    virtual bool hasDType() const override { return true; }
    virtual string verilogKwd() const override { return "extends"; }
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    AstNode* classOrPkgsp() const { return op2p(); }
    AstClass* classp() const;  // Class being extended (after link)
};
class AstClassOrPackageRef final : public AstNode {
private:
    string m_name;
    // Node not NodeModule to appease some early parser usage
    AstNode* m_classOrPackageNodep;  // Package hierarchy
public:
    AstClassOrPackageRef(FileLine* fl, const string& name, AstNode* classOrPackageNodep,
                         AstNode* paramsp)
        : ASTGEN_SUPER_ClassOrPackageRef(fl)
        , m_name{name}
        , m_classOrPackageNodep{classOrPackageNodep} {
        addNOp4p(paramsp);
    }
    ASTGEN_MEMBERS_ClassOrPackageRef;
    // METHODS
    virtual const char* broken() const override {
        BROKEN_RTN(m_classOrPackageNodep && !m_classOrPackageNodep->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_classOrPackageNodep && m_classOrPackageNodep->clonep()) {
            m_classOrPackageNodep = m_classOrPackageNodep->clonep();
        }
    }
    virtual bool same(const AstNode* samep) const override {
        return (m_classOrPackageNodep
                == static_cast<const AstClassOrPackageRef*>(samep)->m_classOrPackageNodep);
    }
    virtual void dump(std::ostream& str = std::cout) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    AstNode* classOrPackageNodep() const { return m_classOrPackageNodep; }
    void classOrPackageNodep(AstNode* nodep) { m_classOrPackageNodep = nodep; }
    AstNodeModule* classOrPackagep() const;
    AstPackage* packagep() const { return VN_CAST(classOrPackageNodep(), Package); }
    void classOrPackagep(AstNodeModule* nodep) { m_classOrPackageNodep = (AstNode*)nodep; }
    AstPin* paramsp() const { return VN_AS(op4p(), Pin); }
};
class AstClocking final : public AstNode {
    // Set default clock region
    // Parents:  MODULE
    // Children: Assertions
public:
    AstClocking(FileLine* fl, AstSenItem* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_Clocking(fl) {
        addOp1p((AstNode*)sensesp);
        addNOp2p(bodysp);
    }
    ASTGEN_MEMBERS_Clocking;
    // op1 = Sensitivity list
    AstSenItem* sensesp() const { return VN_AS(op1p(), SenItem); }
    AstNode* bodysp() const { return op2p(); }  // op2 = Body
};
class AstConstPool final : public AstNode {
    // Container for const static data
    std::unordered_multimap<uint32_t, AstVarScope*> m_tables;  // Constant tables (unpacked arrays)
    std::unordered_multimap<uint32_t, AstVarScope*> m_consts;  // Constant tables (scalars)
    AstModule* const m_modp;  // The Module holding the Scope below ...
    AstScope* const m_scopep;  // Scope holding the constant variables

    AstVarScope* createNewEntry(const string& name, AstNode* initp);

public:
    explicit AstConstPool(FileLine* fl);
    ASTGEN_MEMBERS_ConstPool;
    virtual bool maybePointedTo() const override { return true; }
    const char* broken() const override;
    virtual void cloneRelink() override { V3ERROR_NA; }
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
    // Children: math
private:
    string m_name;  // Name of variable getting set
    string m_path;  // Dotted cellname to set parameter of
public:
    AstDefParam(FileLine* fl, const string& path, const string& name, AstNode* rhsp)
        : ASTGEN_SUPER_DefParam(fl)
        , m_name{name}
        , m_path{path} {
        setOp1p(rhsp);
    }
    virtual string name() const override { return m_name; }  // * = Scope name
    ASTGEN_MEMBERS_DefParam;
    virtual bool same(const AstNode*) const override { return true; }
    AstNode* rhsp() const { return op1p(); }  // op1 = Assign from
    string path() const { return m_path; }
};
class AstDot final : public AstNode {
    // A dot separating paths in an AstVarXRef, AstFuncRef or AstTaskRef
    // These are eliminated in the link stage
    const bool m_colon;  // Is a "::" instead of a "." (lhs must be package/class)
public:
    AstDot(FileLine* fl, bool colon, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_Dot(fl)
        , m_colon{colon} {
        setOp1p(lhsp);
        setOp2p(rhsp);
    }
    ASTGEN_MEMBERS_Dot;
    // For parser, make only if non-null package
    static AstNode* newIfPkg(FileLine* fl, AstNode* packageOrClassp, AstNode* rhsp) {
        if (!packageOrClassp) return rhsp;
        return new AstDot(fl, true, packageOrClassp, rhsp);
    }
    virtual void dump(std::ostream& str) const override;
    AstNode* lhsp() const { return op1p(); }
    void rhsp(AstNode* nodep) { setOp2p(nodep); }
    AstNode* rhsp() const { return op2p(); }
    bool colon() const { return m_colon; }
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
    ASTGEN_MEMBERS_DpiExport;
    virtual string name() const override { return m_name; }
    virtual void name(const string& name) override { m_name = name; }
    string cname() const { return m_cname; }
    void cname(const string& cname) { m_cname = cname; }
};
class AstElabDisplay final : public AstNode {
    // Parents: stmtlist
    // Children: SFORMATF to generate print string
private:
    VDisplayType m_displayType;

public:
    inline AstElabDisplay(FileLine* fl, VDisplayType dispType, AstNode* exprsp);
    ASTGEN_MEMBERS_ElabDisplay;
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override {
        return (string("$") + string(displayType().ascii()));
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstElabDisplay*>(samep)->displayType();
    }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    VDisplayType displayType() const { return m_displayType; }
    void displayType(VDisplayType type) { m_displayType = type; }
    void fmtp(AstSFormatF* nodep) { addOp1p((AstNode*)nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_AS(op1p(), SFormatF); }
};
class AstEmpty final : public AstNode {
    // Represents something missing, e.g. a missing argument in FOREACH
public:
    explicit AstEmpty(FileLine* fl)
        : ASTGEN_SUPER_Empty(fl) {}
    ASTGEN_MEMBERS_Empty;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstExecGraph final : public AstNode {
    // For parallel execution, this node contains a dependency graph.  Each
    // vertex in the graph is an ExecMTask, which contains a body for the
    // mtask (an AstMTaskBody), which contains sequentially executed statements.
    //
    // The AstMTaskBody nodes are also children of this node, so we can visit
    // them without traversing the graph.
private:
    V3Graph* const m_depGraphp;  // contains ExecMTask vertices
    const string m_name;  // Name of this AstExecGraph (for uniqueness at code generation)

public:
    explicit AstExecGraph(FileLine* fl, const string& name);
    ASTGEN_MEMBERS_ExecGraph;
    ~AstExecGraph() override;
    virtual const char* broken() const override {
        BROKEN_RTN(!m_depGraphp);
        return nullptr;
    }
    virtual string name() const override { return m_name; }
    V3Graph* depGraphp() { return m_depGraphp; }
    const V3Graph* depGraphp() const { return m_depGraphp; }
    // op1: The mtask bodies
    AstMTaskBody* mTaskBodiesp() const { return VN_AS(op1p(), MTaskBody); }
    void addMTaskBodyp(AstMTaskBody* bodyp) { addOp1p((AstNode*)bodyp); }
    // op2: In later phases, the statements that start the parallel execution
    void addStmtsp(AstNode* stmtp) { addOp2p(stmtp); }
};
class AstImplicit final : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
public:
    AstImplicit(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_Implicit(fl) {
        addNOp1p(exprsp);
    }
    ASTGEN_MEMBERS_Implicit;
    AstNode* exprsp() const { return op1p(); }  // op1 = Assign from
};
class AstInitArray final : public AstNode {
    // Set a var to a map of values
    // The list of initsp() is not relevant
    // If default is specified, the vector may be sparse, and not provide each value.
    // Key values are C++ array style, with lo() at index 0
    // Parents: ASTVAR::init()
    // Children: AstInitItem
public:
    using KeyItemMap = std::map<uint64_t, AstInitItem*>;

private:
    KeyItemMap m_map;  // Node value for each array index
public:
    AstInitArray(FileLine* fl, AstNodeDType* newDTypep, AstNode* defaultp)
        : ASTGEN_SUPER_InitArray(fl) {
        dtypep(newDTypep);
        addNOp1p(defaultp);
    }
    ASTGEN_MEMBERS_InitArray;
    virtual void dump(std::ostream& str) const override;
    const char* broken() const override;
    void cloneRelink() override;
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        // Only works if exact same children, instead should override comparison
        // of children list, and instead use map-vs-map key/value compare
        return m_map == static_cast<const AstInitArray*>(samep)->m_map;
    }
    AstNode* defaultp() const { return op1p(); }  // op1 = Default if sparse
    void defaultp(AstNode* newp) { setOp1p(newp); }
    AstNode* initsp() const { return op2p(); }  // op2 = Initial value expressions
    void addValuep(AstNode* newp) { addIndexValuep(m_map.size(), newp); }
    const KeyItemMap& map() const { return m_map; }
    AstNode* addIndexValuep(uint64_t index, AstNode* newp);
    AstNode* getIndexValuep(uint64_t index) const;
    AstNode* getIndexDefaultedValuep(uint64_t index) const;
};
class AstInitItem final : public AstNode {
    // Container for a item in an init array
    // This container is present so that the value underneath may get replaced with a new nodep
    // and the upper AstInitArray's map will remain correct (pointing to this InitItem)
public:
    // Parents: INITARRAY
    AstInitItem(FileLine* fl, AstNode* valuep)
        : ASTGEN_SUPER_InitItem(fl) {
        addOp1p(valuep);
    }
    ASTGEN_MEMBERS_InitItem;
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return false; }  // See valuep()'s dtype instead
    AstNode* valuep() const { return op1p(); }  // op1 = Value
    void valuep(AstNode* nodep) { addOp1p(nodep); }
};
class AstIntfRef final : public AstNode {
    // An interface reference
private:
    string m_name;  // Name of the reference
public:
    AstIntfRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER_IntfRef(fl)
        , m_name{name} {}
    virtual string name() const override { return m_name; }
    ASTGEN_MEMBERS_IntfRef;
};
class AstMTaskBody final : public AstNode {
    // Hold statements for each MTask
private:
    ExecMTask* m_execMTaskp = nullptr;

public:
    explicit AstMTaskBody(FileLine* fl)
        : ASTGEN_SUPER_MTaskBody(fl) {}
    ASTGEN_MEMBERS_MTaskBody;
    virtual const char* broken() const override {
        BROKEN_RTN(!m_execMTaskp);
        return nullptr;
    }
    AstNode* stmtsp() const { return op1p(); }
    void addStmtsp(AstNode* nodep) { addOp1p(nodep); }
    void addStmtsFirstp(AstNode* nodep) {
        if (stmtsp()) {
            stmtsp()->addHereThisAsNext(nodep);
        } else {
            addStmtsp(nodep);
        }
    }
    ExecMTask* execMTaskp() const { return m_execMTaskp; }
    void execMTaskp(ExecMTask* execMTaskp) { m_execMTaskp = execMTaskp; }
    virtual void dump(std::ostream& str = std::cout) const override;
};
class AstModport final : public AstNode {
    // A modport in an interface
private:
    string m_name;  // Name of the modport
public:
    AstModport(FileLine* fl, const string& name, AstNode* varsp)
        : ASTGEN_SUPER_Modport(fl)
        , m_name{name} {
        addNOp1p(varsp);
    }
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    ASTGEN_MEMBERS_Modport;
    AstNode* varsp() const { return op1p(); }  // op1 = List of Vars
};
class AstModportFTaskRef final : public AstNode {
    // An import/export referenced under a modport
    // The storage for the function itself is inside the
    // interface/instantiator, thus this is a reference
    // PARENT: AstModport
private:
    string m_name;  // Name of the variable referenced
    bool m_export;  // Type of the function (import/export)
    AstNodeFTask* m_ftaskp = nullptr;  // Link to the function
public:
    AstModportFTaskRef(FileLine* fl, const string& name, bool isExport)
        : ASTGEN_SUPER_ModportFTaskRef(fl)
        , m_name{name}
        , m_export{isExport} {}
    ASTGEN_MEMBERS_ModportFTaskRef;
    const char* broken() const override;
    void cloneRelink() override;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
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
    VDirection m_direction;  // Direction of the variable (in/out)
    AstVar* m_varp = nullptr;  // Link to the actual Var
public:
    AstModportVarRef(FileLine* fl, const string& name, VDirection::en direction)
        : ASTGEN_SUPER_ModportVarRef(fl)
        , m_name{name}
        , m_direction{direction} {}
    ASTGEN_MEMBERS_ModportVarRef;
    const char* broken() const override;
    void cloneRelink() override;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    void direction(const VDirection& flag) { m_direction = flag; }
    VDirection direction() const { return m_direction; }
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp = varp; }
};
class AstNetlist final : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
private:
    AstTypeTable* const m_typeTablep;  // Reference to top type table, for faster lookup
    AstConstPool* const m_constPoolp;  // Reference to constant pool, for faster lookup
    AstPackage* m_dollarUnitPkgp = nullptr;  // $unit
    AstCFunc* m_evalp = nullptr;  // The '_eval' function
    AstVarScope* m_dpiExportTriggerp = nullptr;  // The DPI export trigger variable
    AstTopScope* m_topScopep = nullptr;  // The singleton AstTopScope under the top module
    VTimescale m_timeunit;  // Global time unit
    VTimescale m_timeprecision;  // Global time precision
    bool m_changeRequest = false;  // Have _change_request method
    bool m_timescaleSpecified = false;  // Input HDL specified timescale
    uint32_t m_nextFreeMTaskID = 1;  // Next unique MTask ID within netlist
                                     // starts at 1 so 0 means no MTask ID
    uint32_t m_nextFreeMTaskProfilingID = 0;  // Next unique ID to use for PGO
public:
    AstNetlist();
    ASTGEN_MEMBERS_Netlist;
    const char* broken() const override;
    virtual void cloneRelink() override { V3ERROR_NA; }
    virtual string name() const override { return "$root"; }
    virtual void dump(std::ostream& str) const override;
    AstNodeModule* modulesp() const {  // op1 = List of modules
        return VN_AS(op1p(), NodeModule);
    }
    AstNodeModule* topModulep() const {  // Top module in hierarchy
        return modulesp();  // First one in the list, for now
    }
    void addModulep(AstNodeModule* modulep) { addOp1p((AstNode*)modulep); }
    AstNodeFile* filesp() const { return VN_AS(op2p(), NodeFile); }  // op2 = List of files
    void addFilesp(AstNodeFile* filep) { addOp2p((AstNode*)filep); }
    void addMiscsp(AstNode* nodep) { addOp3p(nodep); }
    AstTypeTable* typeTablep() { return m_typeTablep; }
    void changeRequest(bool specified) { m_changeRequest = specified; }
    bool changeRequest() const { return m_changeRequest; }
    AstConstPool* constPoolp() { return m_constPoolp; }
    AstPackage* dollarUnitPkgp() const { return m_dollarUnitPkgp; }
    AstPackage* dollarUnitPkgAddp();
    AstCFunc* evalp() const { return m_evalp; }
    void evalp(AstCFunc* evalp) { m_evalp = evalp; }
    AstVarScope* dpiExportTriggerp() const { return m_dpiExportTriggerp; }
    void dpiExportTriggerp(AstVarScope* varScopep) { m_dpiExportTriggerp = varScopep; }
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
    ASTGEN_MEMBERS_PackageExport;
    const char* broken() const override;
    void cloneRelink() override;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};
class AstPackageExportStarStar final : public AstNode {
    // A package export *::* declaration
public:
    // cppcheck-suppress noExplicitConstructor
    AstPackageExportStarStar(FileLine* fl)
        : ASTGEN_SUPER_PackageExportStarStar(fl) {}
    ASTGEN_MEMBERS_PackageExportStarStar;
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
    ASTGEN_MEMBERS_PackageImport;
    const char* broken() const override;
    void cloneRelink() override;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }
};
class AstParseRef final : public AstNode {
    // A reference to a variable, function or task
    // We don't know which at parse time due to bison constraints
    // The link stages will replace this with AstVarRef, or AstTaskRef, etc.
    // Parents: math|stmt
    // Children: TEXT|DOT|SEL*|TASK|FUNC (or expression under sel)
private:
    VParseRefExp m_expect;  // Type we think it should resolve to
    string m_name;

public:
    AstParseRef(FileLine* fl, VParseRefExp expect, const string& name, AstNode* lhsp = nullptr,
                AstNodeFTaskRef* ftaskrefp = nullptr)
        : ASTGEN_SUPER_ParseRef(fl)
        , m_expect{expect}
        , m_name{name} {
        setNOp1p(lhsp);
        setNOp2p((AstNode*)ftaskrefp);
    }
    ASTGEN_MEMBERS_ParseRef;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool same(const AstNode* samep) const override {
        const AstParseRef* const asamep = static_cast<const AstParseRef*>(samep);
        return (expect() == asamep->expect() && m_name == asamep->m_name);
    }
    virtual void name(const string& name) override { m_name = name; }
    VParseRefExp expect() const { return m_expect; }
    void expect(VParseRefExp exp) { m_expect = exp; }
    // op1 = Components
    AstNode* lhsp() const { return op1p(); }  // op1 = List of statements
    AstNode* ftaskrefp() const { return op2p(); }  // op2 = Function/task reference
    // op2 = Function/task reference
    void ftaskrefp(AstNodeFTaskRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstPin final : public AstNode {
    // A pin on a cell
private:
    int m_pinNum;  // Pin number
    string m_name;  // Pin name, or "" for number based interconnect
    AstVar* m_modVarp = nullptr;  // Input/output this pin connects to on submodule.
    AstParamTypeDType* m_modPTypep = nullptr;  // Param type this pin connects to on submodule.
    bool m_param = false;  // Pin connects to parameter
    bool m_svImplicit = false;  // Pin is SystemVerilog .name'ed
public:
    AstPin(FileLine* fl, int pinNum, const string& name, AstNode* exprp)
        : ASTGEN_SUPER_Pin(fl)
        , m_pinNum{pinNum}
        , m_name{name} {
        setNOp1p(exprp);
    }
    inline AstPin(FileLine* fl, int pinNum, AstVarRef* varname, AstNode* exprp);
    ASTGEN_MEMBERS_Pin;
    virtual void dump(std::ostream& str) const override;
    const char* broken() const override;
    virtual string name() const override { return m_name; }  // * = Pin name, ""=go by number
    virtual void name(const string& name) override { m_name = name; }
    string prettyOperatorName() const override;
    bool dotStar() const { return name() == ".*"; }  // Fake name for .* connections until linked
    int pinNum() const { return m_pinNum; }
    void exprp(AstNode* nodep) { addOp1p(nodep); }
    // op1 = Expression connected to pin, nullptr if unconnected
    AstNode* exprp() const { return op1p(); }
    AstVar* modVarp() const { return m_modVarp; }  // [After Link] Pointer to variable
    void modVarp(AstVar* nodep) { m_modVarp = nodep; }
    // [After Link] Pointer to variable
    AstParamTypeDType* modPTypep() const { return m_modPTypep; }
    void modPTypep(AstParamTypeDType* nodep) { m_modPTypep = nodep; }
    bool param() const { return m_param; }
    void param(bool flag) { m_param = flag; }
    bool svImplicit() const { return m_svImplicit; }
    void svImplicit(bool flag) { m_svImplicit = flag; }
};
class AstPort final : public AstNode {
    // A port (in/out/inout) on a module
private:
    int m_pinNum;  // Pin number
    string m_name;  // Name of pin
public:
    AstPort(FileLine* fl, int pinnum, const string& name)
        : ASTGEN_SUPER_Port(fl)
        , m_pinNum{pinnum}
        , m_name{name} {}
    ASTGEN_MEMBERS_Port;
    virtual string name() const override { return m_name; }  // * = Port name
    int pinNum() const { return m_pinNum; }  // * = Pin number, for order based instantiation
    AstNode* exprp() const { return op1p(); }  // op1 = Expression connected to port
};
class AstPragma final : public AstNode {
private:
    const VPragmaType m_pragType;  // Type of pragma
public:
    // Pragmas don't result in any output code, they're just flags that affect
    // other processing in verilator.
    AstPragma(FileLine* fl, VPragmaType pragType)
        : ASTGEN_SUPER_Pragma(fl)
        , m_pragType{pragType} {}
    ASTGEN_MEMBERS_Pragma;
    VPragmaType pragType() const { return m_pragType; }  // *=type of the pragma
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* samep) const override {
        return pragType() == static_cast<const AstPragma*>(samep)->pragType();
    }
};
class AstPropClocked final : public AstNode {
    // A clocked property
    // Parents:  ASSERT|COVER (property)
    // Children: SENITEM, Properties
public:
    AstPropClocked(FileLine* fl, AstSenItem* sensesp, AstNode* disablep, AstNode* propp)
        : ASTGEN_SUPER_PropClocked(fl) {
        addNOp1p((AstNode*)sensesp);
        addNOp2p(disablep);
        addOp3p(propp);
    }
    ASTGEN_MEMBERS_PropClocked;
    virtual bool hasDType() const override {
        return true;
    }  // Used under Cover, which expects a bool child
    AstSenItem* sensesp() const { return VN_AS(op1p(), SenItem); }  // op1 = Sensitivity list
    AstNode* disablep() const { return op2p(); }  // op2 = disable
    AstNode* propp() const { return op3p(); }  // op3 = property
};
class AstPull final : public AstNode {
private:
    bool m_direction;

public:
    AstPull(FileLine* fl, AstNode* lhsp, bool direction)
        : ASTGEN_SUPER_Pull(fl)
        , m_direction{direction} {
        setOp1p(lhsp);
    }
    ASTGEN_MEMBERS_Pull;
    virtual bool same(const AstNode* samep) const override {
        return direction() == static_cast<const AstPull*>(samep)->direction();
    }
    void lhsp(AstNode* np) { setOp1p(np); }
    AstNode* lhsp() const { return op1p(); }  // op1 = Assign to
    uint32_t direction() const { return (uint32_t)m_direction; }
};
class AstSFormatF final : public AstNode {
    // Convert format to string, generally under an AstDisplay or AstSFormat
    // Also used as "real" function for /*verilator sformat*/ functions
    string m_text;
    const bool m_hidden;  // Under display, etc
    bool m_hasFormat;  // Has format code
    const char m_missingArgChar;  // Format code when argument without format, 'h'/'o'/'b'
    VTimescale m_timeunit;  // Parent module time unit
public:
    class NoFormat {};
    AstSFormatF(FileLine* fl, const string& text, bool hidden, AstNode* exprsp,
                char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormatF(fl)
        , m_text{text}
        , m_hidden{hidden}
        , m_hasFormat{true}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addNOp1p(exprsp);
        addNOp2p(nullptr);
    }
    AstSFormatF(FileLine* fl, NoFormat, AstNode* exprsp, char missingArgChar = 'd',
                bool hidden = true)
        : ASTGEN_SUPER_SFormatF(fl)
        , m_text{""}
        , m_hidden{hidden}
        , m_hasFormat{false}
        , m_missingArgChar{missingArgChar} {
        dtypeSetString();
        addNOp1p(exprsp);
        addNOp2p(nullptr);
    }
    ASTGEN_MEMBERS_SFormatF;
    virtual string name() const override { return m_text; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return text() == static_cast<const AstSFormatF*>(samep)->text();
    }
    virtual string verilogKwd() const override { return "$sformatf"; }
    void addExprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    string text() const { return m_text; }  // * = Text to display
    void text(const string& text) { m_text = text; }
    AstScopeName* scopeNamep() const { return VN_AS(op2p(), ScopeName); }
    void scopeNamep(AstNode* nodep) { setNOp2p(nodep); }
    bool formatScopeTracking() const {  // Track scopeNamep();  Ok if false positive
        return (name().find("%m") != string::npos || name().find("%M") != string::npos);
    }
    bool hidden() const { return m_hidden; }
    void hasFormat(bool flag) { m_hasFormat = flag; }
    bool hasFormat() const { return m_hasFormat; }
    char missingArgChar() const { return m_missingArgChar; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstScope final : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
private:
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
    ASTGEN_MEMBERS_Scope;
    virtual void cloneRelink() override;
    virtual const char* broken() const override;
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return m_name; }  // * = Scope name
    virtual void name(const string& name) override { m_name = name; }
    virtual void dump(std::ostream& str) const override;
    string nameDotless() const;
    string nameVlSym() const { return ((string("vlSymsp->")) + nameDotless()); }
    AstNodeModule* modp() const { return m_modp; }
    void addVarp(AstVarScope* nodep) { addOp1p((AstNode*)nodep); }
    AstVarScope* varsp() const { return VN_AS(op1p(), VarScope); }  // op1 = AstVarScope's
    void addActivep(AstNode* nodep) { addOp2p(nodep); }
    AstNode* blocksp() const { return op2p(); }  // op2 = Block names
    void addFinalClkp(AstNode* nodep) { addOp3p(nodep); }
    AstNode* finalClksp() const { return op3p(); }  // op3 = Final assigns for clock correction
    AstScope* aboveScopep() const { return m_aboveScopep; }
    AstCell* aboveCellp() const { return m_aboveCellp; }
    bool isTop() const { return aboveScopep() == nullptr; }  // At top of hierarchy
};
class AstSelLoopVars final : public AstNode {
    // Parser only concept "[id, id, id]" for a foreach statement
    // Unlike normal selects elements is a list
public:
    AstSelLoopVars(FileLine* fl, AstNode* fromp, AstNode* elementsp)
        : ASTGEN_SUPER_SelLoopVars(fl) {
        setOp1p(fromp);
        addNOp2p(elementsp);
    }
    ASTGEN_MEMBERS_SelLoopVars;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual bool maybePointedTo() const override { return false; }
    AstNode* fromp() const { return op1p(); }
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* elementsp() const { return op2p(); }
};
class AstSenItem final : public AstNode {
    // Parents:  SENTREE
    // Children: (optional) VARREF
private:
    VEdgeType m_edgeType;  // Edge type
public:
    class Combo {};  // for creator type-overload selection
    class Illegal {};  // for creator type-overload selection
    class Initial {};  // for creator type-overload selection
    class Settle {};  // for creator type-overload selection
    class Never {};  // for creator type-overload selection
    AstSenItem(FileLine* fl, VEdgeType edgeType, AstNode* varrefp)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{edgeType} {
        setOp1p(varrefp);
    }
    AstSenItem(FileLine* fl, Combo)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_COMBO} {}
    AstSenItem(FileLine* fl, Illegal)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_ILLEGAL} {}
    AstSenItem(FileLine* fl, Initial)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_INITIAL} {}
    AstSenItem(FileLine* fl, Settle)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_SETTLE} {}
    AstSenItem(FileLine* fl, Never)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_NEVER} {}
    ASTGEN_MEMBERS_SenItem;
    virtual void dump(std::ostream& str) const override;
    virtual bool same(const AstNode* samep) const override {
        return edgeType() == static_cast<const AstSenItem*>(samep)->edgeType();
    }
    VEdgeType edgeType() const { return m_edgeType; }  // * = Posedge/negedge
    void edgeType(VEdgeType type) {
        m_edgeType = type;
        editCountInc();
    }  // * = Posedge/negedge
    AstNode* sensp() const { return op1p(); }  // op1 = Signal sensitized
    AstNodeVarRef* varrefp() const {
        return VN_CAST(op1p(), NodeVarRef);
    }  // op1 = Signal sensitized
    //
    bool isClocked() const { return edgeType().clockedStmt(); }
    bool isCombo() const { return edgeType() == VEdgeType::ET_COMBO; }
    bool isInitial() const { return edgeType() == VEdgeType::ET_INITIAL; }
    bool isIllegal() const { return edgeType() == VEdgeType::ET_ILLEGAL; }
    bool isSettle() const { return edgeType() == VEdgeType::ET_SETTLE; }
    bool isNever() const { return edgeType() == VEdgeType::ET_NEVER; }
    bool hasVar() const { return !(isCombo() || isInitial() || isSettle() || isNever()); }
};
class AstSenTree final : public AstNode {
    // A list of senitems
    // Parents:  MODULE | SBLOCK
    // Children: SENITEM list
private:
    bool m_multi = false;  // Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstSenItem* sensesp)
        : ASTGEN_SUPER_SenTree(fl) {
        addNOp1p(sensesp);
    }
    ASTGEN_MEMBERS_SenTree;
    virtual void dump(std::ostream& str) const override;
    virtual bool maybePointedTo() const override { return true; }
    bool isMulti() const { return m_multi; }
    // op1 = Sensitivity list
    AstSenItem* sensesp() const { return VN_AS(op1p(), SenItem); }
    void addSensesp(AstSenItem* nodep) { addOp1p(nodep); }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    bool hasClocked() const;  // Includes a clocked statement
    bool hasSettle() const;  // Includes a SETTLE SenItem
    bool hasInitial() const;  // Includes a INITIAL SenItem
    bool hasCombo() const;  // Includes a COMBO SenItem
};
class AstSplitPlaceholder final : public AstNode {
public:
    // Dummy node used within V3Split; never exists outside of V3Split.
    explicit AstSplitPlaceholder(FileLine* fl)
        : ASTGEN_SUPER_SplitPlaceholder(fl) {}
    ASTGEN_MEMBERS_SplitPlaceholder;
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

    ASTGEN_MEMBERS_StrengthSpec;
    VStrength strength0() { return m_s0; }
    VStrength strength1() { return m_s1; }
    virtual void dump(std::ostream& str) const override;
};
class AstTopScope final : public AstNode {
    // A singleton, held under the top level AstModule. Holds the top level AstScope,
    // and after V3ActiveTop, the global list of AstSenTrees (list of unique sensitivity lists).
    // Parent: Top level AstModule
    // Children: AstSenTree, AstScope
    friend class AstNetlist;  // Only the AstNetlist can create one
    AstTopScope(FileLine* fl, AstScope* ascopep)
        : ASTGEN_SUPER_TopScope(fl) {
        addOp2p(ascopep);
    }

public:
    ASTGEN_MEMBERS_TopScope;
    virtual bool maybePointedTo() const override { return true; }
    AstSenTree* senTreesp() const { return VN_AS(op1p(), SenTree); }
    void addSenTreep(AstSenTree* nodep) { addOp1p((AstNode*)nodep); }
    AstScope* scopep() const { return VN_AS(op2p(), Scope); }
};
class AstTypeTable final : public AstNode {
    // Container for hash of standard data types
    // Children:  NODEDTYPEs
    AstEmptyQueueDType* m_emptyQueuep = nullptr;
    AstQueueDType* m_queueIndexp = nullptr;
    AstVoidDType* m_voidp = nullptr;
    AstBasicDType* m_basicps[VBasicDTypeKwd::_ENUM_MAX]{};
    //
    using DetailedMap = std::map<VBasicTypeKey, AstBasicDType*>;
    DetailedMap m_detailedMap;

public:
    explicit AstTypeTable(FileLine* fl);
    ASTGEN_MEMBERS_TypeTable;
    virtual bool maybePointedTo() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(m_emptyQueuep && !m_emptyQueuep->brokeExists());
        BROKEN_RTN(m_queueIndexp && !m_queueIndexp->brokeExists());
        BROKEN_RTN(m_voidp && !m_voidp->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override { V3ERROR_NA; }
    AstNodeDType* typesp() const { return VN_AS(op1p(), NodeDType); }  // op1 = List of dtypes
    void addTypesp(AstNodeDType* nodep) { addOp1p(nodep); }
    AstBasicDType* findBasicDType(FileLine* fl, VBasicDTypeKwd kwd);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, int width, int widthMin,
                                     VSigning numeric);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, const VNumRange& range,
                                     int widthMin, VSigning numeric);
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);
    AstEmptyQueueDType* findEmptyQueueDType(FileLine* fl);
    AstQueueDType* findQueueIndexDType(FileLine* fl);
    AstVoidDType* findVoidDType(FileLine* fl);
    void clearCache();
    void repairCache();
    virtual void dump(std::ostream& str = std::cout) const override;
};
class AstTypedef final : public AstNode {
private:
    string m_name;
    bool m_attrPublic = false;
    string m_tag;  // Holds the string of the verilator tag -- used in XML output.
public:
    AstTypedef(FileLine* fl, const string& name, AstNode* attrsp, VFlagChildDType,
               AstNodeDType* dtp)
        : ASTGEN_SUPER_Typedef(fl)
        , m_name{name} {
        childDTypep(dtp);  // Only for parser
        addAttrsp(attrsp);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_Typedef;
    virtual void dump(std::ostream& str) const override;
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Type assigning to
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode* attrsp() const { return op4p(); }  // op4 = Attributes during early parse
    // METHODS
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& flag) override { m_name = flag; }
    bool attrPublic() const { return m_attrPublic; }
    void attrPublic(bool flag) { m_attrPublic = flag; }
    virtual void tag(const string& text) override { m_tag = text; }
    virtual string tag() const override { return m_tag; }
};
class AstTypedefFwd final : public AstNode {
    // Forward declaration of a type; stripped after netlist parsing is complete
private:
    string m_name;

public:
    AstTypedefFwd(FileLine* fl, const string& name)
        : ASTGEN_SUPER_TypedefFwd(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_TypedefFwd;
    // METHODS
    virtual string name() const override { return m_name; }
    virtual bool maybePointedTo() const override { return true; }
};
class AstUdpTable final : public AstNode {
public:
    AstUdpTable(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_UdpTable(fl) {
        addNOp1p(bodysp);
    }
    ASTGEN_MEMBERS_UdpTable;
    // op1 = List of UdpTableLines
    AstUdpTableLine* bodysp() const { return VN_AS(op1p(), UdpTableLine); }
};
class AstUdpTableLine final : public AstNode {
    string m_text;

public:
    AstUdpTableLine(FileLine* fl, const string& text)
        : ASTGEN_SUPER_UdpTableLine(fl)
        , m_text{text} {}
    ASTGEN_MEMBERS_UdpTableLine;
    virtual string name() const override { return m_text; }
    string text() const { return m_text; }
};
class AstUnlinkedRef final : public AstNode {
    // As-of-yet unlinkable Ref
private:
    string m_name;  // Var name
public:
    AstUnlinkedRef(FileLine* fl, AstNode* refp, const string& name, AstNode* crp)
        : ASTGEN_SUPER_UnlinkedRef(fl)
        , m_name{name} {
        addNOp1p(refp);
        addNOp2p(crp);
    }
    ASTGEN_MEMBERS_UnlinkedRef;
    // ACCESSORS
    virtual string name() const override { return m_name; }  // * = Var name
    AstNode* refp() const { return op1p(); }  // op1 = VarXRef or AstNodeFTaskRef
    AstNode* cellrefp() const { return op2p(); }  // op2 = CellArrayRef or CellRef
};
class AstVar final : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
private:
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
    bool m_ansi : 1;  // ANSI port list variable (for dedup check)
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
    bool m_funcLocal : 1;  // Local variable for a function
    bool m_funcReturn : 1;  // Return variable for a function
    bool m_attrClockEn : 1;  // User clock enable attribute
    bool m_attrScBv : 1;  // User force bit vector attribute
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_attrSFormat : 1;  // User sformat attribute
    bool m_attrSplitVar : 1;  // declared with split_var metacomment
    bool m_fileDescr : 1;  // File descriptor
    bool m_isRand : 1;  // Random variable
    bool m_isConst : 1;  // Table contains constant data
    bool m_isContinuously : 1;  // Ever assigned continuously (for force/release)
    bool m_hasStrengthAssignment : 1;  // Is on LHS of assignment with strength specifier
    bool m_isStatic : 1;  // Static C variable (for Verilog see instead isAutomatic)
    bool m_isPulldown : 1;  // Tri0
    bool m_isPullup : 1;  // Tri1
    bool m_isIfaceParent : 1;  // dtype is reference to interface present in this module
    bool m_isDpiOpenArray : 1;  // DPI import open array
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_noReset : 1;  // Do not do automated reset/randomization
    bool m_noSubst : 1;  // Do not substitute out references
    bool m_overridenParam : 1;  // Overridden parameter by #(...) or defparam
    bool m_trace : 1;  // Trace this variable
    bool m_isLatched : 1;  // Not assigned in all control paths of combo always
    bool m_isForceable : 1;  // May be forced/released externally from user C code

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
        m_sigPublic = false;
        m_sigModPublic = false;
        m_sigUserRdPublic = false;
        m_sigUserRWPublic = false;
        m_funcLocal = false;
        m_funcReturn = false;
        m_attrClockEn = false;
        m_attrScBv = false;
        m_attrIsolateAssign = false;
        m_attrSFormat = false;
        m_attrSplitVar = false;
        m_fileDescr = false;
        m_isRand = false;
        m_isConst = false;
        m_isContinuously = false;
        m_hasStrengthAssignment = false;
        m_isStatic = false;
        m_isPulldown = false;
        m_isPullup = false;
        m_isIfaceParent = false;
        m_isDpiOpenArray = false;
        m_isHideLocal = false;
        m_isHideProtected = false;
        m_noReset = false;
        m_noSubst = false;
        m_overridenParam = false;
        m_trace = false;
        m_isLatched = false;
        m_isForceable = false;
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
    ASTGEN_MEMBERS_Var;
    virtual void dump(std::ostream& str) const override;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool hasDType() const override { return true; }
    virtual bool maybePointedTo() const override { return true; }
    virtual string origName() const override { return m_origName; }  // * = Original name
    void origName(const string& name) { m_origName = name; }
    VVarType varType() const { return m_varType; }  // * = Type of variable
    void direction(const VDirection& flag) {
        m_direction = flag;
        if (m_direction == VDirection::INOUT) m_tristate = true;
    }
    VDirection direction() const { return m_direction; }
    bool isIO() const { return m_direction != VDirection::NONE; }
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
    virtual AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    // op1 = Range of variable
    AstNodeDType* childDTypep() const { return VN_AS(op1p(), NodeDType); }
    // op2 = Net delay
    AstNode* delayp() const { return op2p(); }
    void delayp(AstNode* const nodep) { setNOp2p(nodep); }
    AstNodeDType* dtypeSkipRefp() const { return subDTypep()->skipRefp(); }
    // (Slow) recurse down to find basic data type (Note don't need virtual -
    // AstVar isn't a NodeDType)
    AstBasicDType* basicp() const { return subDTypep()->basicp(); }
    // op3 = Initial value that never changes (static const), or constructor argument for
    // MTASKSTATE variables
    AstNode* valuep() const { return op3p(); }
    // It's valuep(), not constp(), as may be more complicated than an AstConst
    void valuep(AstNode* nodep) { setOp3p(nodep); }
    void addAttrsp(AstNode* nodep) { addNOp4p(nodep); }
    AstNode* attrsp() const { return op4p(); }  // op4 = Attributes during early parse
    void childDTypep(AstNodeDType* nodep) { setOp1p(nodep); }
    virtual AstNodeDType* subDTypep() const { return dtypep() ? dtypep() : childDTypep(); }
    void ansi(bool flag) { m_ansi = flag; }
    void declTyped(bool flag) { m_declTyped = flag; }
    void attrClockEn(bool flag) { m_attrClockEn = flag; }
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
    void isConst(bool flag) { m_isConst = flag; }
    void isContinuously(bool flag) { m_isContinuously = flag; }
    void isStatic(bool flag) { m_isStatic = flag; }
    void isIfaceParent(bool flag) { m_isIfaceParent = flag; }
    void funcLocal(bool flag) { m_funcLocal = flag; }
    void funcReturn(bool flag) { m_funcReturn = flag; }
    void hasStrengthAssignment(bool flag) { m_hasStrengthAssignment = flag; }
    bool hasStrengthAssignment() { return m_hasStrengthAssignment; }
    void isDpiOpenArray(bool flag) { m_isDpiOpenArray = flag; }
    bool isDpiOpenArray() const { return m_isDpiOpenArray; }
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
    // METHODS
    virtual void name(const string& name) override { m_name = name; }
    virtual void tag(const string& text) override { m_tag = text; }
    virtual string tag() const override { return m_tag; }
    bool isAnsi() const { return m_ansi; }
    bool isContinuously() const { return m_isContinuously; }
    bool isDeclTyped() const { return m_declTyped; }
    bool isInoutish() const { return m_direction.isInoutish(); }
    bool isNonOutput() const { return m_direction.isNonOutput(); }
    bool isReadOnly() const { return m_direction.isReadOnly(); }
    bool isWritable() const { return m_direction.isWritable(); }
    bool isTristate() const { return m_tristate; }
    bool isPrimaryIO() const { return m_primaryIO; }
    bool isPrimaryInish() const { return isPrimaryIO() && isNonOutput(); }
    bool isIfaceRef() const { return (varType() == VVarType::IFACEREF); }
    bool isIfaceParent() const { return m_isIfaceParent; }
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
    bool isParam() const {
        return (varType() == VVarType::LPARAM || varType() == VVarType::GPARAM);
    }
    bool isGParam() const { return (varType() == VVarType::GPARAM); }
    bool isGenVar() const { return (varType() == VVarType::GENVAR); }
    bool isBitLogic() const {
        AstBasicDType* bdtypep = basicp();
        return bdtypep && bdtypep->isBitLogic();
    }
    bool isUsedClock() const { return m_usedClock; }
    bool isUsedParam() const { return m_usedParam; }
    bool isUsedLoopIdx() const { return m_usedLoopIdx; }
    bool isSc() const { return m_sc; }
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
    bool isConst() const { return m_isConst; }
    bool isStatic() const { return m_isStatic; }
    bool isLatched() const { return m_isLatched; }
    bool isFuncLocal() const { return m_funcLocal; }
    bool isFuncReturn() const { return m_funcReturn; }
    bool isPullup() const { return m_isPullup; }
    bool isPulldown() const { return m_isPulldown; }
    bool attrClockEn() const { return m_attrClockEn; }
    bool attrScBv() const { return m_attrScBv; }
    bool attrFileDescr() const { return m_fileDescr; }
    bool attrScClocked() const { return m_scClocked; }
    bool attrSFormat() const { return m_attrSFormat; }
    bool attrSplitVar() const { return m_attrSplitVar; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    VVarAttrClocker attrClocker() const { return m_attrClocker; }
    virtual string verilogKwd() const override;
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void propagateAttrFrom(AstVar* fromp) {
        // This is getting connected to fromp; keep attributes
        // Note the method below too
        if (fromp->attrClockEn()) attrClockEn(true);
        if (fromp->attrFileDescr()) attrFileDescr(true);
        if (fromp->attrIsolateAssign()) attrIsolateAssign(true);
        if (fromp->isContinuously()) isContinuously(true);
    }
    bool gateMultiInputOptimizable() const {
        // Ok to gate optimize; must return false if propagateAttrFrom would do anything
        return (!attrClockEn() && !isUsedClock());
    }
    void combineType(AstVar* typevarp) {
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
    bool m_circular : 1;  // Used in circular ordering dependency, need change detect
    bool m_trace : 1;  // Tracing is turned on for this scope
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
        : ASTGEN_SUPER_VarScope(fl)
        , m_scopep{scopep}
        , m_varp{varp} {
        UASSERT_OBJ(scopep, fl, "Scope must be non-null");
        UASSERT_OBJ(varp, fl, "Var must be non-null");
        m_circular = false;
        m_trace = true;
        dtypeFrom(varp);
    }
    ASTGEN_MEMBERS_VarScope;
    virtual void cloneRelink() override {
        if (m_varp && m_varp->clonep()) {
            m_varp = m_varp->clonep();
            UASSERT(m_scopep->clonep(), "No clone cross link: " << this);
            m_scopep = m_scopep->clonep();
        }
    }
    virtual const char* broken() const override {
        BROKEN_RTN(m_varp && !m_varp->brokeExists());
        BROKEN_RTN(m_scopep && !m_scopep->brokeExists());
        return nullptr;
    }
    virtual bool maybePointedTo() const override { return true; }
    virtual string name() const override { return scopep()->name() + "->" + varp()->name(); }
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    AstVar* varp() const { return m_varp; }  // [After Link] Pointer to variable
    AstScope* scopep() const { return m_scopep; }  // Pointer to scope it's under
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    bool isCircular() const { return m_circular; }
    void circular(bool flag) { m_circular = flag; }
    bool isTrace() const { return m_trace; }
    void trace(bool flag) { m_trace = flag; }
};

// === AstNodeBlock ===
class AstBegin final : public AstNodeBlock {
    // A Begin/end named block, only exists shortly after parsing until linking
    // Parents: statement
    // Children: statements
private:
    bool m_generate;  // Underneath a generate
    const bool m_implied;  // Not inserted by user
public:
    // Node that puts name into the output stream
    AstBegin(FileLine* fl, const string& name, AstNode* stmtsp, bool generate = false,
             bool implied = false)
        : ASTGEN_SUPER_Begin(fl, name, stmtsp)
        , m_generate{generate}
        , m_implied{implied} {}
    ASTGEN_MEMBERS_Begin;
    virtual void dump(std::ostream& str) const override;
    // op1p is statements in NodeBlock
    AstNode* genforp() const { return op2p(); }  // op2 = GENFOR, if applicable,
    // might NOT be a GenFor, as loop unrolling replaces with Begin
    void addGenforp(AstGenFor* nodep) { addOp2p((AstNode*)nodep); }
    void generate(bool flag) { m_generate = flag; }
    bool generate() const { return m_generate; }
    bool implied() const { return m_implied; }
};
class AstFork final : public AstNodeBlock {
    // A fork named block
    // Parents: statement
    // Children: statements
private:
    VJoinType m_joinType;  // Join keyword type
public:
    // Node that puts name into the output stream
    AstFork(FileLine* fl, const string& name, AstNode* stmtsp)
        : ASTGEN_SUPER_Fork(fl, name, stmtsp) {}
    ASTGEN_MEMBERS_Fork;
    virtual void dump(std::ostream& str) const override;
    VJoinType joinType() const { return m_joinType; }
    void joinType(const VJoinType& flag) { m_joinType = flag; }
};

// === AstNodeFTask ===
class AstFunc final : public AstNodeFTask {
    // A function inside a module
public:
    AstFunc(FileLine* fl, const string& name, AstNode* stmtp, AstNode* fvarsp)
        : ASTGEN_SUPER_Func(fl, name, stmtp) {
        addNOp1p(fvarsp);
    }
    ASTGEN_MEMBERS_Func;
    virtual bool hasDType() const override { return true; }
};
class AstTask final : public AstNodeFTask {
    // A task inside a module
public:
    AstTask(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER_Task(fl, name, stmtp) {}
    ASTGEN_MEMBERS_Task;
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
    ASTGEN_MEMBERS_CFile;
    virtual void dump(std::ostream& str = std::cout) const override;
    bool slow() const { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool source() const { return m_source; }
    void source(bool flag) { m_source = flag; }
    bool support() const { return m_support; }
    void support(bool flag) { m_support = flag; }
};
class AstVFile final : public AstNodeFile {
    // Verilog output file
    // Parents:  NETLIST
public:
    AstVFile(FileLine* fl, const string& name)
        : ASTGEN_SUPER_VFile(fl, name) {}
    ASTGEN_MEMBERS_VFile;
    virtual void dump(std::ostream& str = std::cout) const override;
};

// === AstNodeModule ===
class AstClass final : public AstNodeModule {
    // TYPES
    using MemberNameMap = std::map<const std::string, AstNode*>;
    // MEMBERS
    MemberNameMap m_members;  // Members or method children
    AstClassPackage* m_classOrPackagep = nullptr;  // Class package this is under
    bool m_virtual = false;  // Virtual class
    bool m_extended = false;  // Is extension or extended by other classes
    void insertCache(AstNode* nodep);

public:
    AstClass(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Class(fl, name) {}
    ASTGEN_MEMBERS_Class;
    virtual string verilogKwd() const override { return "class"; }
    virtual bool maybePointedTo() const override { return true; }
    virtual void dump(std::ostream& str) const override;
    const char* broken() const override;
    void cloneRelink() override;
    virtual bool timescaleMatters() const override { return false; }
    // op1/op2/op3 in AstNodeModule
    AstClassPackage* classOrPackagep() const { return m_classOrPackagep; }
    void classOrPackagep(AstClassPackage* classpackagep) { m_classOrPackagep = classpackagep; }
    AstNode* membersp() const { return stmtsp(); }  // op2 = List of statements
    void addMembersp(AstNode* nodep) {
        insertCache(nodep);
        addStmtp(nodep);
    }
    AstClassExtends* extendsp() const { return VN_AS(op4p(), ClassExtends); }
    void extendsp(AstNode* nodep) { addNOp4p(nodep); }
    void clearCache() { m_members.clear(); }
    void repairCache();
    AstNode* findMember(const string& name) const {
        const auto it = m_members.find(name);
        return (it == m_members.end()) ? nullptr : it->second;
    }
    bool isExtended() const { return m_extended; }
    void isExtended(bool flag) { m_extended = flag; }
    bool isVirtual() const { return m_virtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    // Return true if this class is an extension of base class (SLOW)
    // Accepts nullptrs
    static bool isClassExtendedFrom(const AstClass* refClassp, const AstClass* baseClassp);
};
class AstClassPackage final : public AstNodeModule {
    // The static information portion of a class (treated similarly to a package)
    AstClass* m_classp
        = nullptr;  // Class package this is under (weak pointer, hard link is other way)
public:
    AstClassPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER_ClassPackage(fl, name) {}
    ASTGEN_MEMBERS_ClassPackage;
    virtual string verilogKwd() const override { return "classpackage"; }
    virtual const char* broken() const override;
    virtual void cloneRelink() override;
    virtual bool timescaleMatters() const override { return false; }
    AstClass* classp() const { return m_classp; }
    void classp(AstClass* classp) { m_classp = classp; }
};
class AstIface final : public AstNodeModule {
    // A module declaration
public:
    AstIface(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Iface(fl, name) {}
    ASTGEN_MEMBERS_Iface;
    // Interfaces have `timescale applicability but lots of code seems to
    // get false warnings if we enable this
    virtual string verilogKwd() const override { return "interface"; }
    virtual bool timescaleMatters() const override { return false; }
};
class AstModule final : public AstNodeModule {
    // A module declaration
private:
    const bool m_isProgram;  // Module represents a program
public:
    AstModule(FileLine* fl, const string& name, bool program = false)
        : ASTGEN_SUPER_Module(fl, name)
        , m_isProgram{program} {}
    ASTGEN_MEMBERS_Module;
    virtual string verilogKwd() const override { return m_isProgram ? "program" : "module"; }
    virtual bool timescaleMatters() const override { return true; }
};
class AstNotFoundModule final : public AstNodeModule {
    // A missing module declaration
public:
    AstNotFoundModule(FileLine* fl, const string& name)
        : ASTGEN_SUPER_NotFoundModule(fl, name) {}
    ASTGEN_MEMBERS_NotFoundModule;
    virtual string verilogKwd() const override { return "/*not-found-*/ module"; }
    virtual bool timescaleMatters() const override { return false; }
};
class AstPackage final : public AstNodeModule {
    // A package declaration
public:
    AstPackage(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Package(fl, name) {}
    ASTGEN_MEMBERS_Package;
    virtual string verilogKwd() const override { return "package"; }
    virtual bool timescaleMatters() const override { return !isDollarUnit(); }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};
class AstPrimitive final : public AstNodeModule {
    // A primitive declaration
public:
    AstPrimitive(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Primitive(fl, name) {}
    ASTGEN_MEMBERS_Primitive;
    virtual string verilogKwd() const override { return "primitive"; }
    virtual bool timescaleMatters() const override { return false; }
};

// === AstNodePreSel ===
class AstSelBit final : public AstNodePreSel {
    // Single bit range extraction, perhaps with non-constant selection or array selection
    // Gets replaced during link with AstArraySel or AstSel
public:
    AstSelBit(FileLine* fl, AstNode* fromp, AstNode* bitp)
        : ASTGEN_SUPER_SelBit(fl, fromp, bitp, nullptr) {
        UASSERT_OBJ(!v3Global.assertDTypesResolved(), this,
                    "not coded to create after dtypes resolved");
    }
    ASTGEN_MEMBERS_SelBit;
    AstNode* bitp() const { return rhsp(); }
};
class AstSelExtract final : public AstNodePreSel {
    // Range extraction, gets replaced with AstSel
public:
    AstSelExtract(FileLine* fl, AstNode* fromp, AstNode* msbp, AstNode* lsbp)
        : ASTGEN_SUPER_SelExtract(fl, fromp, msbp, lsbp) {}
    ASTGEN_MEMBERS_SelExtract;
    AstNode* leftp() const { return rhsp(); }
    AstNode* rightp() const { return thsp(); }
};
class AstSelMinus final : public AstNodePreSel {
    // -: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelMinus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
        : ASTGEN_SUPER_SelMinus(fl, fromp, bitp, widthp) {}
    ASTGEN_MEMBERS_SelMinus;
    AstNode* bitp() const { return rhsp(); }
    AstNode* widthp() const { return thsp(); }
};
class AstSelPlus final : public AstNodePreSel {
    // +: range extraction, perhaps with non-constant selection
    // Gets replaced during link with AstSel
public:
    AstSelPlus(FileLine* fl, AstNode* fromp, AstNode* bitp, AstNode* widthp)
        : ASTGEN_SUPER_SelPlus(fl, fromp, bitp, widthp) {}
    ASTGEN_MEMBERS_SelPlus;
    AstNode* bitp() const { return rhsp(); }
    AstNode* widthp() const { return thsp(); }
};

// === AstNodeProcedure ===
class AstAlways final : public AstNodeProcedure {
    const VAlwaysKwd m_keyword;

public:
    AstAlways(FileLine* fl, VAlwaysKwd keyword, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_Always(fl, bodysp)
        , m_keyword{keyword} {
        addNOp1p(sensesp);
    }
    ASTGEN_MEMBERS_Always;
    //
    virtual void dump(std::ostream& str) const override;
    AstSenTree* sensesp() const { return VN_AS(op1p(), SenTree); }  // op1 = Sensitivity list
    void sensesp(AstSenTree* nodep) { setOp1p(nodep); }
    VAlwaysKwd keyword() const { return m_keyword; }
};
class AstAlwaysPost final : public AstNodeProcedure {
    // Like always but post assignments for memory assignment IFs
public:
    AstAlwaysPost(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysPost(fl, bodysp) {
        addNOp1p(sensesp);
    }
    ASTGEN_MEMBERS_AlwaysPost;
};
class AstAlwaysPostponed final : public AstNodeProcedure {
    // Like always but postponement scheduling region

public:
    AstAlwaysPostponed(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysPostponed(fl, bodysp) {}
    ASTGEN_MEMBERS_AlwaysPostponed;
};
class AstFinal final : public AstNodeProcedure {
public:
    AstFinal(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_Final(fl, bodysp) {}
    ASTGEN_MEMBERS_Final;
};
class AstInitial final : public AstNodeProcedure {
public:
    AstInitial(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_Initial(fl, bodysp) {}
    ASTGEN_MEMBERS_Initial;
};
class AstInitialAutomatic final : public AstNodeProcedure {
    // Automatic variable initialization
    // That is, it runs every function start, or class construction
public:
    AstInitialAutomatic(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_InitialAutomatic(fl, bodysp) {}
    ASTGEN_MEMBERS_InitialAutomatic;
};
class AstInitialStatic final : public AstNodeProcedure {
    // Static variable initialization
    // That is, it runs at the beginning of simulation, before 'initial' blocks
public:
    AstInitialStatic(FileLine* fl, AstNode* bodysp)
        : ASTGEN_SUPER_InitialStatic(fl, bodysp) {}
    ASTGEN_MEMBERS_InitialStatic;
};

// === AstNodeRange ===
class AstBracketRange final : public AstNodeRange {
    // Parser only concept "[lhsp]", a AstUnknownRange, QueueRange or Range,
    // unknown until lhsp type is determined
public:
    AstBracketRange(FileLine* fl, AstNode* elementsp)
        : ASTGEN_SUPER_BracketRange(fl) {
        setOp1p(elementsp);
    }
    ASTGEN_MEMBERS_BracketRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { V3ERROR_NA_RETURN(""); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    virtual bool maybePointedTo() const override { return false; }
    AstNode* elementsp() const { return op1p(); }
};
class AstRange final : public AstNodeRange {
    // Range specification, for use under variables and cells
public:
    AstRange(FileLine* fl, AstNode* leftp, AstNode* rightp)
        : ASTGEN_SUPER_Range(fl) {
        setOp2p(leftp);
        setOp3p(rightp);
    }
    inline AstRange(FileLine* fl, int left, int right);
    inline AstRange(FileLine* fl, const VNumRange& range);
    ASTGEN_MEMBERS_Range;
    AstNode* leftp() const { return op2p(); }
    AstNode* rightp() const { return op3p(); }
    inline int leftConst() const;
    inline int rightConst() const;
    int hiConst() const {
        const int l = leftConst();
        const int r = rightConst();
        return l > r ? l : r;
    }
    int loConst() const {
        const int l = leftConst();
        const int r = rightConst();
        return l > r ? r : l;
    }
    int elementsConst() const { return hiConst() - loConst() + 1; }
    bool littleEndian() const { return leftConst() < rightConst(); }
    virtual void dump(std::ostream& str) const override;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstUnsizedRange final : public AstNodeRange {
    // Unsized range specification, for open arrays
public:
    explicit AstUnsizedRange(FileLine* fl)
        : ASTGEN_SUPER_UnsizedRange(fl) {}
    ASTGEN_MEMBERS_UnsizedRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[]"; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstWildcardRange final : public AstNodeRange {
    // Wildcard range specification, for wildcard index type associative arrays
public:
    explicit AstWildcardRange(FileLine* fl)
        : ASTGEN_SUPER_WildcardRange(fl) {}
    ASTGEN_MEMBERS_WildcardRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[*]"; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};

// === AstNodeStmt ===
class AstAlwaysPublic final : public AstNodeStmt {
    // "Fake" sensitivity created by /*verilator public_flat_rw @(edgelist)*/
    // Body statements are just AstVarRefs to the public signals
public:
    AstAlwaysPublic(FileLine* fl, AstSenTree* sensesp, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysPublic(fl) {
        addNOp1p(sensesp);
        addNOp2p(bodysp);
    }
    ASTGEN_MEMBERS_AlwaysPublic;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    //
    AstSenTree* sensesp() const { return VN_AS(op1p(), SenTree); }  // op1 = Sensitivity list
    AstNode* bodysp() const { return op2p(); }  // op2 = Statements to evaluate
    void addStmtp(AstNode* nodep) { addOp2p(nodep); }
    // Special accessors
    bool isJustOneBodyStmt() const { return bodysp() && !bodysp()->nextp(); }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstBreak final : public AstNodeStmt {
public:
    explicit AstBreak(FileLine* fl)
        : ASTGEN_SUPER_Break(fl) {}
    ASTGEN_MEMBERS_Break;
    virtual string verilogKwd() const override { return "break"; }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstCMethodHard final : public AstNodeStmt {
    // A reference to a "C" hardcoded member task (or function)
    // PARENTS: stmt/math
    // Not all calls are statments vs math.  AstNodeStmt needs isStatement() to deal.
private:
    string m_name;  // Name of method
    bool m_pure = false;  // Pure optimizable
public:
    AstCMethodHard(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name,
                   AstNode* pinsp = nullptr)
        : ASTGEN_SUPER_CMethodHard(fl, false)
        , m_name{name} {
        setOp1p(fromp);
        dtypep(nullptr);  // V3Width will resolve
        addNOp2p(pinsp);
    }
    AstCMethodHard(FileLine* fl, AstNode* fromp, const string& name, AstNode* pinsp = nullptr)
        : ASTGEN_SUPER_CMethodHard(fl, false)
        , m_name{name} {
        setOp1p(fromp);
        addNOp2p(pinsp);
    }
    ASTGEN_MEMBERS_CMethodHard;
    virtual string name() const override { return m_name; }  // * = Var name
    virtual bool hasDType() const override { return true; }
    virtual void name(const string& name) override { m_name = name; }
    virtual bool same(const AstNode* samep) const override {
        const AstCMethodHard* asamep = static_cast<const AstCMethodHard*>(samep);
        return (m_name == asamep->m_name);
    }
    virtual bool isPure() const override { return m_pure; }
    void pure(bool flag) { m_pure = flag; }
    void makeStatement() {
        statement(true);
        dtypeSetVoid();
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
    AstNode* pinsp() const { return op2p(); }  // op2 = Pin interconnection list
    void addPinsp(AstNode* nodep) { addOp2p(nodep); }
};
class AstCReset final : public AstNodeStmt {
    // Reset variable at startup
public:
    AstCReset(FileLine* fl, AstVarRef* exprsp)
        : ASTGEN_SUPER_CReset(fl) {
        addNOp1p((AstNode*)exprsp);
    }
    ASTGEN_MEMBERS_CReset;
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstVarRef* varrefp() const { return VN_AS(op1p(), VarRef); }  // op1 = varref to reset
};
class AstCReturn final : public AstNodeStmt {
    // C++ return from a function
    // Parents:  CFUNC/statement
    // Children: Math
public:
    AstCReturn(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_CReturn(fl) {
        setOp1p(lhsp);
    }
    ASTGEN_MEMBERS_CReturn;
    virtual int instrCount() const override { return widthInstrs(); }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    //
    AstNode* lhsp() const { return op1p(); }
};
class AstCStmt final : public AstNodeStmt {
    // Emit C statement
public:
    AstCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_CStmt(fl) {
        addNOp1p(exprsp);
    }
    inline AstCStmt(FileLine* fl, const string& textStmt);
    ASTGEN_MEMBERS_CStmt;
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    void addBodysp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
};
class AstChangeDet final : public AstNodeStmt {
    // A comparison to determine change detection, common & must be fast.
public:
    // Null lhs+rhs used to indicate change needed with no spec vars
    AstChangeDet(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_ChangeDet(fl) {
        setNOp1p(lhsp);
        setNOp2p(rhsp);
    }
    ASTGEN_MEMBERS_ChangeDet;
    AstNode* lhsp() const { return op1p(); }
    AstNode* rhsp() const { return op2p(); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual int instrCount() const override { return widthInstrs() * 2; }  // xor, or/logor
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstComment final : public AstNodeStmt {
    // Some comment to put into the output stream
    // Parents:  {statement list}
    // Children: none
private:
    const bool m_showAt;  // Show "at <fileline>"
    const string m_name;  // Text of comment
public:
    AstComment(FileLine* fl, const string& name, bool showAt = false)
        : ASTGEN_SUPER_Comment(fl)
        , m_showAt{showAt}
        , m_name{name} {}
    ASTGEN_MEMBERS_Comment;
    virtual string name() const override { return m_name; }  // * = Text
    virtual bool same(const AstNode* samep) const override {
        return true;
    }  // Ignore name in comments
    virtual bool showAt() const { return m_showAt; }
};
class AstContinue final : public AstNodeStmt {
public:
    explicit AstContinue(FileLine* fl)
        : ASTGEN_SUPER_Continue(fl) {}
    ASTGEN_MEMBERS_Continue;
    virtual string verilogKwd() const override { return "continue"; }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstCoverDecl final : public AstNodeStmt {
    // Coverage analysis point declaration
    // Parents:  {statement list}
    // Children: none
private:
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
    ASTGEN_MEMBERS_CoverDecl;
    virtual const char* broken() const override {
        BROKEN_RTN(m_dataDeclp && !m_dataDeclp->brokeExists());
        if (m_dataDeclp && m_dataDeclp->m_dataDeclp) {  // Avoid O(n^2) accessing
            v3fatalSrc("dataDeclp should point to real data, not be a list");
        }
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_dataDeclp && m_dataDeclp->clonep()) m_dataDeclp = m_dataDeclp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    virtual bool maybePointedTo() const override { return true; }
    void binNum(int flag) { m_binNum = flag; }
    int binNum() const { return m_binNum; }
    int offset() const { return m_offset; }
    const string& comment() const { return m_text; }  // text to insert in code
    const string& linescov() const { return m_linescov; }
    const string& page() const { return m_page; }
    const string& hier() const { return m_hier; }
    void hier(const string& flag) { m_hier = flag; }
    void comment(const string& flag) { m_text = flag; }
    virtual bool same(const AstNode* samep) const override {
        const AstCoverDecl* const asamep = static_cast<const AstCoverDecl*>(samep);
        return (fileline() == asamep->fileline() && linescov() == asamep->linescov()
                && hier() == asamep->hier() && comment() == asamep->comment());
    }
    virtual bool isPredictOptimizable() const override { return false; }
    void dataDeclp(AstCoverDecl* nodep) { m_dataDeclp = nodep; }
    // dataDecl nullptr means "use this one", but often you want "this" to
    // indicate to get data from here
    AstCoverDecl* dataDeclNullp() const { return m_dataDeclp; }
    AstCoverDecl* dataDeclThisp() { return dataDeclNullp() ? dataDeclNullp() : this; }
};
class AstCoverInc final : public AstNodeStmt {
    // Coverage analysis point; increment coverage count
    // Parents:  {statement list}
    // Children: none
private:
    AstCoverDecl* m_declp;  // [After V3Coverage] Pointer to declaration
public:
    AstCoverInc(FileLine* fl, AstCoverDecl* declp)
        : ASTGEN_SUPER_CoverInc(fl)
        , m_declp{declp} {}
    ASTGEN_MEMBERS_CoverInc;
    virtual const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    virtual bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstCoverInc*>(samep)->declp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    // but isPure()  true
    AstCoverDecl* declp() const { return m_declp; }  // Where defined
};
class AstCoverToggle final : public AstNodeStmt {
    // Toggle analysis of given signal
    // Parents:  MODULE
    // Children: AstCoverInc, orig var, change det var
public:
    AstCoverToggle(FileLine* fl, AstCoverInc* incp, AstNode* origp, AstNode* changep)
        : ASTGEN_SUPER_CoverToggle(fl) {
        setOp1p(incp);
        setOp2p(origp);
        setOp3p(changep);
    }
    ASTGEN_MEMBERS_CoverToggle;
    virtual int instrCount() const override { return 3 + INSTR_COUNT_BRANCH + INSTR_COUNT_LD; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isOutputter() const override {
        return false;  // Though the AstCoverInc under this is an outputter
    }
    // but isPure()  true
    AstCoverInc* incp() const { return VN_AS(op1p(), CoverInc); }
    void incp(AstCoverInc* nodep) { setOp1p(nodep); }
    AstNode* origp() const { return op2p(); }
    AstNode* changep() const { return op3p(); }
};
class AstDelay final : public AstNodeStmt {
    // Delay statement
public:
    AstDelay(FileLine* fl, AstNode* lhsp, AstNode* stmtsp)
        : ASTGEN_SUPER_Delay(fl) {
        setOp1p(lhsp);
        setNOp2p(stmtsp);
    }
    ASTGEN_MEMBERS_Delay;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    //
    AstNode* lhsp() const { return op1p(); }  // op1 = delay value
    void lhsp(AstNode* nodep) { setOp1p(nodep); }
    void stmtsp(AstNode* nodep) { setOp2p(nodep); }  // op2 = statements under delay
    AstNode* stmtsp() const { return op2p(); }
};
class AstDisable final : public AstNodeStmt {
private:
    string m_name;  // Name of block
public:
    AstDisable(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Disable(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_Disable;
    virtual string name() const override { return m_name; }  // * = Block name
    virtual void name(const string& flag) override { m_name = flag; }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstDisableFork final : public AstNodeStmt {
    // A "disable fork" statement
public:
    explicit AstDisableFork(FileLine* fl)
        : ASTGEN_SUPER_DisableFork(fl) {}
    ASTGEN_MEMBERS_DisableFork;
};
class AstDisplay final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
    // Children: SFORMATF to generate print string
private:
    VDisplayType m_displayType;

public:
    AstDisplay(FileLine* fl, VDisplayType dispType, const string& text, AstNode* filep,
               AstNode* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        setOp1p(new AstSFormatF{fl, text, true, exprsp, missingArgChar});
        setNOp3p(filep);
    }
    AstDisplay(FileLine* fl, VDisplayType dispType, AstNode* filep, AstNode* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_Display(fl)
        , m_displayType{dispType} {
        setOp1p(new AstSFormatF{fl, AstSFormatF::NoFormat(), exprsp, missingArgChar});
        setNOp3p(filep);
    }
    ASTGEN_MEMBERS_Display;
    virtual void dump(std::ostream& str) const override;
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override {
        return (filep() ? string("$f") + string(displayType().ascii())
                        : string("$") + string(displayType().ascii()));
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return displayType() == static_cast<const AstDisplay*>(samep)->displayType();
    }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    VDisplayType displayType() const { return m_displayType; }
    void displayType(VDisplayType type) { m_displayType = type; }
    // * = Add a newline for $display
    bool addNewline() const { return displayType().addNewline(); }
    void fmtp(AstSFormatF* nodep) { addOp1p(nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_AS(op1p(), SFormatF); }
    AstNode* filep() const { return op3p(); }
    void filep(AstNodeVarRef* nodep) { setNOp3p((AstNode*)nodep); }
};
class AstDpiExportUpdated final : public AstNodeStmt {
    // Denotes that the referenced variable may have been updated via a DPI Export
public:
    inline AstDpiExportUpdated(FileLine* fl, AstVarScope* varScopep);
    ASTGEN_MEMBERS_DpiExportUpdated;
    inline AstVarScope* varScopep() const;
};
class AstDumpCtl final : public AstNodeStmt {
    // $dumpon etc
    // Parents: expr
    // Child: expr based on type of control statement
    const VDumpCtlType m_ctlType;  // Type of operation
public:
    AstDumpCtl(FileLine* fl, VDumpCtlType ctlType, AstNode* exprp = nullptr)
        : ASTGEN_SUPER_DumpCtl(fl)
        , m_ctlType{ctlType} {
        setNOp1p(exprp);
    }
    ASTGEN_MEMBERS_DumpCtl;
    virtual string verilogKwd() const override { return ctlType().ascii(); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool cleanOut() const { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    VDumpCtlType ctlType() const { return m_ctlType; }
    AstNode* exprp() const { return op1p(); }  // op2 = Expressions to output
    void exprp(AstNode* nodep) { setOp1p(nodep); }
};
class AstEventControl final : public AstNodeStmt {
    // Parents: stmtlist
public:
    AstEventControl(FileLine* fl, AstSenTree* sensesp, AstNode* stmtsp)
        : ASTGEN_SUPER_EventControl(fl) {
        setNOp1p(sensesp);
        setNOp2p(stmtsp);
    }
    ASTGEN_MEMBERS_EventControl;
    virtual string verilogKwd() const override { return "@(%l) %r"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return false; }
    virtual int instrCount() const override { return 0; }
    AstSenTree* sensesp() const { return VN_AS(op1p(), SenTree); }
    AstNode* stmtsp() const { return op2p(); }
};
class AstFClose final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFClose(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FClose(fl) {
        setNOp2p(filep);
    }
    ASTGEN_MEMBERS_FClose;
    virtual string verilogKwd() const override { return "$fclose"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstFFlush final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: file which must be a varref
public:
    AstFFlush(FileLine* fl, AstNode* filep)
        : ASTGEN_SUPER_FFlush(fl) {
        setNOp2p(filep);
    }
    ASTGEN_MEMBERS_FFlush;
    virtual string verilogKwd() const override { return "$fflush"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op2p(); }
    void filep(AstNodeVarRef* nodep) { setNOp2p((AstNode*)nodep); }
};
class AstFOpen final : public AstNodeStmt {
    // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
public:
    AstFOpen(FileLine* fl, AstNode* filep, AstNode* filenamep, AstNode* modep)
        : ASTGEN_SUPER_FOpen(fl) {
        setOp1p(filep);
        setOp2p(filenamep);
        setOp3p(modep);
    }
    ASTGEN_MEMBERS_FOpen;
    virtual string verilogKwd() const override { return "$fopen"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op1p(); }
    AstNode* filenamep() const { return op2p(); }
    AstNode* modep() const { return op3p(); }
};
class AstFOpenMcd final : public AstNodeStmt {
    // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
public:
    AstFOpenMcd(FileLine* fl, AstNode* filep, AstNode* filenamep)
        : ASTGEN_SUPER_FOpenMcd(fl) {
        setOp1p(filep);
        setOp2p(filenamep);
    }
    ASTGEN_MEMBERS_FOpenMcd;
    virtual string verilogKwd() const override { return "$fopen"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* filep() const { return op1p(); }
    AstNode* filenamep() const { return op2p(); }
};
class AstFinish final : public AstNodeStmt {
public:
    explicit AstFinish(FileLine* fl)
        : ASTGEN_SUPER_Finish(fl) {}
    ASTGEN_MEMBERS_Finish;
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual int instrCount() const override { return 0; }  // Rarely executes
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};
class AstForeach final : public AstNodeStmt {
public:
    AstForeach(FileLine* fl, AstNode* arrayp, AstNode* bodysp)
        : ASTGEN_SUPER_Foreach(fl) {
        setOp1p(arrayp);
        addNOp4p(bodysp);
    }
    ASTGEN_MEMBERS_Foreach;
    AstNode* arrayp() const { return op1p(); }  // op1 = array and index vars
    AstNode* bodysp() const { return op4p(); }  // op4 = body of loop
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstJumpBlock final : public AstNodeStmt {
    // Block of code including a JumpGo and JumpLabel
    // Parents:  {statement list}
    // Children: {statement list, with JumpGo and JumpLabel below}
private:
    AstJumpLabel* m_labelp = nullptr;  // [After V3Jump] Pointer to declaration
    int m_labelNum = 0;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    // After construction must call ->labelp to associate with appropriate label
    AstJumpBlock(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_JumpBlock(fl) {
        addNOp1p(stmtsp);
    }
    virtual const char* broken() const override;
    virtual void cloneRelink() override;
    ASTGEN_MEMBERS_JumpBlock;
    virtual int instrCount() const override { return 0; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    // op1 = Statements
    AstNode* stmtsp() const { return op1p(); }  // op1 = List of statements
    void addStmtsp(AstNode* nodep) { addNOp1p(nodep); }
    AstNode* endStmtsp() const { return op2p(); }  // op1 = List of end-of-block
    void addEndStmtsp(AstNode* nodep) { addNOp2p(nodep); }
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
    ASTGEN_MEMBERS_JumpGo;
    const char* broken() const override;
    void cloneRelink() override;
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* samep) const override {
        return labelp() == static_cast<const AstJumpGo*>(samep)->labelp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isBrancher() const override {
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
    ASTGEN_MEMBERS_JumpLabel;
    virtual bool maybePointedTo() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(!blockp()->brokeExistsAbove());
        BROKEN_RTN(blockp()->labelp() != this);
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_blockp->clonep()) m_blockp = m_blockp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 0; }
    virtual bool same(const AstNode* samep) const override {
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
    ASTGEN_MEMBERS_MonitorOff;
    virtual string verilogKwd() const override { return m_off ? "$monitoroff" : "$monitoron"; }
    virtual bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    virtual bool isPredictOptimizable() const override {
        return false;
    }  // Though deleted before opt
    virtual bool isPure() const override { return false; }  // Though deleted before opt
    virtual bool isOutputter() const override { return true; }  // Though deleted before opt
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    virtual bool same(const AstNode* samep) const override {
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
    ASTGEN_MEMBERS_PrintTimeScale;
    virtual void name(const string& name) override { m_name = name; }
    virtual string name() const override { return m_name; }  // * = Var name
    virtual void dump(std::ostream& str) const override;
    virtual string verilogKwd() const override { return "$printtimescale"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VTimescale timeunit() const { return m_timeunit; }
};
class AstRelease final : public AstNodeStmt {
    // Procedural 'release' statement
public:
    AstRelease(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_Release(fl) {
        setOp1p(lhsp);
    }
    ASTGEN_MEMBERS_Release;
    AstNode* lhsp() const { return op1p(); }
};
class AstRepeat final : public AstNodeStmt {
public:
    AstRepeat(FileLine* fl, AstNode* countp, AstNode* bodysp)
        : ASTGEN_SUPER_Repeat(fl) {
        setOp2p(countp);
        addNOp3p(bodysp);
    }
    ASTGEN_MEMBERS_Repeat;
    AstNode* countp() const { return op2p(); }  // op2 = condition to continue
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
    virtual bool isGateOptimizable() const override {
        return false;
    }  // Not relevant - converted to FOR
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstReturn final : public AstNodeStmt {
public:
    explicit AstReturn(FileLine* fl, AstNode* lhsp = nullptr)
        : ASTGEN_SUPER_Return(fl) {
        setNOp1p(lhsp);
    }
    ASTGEN_MEMBERS_Return;
    virtual string verilogKwd() const override { return "return"; }
    AstNode* lhsp() const { return op1p(); }
    virtual bool isBrancher() const override {
        return true;  // SPECIAL: We don't process code after breaks
    }
};
class AstSFormat final : public AstNodeStmt {
    // Parents: statement container
    // Children: string to load
    // Children: SFORMATF to generate print string
public:
    AstSFormat(FileLine* fl, AstNode* lhsp, const string& text, AstNode* exprsp,
               char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        setOp1p(new AstSFormatF(fl, text, true, exprsp, missingArgChar));
        setOp3p(lhsp);
    }
    AstSFormat(FileLine* fl, AstNode* lhsp, AstNode* exprsp, char missingArgChar = 'd')
        : ASTGEN_SUPER_SFormat(fl) {
        setOp1p(new AstSFormatF(fl, AstSFormatF::NoFormat(), exprsp, missingArgChar));
        setOp3p(lhsp);
    }
    ASTGEN_MEMBERS_SFormat;
    virtual const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    virtual string verilogKwd() const override { return "$sformat"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isPure() const override { return true; }
    virtual bool isOutputter() const override { return false; }
    virtual bool cleanOut() const { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    void fmtp(AstSFormatF* nodep) { addOp1p(nodep); }  // op1 = To-String formatter
    AstSFormatF* fmtp() const { return VN_AS(op1p(), SFormatF); }
    AstNode* lhsp() const { return op3p(); }
    void lhsp(AstNode* nodep) { setOp3p(nodep); }
};
class AstStop final : public AstNodeStmt {
public:
    AstStop(FileLine* fl, bool maybe)
        : ASTGEN_SUPER_Stop(fl) {}
    ASTGEN_MEMBERS_Stop;
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override {
        return false;
    }  // SPECIAL: $display has 'visual' ordering
    virtual bool isOutputter() const override { return true; }  // SPECIAL: $display makes output
    virtual bool isUnlikely() const override { return true; }
    virtual int instrCount() const override { return 0; }  // Rarely executes
    virtual bool same(const AstNode* samep) const override {
        return fileline() == samep->fileline();
    }
};
class AstSysFuncAsTask final : public AstNodeStmt {
    // Call what is normally a system function (with a return) in a non-return context
    // Parents: stmtlist
    // Children: a system function
public:
    AstSysFuncAsTask(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_SysFuncAsTask(fl) {
        addNOp1p(exprsp);
    }
    ASTGEN_MEMBERS_SysFuncAsTask;
    virtual string verilogKwd() const override { return ""; }
    virtual bool isGateOptimizable() const override { return true; }
    virtual bool isPredictOptimizable() const override { return true; }
    virtual bool isPure() const override { return true; }
    virtual bool isOutputter() const override { return false; }
    virtual int instrCount() const override { return 0; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* lhsp() const { return op1p(); }  // op1 = Expressions to eval
    void lhsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to eval
};
class AstSysIgnore final : public AstNodeStmt {
    // Parents: stmtlist
    // Children: varrefs or exprs
public:
    AstSysIgnore(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_SysIgnore(fl) {
        addNOp1p(exprsp);
    }
    ASTGEN_MEMBERS_SysIgnore;
    virtual string verilogKwd() const override { return "$ignored"; }
    virtual bool isGateOptimizable() const override { return false; }  // Though deleted before opt
    virtual bool isPredictOptimizable() const override {
        return false;
    }  // Though deleted before opt
    virtual bool isPure() const override { return false; }  // Though deleted before opt
    virtual bool isOutputter() const override { return true; }  // Though deleted before opt
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    AstNode* exprsp() const { return op1p(); }  // op1 = Expressions to output
    void exprsp(AstNode* nodep) { addOp1p(nodep); }  // op1 = Expressions to output
};
class AstSystemT final : public AstNodeStmt {
    // $system used as task
public:
    AstSystemT(FileLine* fl, AstNode* lhsp)
        : ASTGEN_SUPER_SystemT(fl) {
        setOp1p(lhsp);
    }
    ASTGEN_MEMBERS_SystemT;
    virtual string verilogKwd() const override { return "$system"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool isUnlikely() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    AstNode* lhsp() const { return op1p(); }
};
class AstTimeFormat final : public AstNodeStmt {
    // Parents: stmtlist
public:
    AstTimeFormat(FileLine* fl, AstNode* unitsp, AstNode* precisionp, AstNode* suffixp,
                  AstNode* widthp)
        : ASTGEN_SUPER_TimeFormat(fl) {
        setOp1p(unitsp);
        setOp2p(precisionp);
        setOp3p(suffixp);
        setOp4p(widthp);
    }
    ASTGEN_MEMBERS_TimeFormat;
    virtual string verilogKwd() const override { return "$timeformat"; }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual int instrCount() const override { return INSTR_COUNT_PLI; }
    AstNode* unitsp() const { return op1p(); }
    AstNode* precisionp() const { return op2p(); }
    AstNode* suffixp() const { return op3p(); }
    AstNode* widthp() const { return op4p(); }
};
class AstTraceDecl final : public AstNodeStmt {
    // Trace point declaration
    // Separate from AstTraceInc; as a declaration can't be deleted
    // Parents:  {statement list}
    // Children: expression being traced
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
                 AstNode* valuep, const VNumRange& bitRange, const VNumRange& arrayRange)
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
        addNOp1p(valuep);
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 100; }  // Large...
    ASTGEN_MEMBERS_TraceDecl;
    virtual string name() const override { return m_showname; }
    virtual bool maybePointedTo() const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override { return false; }
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
    AstNode* valuep() const { return op1p(); }
};
class AstTraceInc final : public AstNodeStmt {
    // Trace point dump
    // Parents:  {statement list}
    // Children: op1: things to emit before this node,
    //           op2: expression being traced (from decl)

private:
    AstTraceDecl* m_declp;  // Pointer to declaration
    const bool m_full;  // Is this a full vs incremental dump
    const uint32_t m_baseCode;  // Trace code base value in function containing this AstTraceInc

public:
    AstTraceInc(FileLine* fl, AstTraceDecl* declp, bool full, uint32_t baseCode = 0)
        : ASTGEN_SUPER_TraceInc(fl)
        , m_declp{declp}
        , m_full{full}
        , m_baseCode{baseCode} {
        dtypeFrom(declp);
        addOp2p(declp->valuep()->cloneTree(true));
    }
    ASTGEN_MEMBERS_TraceInc;
    virtual const char* broken() const override {
        BROKEN_RTN(!declp()->brokeExists());
        return nullptr;
    }
    virtual void cloneRelink() override {
        if (m_declp->clonep()) m_declp = m_declp->clonep();
    }
    virtual void dump(std::ostream& str) const override;
    virtual int instrCount() const override { return 10 + 2 * INSTR_COUNT_LD; }
    virtual bool hasDType() const override { return true; }
    virtual bool same(const AstNode* samep) const override {
        return declp() == static_cast<const AstTraceInc*>(samep)->declp();
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    // but isPure()  true
    // op1 = Statements before the value
    AstNode* precondsp() const { return op1p(); }
    void addPrecondsp(AstNode* newp) { addOp1p(newp); }
    AstNode* valuep() const { return op2p(); }
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
    ASTGEN_MEMBERS_TracePopNamePrefix;
    virtual bool same(const AstNode* samep) const override { return false; }
    unsigned count() const { return m_count; }
};
class AstTracePushNamePrefix final : public AstNodeStmt {
    const string m_prefix;  // Prefix to add to signal names
public:
    AstTracePushNamePrefix(FileLine* fl, const string& prefix)
        : ASTGEN_SUPER_TracePushNamePrefix(fl)
        , m_prefix{prefix} {}
    ASTGEN_MEMBERS_TracePushNamePrefix;
    virtual bool same(const AstNode* samep) const override { return false; }
    string prefix() const { return m_prefix; }
};
class AstUCStmt final : public AstNodeStmt {
    // User $c statement
public:
    AstUCStmt(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_UCStmt(fl) {
        addNOp1p(exprsp);
    }
    ASTGEN_MEMBERS_UCStmt;
    AstNode* bodysp() const { return op1p(); }  // op1 = expressions to print
    virtual bool isGateOptimizable() const override { return false; }
    virtual bool isPredictOptimizable() const override { return false; }
    virtual bool isPure() const override { return false; }
    virtual bool isOutputter() const override { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
};
class AstWait final : public AstNodeStmt {
public:
    AstWait(FileLine* fl, AstNode* condp, AstNode* bodysp)
        : ASTGEN_SUPER_Wait(fl) {
        setOp2p(condp);
        addNOp3p(bodysp);
    }
    ASTGEN_MEMBERS_Wait;
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstWaitFork final : public AstNodeStmt {
    // A "wait fork" statement
public:
    explicit AstWaitFork(FileLine* fl)
        : ASTGEN_SUPER_WaitFork(fl) {}
    ASTGEN_MEMBERS_WaitFork;
};
class AstWhile final : public AstNodeStmt {
public:
    AstWhile(FileLine* fl, AstNode* condp, AstNode* bodysp = nullptr, AstNode* incsp = nullptr)
        : ASTGEN_SUPER_While(fl) {
        setOp2p(condp);
        addNOp3p(bodysp);
        addNOp4p(incsp);
    }
    ASTGEN_MEMBERS_While;
    // op1 = prepare statements for condition (exec every loop)
    AstNode* precondsp() const { return op1p(); }
    AstNode* condp() const { return op2p(); }  // op2 = condition to continue
    AstNode* bodysp() const { return op3p(); }  // op3 = body of loop
    AstNode* incsp() const { return op4p(); }  // op4 = increment (if from a FOR loop)
    void addPrecondsp(AstNode* newp) { addOp1p(newp); }
    void addBodysp(AstNode* newp) { addOp3p(newp); }
    void addIncsp(AstNode* newp) { addOp4p(newp); }
    virtual bool isGateOptimizable() const override { return false; }
    virtual int instrCount() const override { return INSTR_COUNT_BRANCH; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    // Stop statement searchback here
    virtual void addBeforeStmt(AstNode* newp, AstNode* belowp) override;
    // Stop statement searchback here
    virtual void addNextStmt(AstNode* newp, AstNode* belowp) override;
    bool isFirstInMyListOfStatements(AstNode* n) const override { return n == bodysp(); }
};
class AstWith final : public AstNodeStmt {
    // Used as argument to method, then to AstCMethodHard
    // dtypep() contains the with lambda's return dtype
    // Parents: funcref (similar to AstArg)
    // Children: LambdaArgRef that declares the item variable
    // Children: LambdaArgRef that declares the item.index variable
    // Children: math (equation establishing the with)
public:
    AstWith(FileLine* fl, AstLambdaArgRef* indexArgRefp, AstLambdaArgRef* valueArgRefp,
            AstNode* exprp)
        : ASTGEN_SUPER_With(fl) {
        addOp1p((AstNode*)indexArgRefp);
        addOp2p((AstNode*)valueArgRefp);
        addNOp3p(exprp);
    }
    ASTGEN_MEMBERS_With;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual const char* broken() const override {
        BROKEN_RTN(!indexArgRefp());  // varp needed to know lambda's arg dtype
        BROKEN_RTN(!valueArgRefp());  // varp needed to know lambda's arg dtype
        return nullptr;
    }
    //
    AstLambdaArgRef* indexArgRefp() const { return VN_AS(op1p(), LambdaArgRef); }
    AstLambdaArgRef* valueArgRefp() const { return VN_AS(op2p(), LambdaArgRef); }
    AstNode* exprp() const { return op3p(); }
};
class AstWithParse final : public AstNodeStmt {
    // In early parse, FUNC(index) WITH equation-using-index
    // Replaced with AstWith
    // Parents: math|stmt
    // Children: funcref, math
public:
    AstWithParse(FileLine* fl, bool stmt, AstNode* funcrefp, AstNode* exprp)
        : ASTGEN_SUPER_WithParse(fl) {
        statement(stmt);
        setOp1p(funcrefp);
        addNOp2p(exprp);
    }
    ASTGEN_MEMBERS_WithParse;
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    //
    AstNode* funcrefp() const { return op1p(); }
    AstNode* exprp() const { return op2p(); }
};

// === AstNodeAssign ===
class AstAssign final : public AstNodeAssign {
public:
    AstAssign(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_Assign(fl, lhsp, rhsp, timingControlp) {
        dtypeFrom(lhsp);
    }
    ASTGEN_MEMBERS_Assign;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssign(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignAlias final : public AstNodeAssign {
    // Like AstAssignW, but a true bidirect interconnection alias
    // If both sides are wires, there's no LHS vs RHS,
public:
    AstAssignAlias(FileLine* fl, AstVarRef* lhsp, AstVarRef* rhsp)
        : ASTGEN_SUPER_AssignAlias(fl, (AstNode*)lhsp, (AstNode*)rhsp) {}
    ASTGEN_MEMBERS_AssignAlias;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        V3ERROR_NA_RETURN(nullptr);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return false; }
};
class AstAssignDly final : public AstNodeAssign {
public:
    AstAssignDly(FileLine* fl, AstNode* lhsp, AstNode* rhsp, AstNode* timingControlp = nullptr)
        : ASTGEN_SUPER_AssignDly(fl, lhsp, rhsp, timingControlp) {}
    ASTGEN_MEMBERS_AssignDly;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignDly(this->fileline(), lhsp, rhsp);
    }
    virtual bool isGateOptimizable() const override { return false; }
    virtual string verilogKwd() const override { return "<="; }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignForce final : public AstNodeAssign {
    // Procedural 'force' statement
public:
    AstAssignForce(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AssignForce(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AssignForce;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignForce{this->fileline(), lhsp, rhsp};
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignPost final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPost(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AssignPost(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AssignPost;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignPost(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignPre final : public AstNodeAssign {
    // Like Assign, but predelayed assignment requiring special order handling
public:
    AstAssignPre(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AssignPre(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AssignPre;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignPre(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
};
class AstAssignVarScope final : public AstNodeAssign {
    // Assign two VarScopes to each other
public:
    AstAssignVarScope(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AssignVarScope(fl, lhsp, rhsp) {
        dtypeFrom(rhsp);
    }
    ASTGEN_MEMBERS_AssignVarScope;
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignVarScope(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return false; }
};
class AstAssignW final : public AstNodeAssign {
    // Like assign, but wire/assign's in verilog, the only setting of the specified variable
public:
    AstAssignW(FileLine* fl, AstNode* lhsp, AstNode* rhsp)
        : ASTGEN_SUPER_AssignW(fl, lhsp, rhsp) {}
    ASTGEN_MEMBERS_AssignW;
    AstStrengthSpec* strengthSpecp() const { return VN_AS(op4p(), StrengthSpec); }
    void strengthSpecp(AstStrengthSpec* const strengthSpecp) { setOp4p((AstNode*)strengthSpecp); }
    virtual AstNode* cloneType(AstNode* lhsp, AstNode* rhsp) override {
        return new AstAssignW(this->fileline(), lhsp, rhsp);
    }
    virtual bool brokeLhsMustBeLvalue() const override { return true; }
    AstAlways* convertToAlways() {
        AstNode* const lhs1p = lhsp()->unlinkFrBack();
        AstNode* const rhs1p = rhsp()->unlinkFrBack();
        AstAlways* const newp = new AstAlways(fileline(), VAlwaysKwd::ALWAYS, nullptr,
                                              new AstAssign(fileline(), lhs1p, rhs1p));
        replaceWith(newp);  // User expected to then deleteTree();
        return newp;
    }
};

// === AstNodeCCall ===
class AstCCall final : public AstNodeCCall {
    // C++ function call
    // Parents:  Anything above a statement
    // Children: Args to the function

    string m_selfPointer;  // Output code object pointer (e.g.: 'this')

public:
    AstCCall(FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER_CCall(fl, funcp, argsp) {}
    ASTGEN_MEMBERS_CCall;

    string selfPointer() const { return m_selfPointer; }
    void selfPointer(const string& value) { m_selfPointer = value; }
    string selfPointerProtect(bool useSelfForThis) const;
};
class AstCMethodCall final : public AstNodeCCall {
    // C++ method call
    // Parents:  Anything above a statement
    // Children: Args to the function
public:
    AstCMethodCall(FileLine* fl, AstNode* fromp, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER_CMethodCall(fl, funcp, argsp) {
        setOp1p(fromp);
    }
    ASTGEN_MEMBERS_CMethodCall;
    virtual const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeCCall::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
    AstNode* fromp() const {
        return op1p();
    }  // op1 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp1p(nodep); }
};
class AstCNew final : public AstNodeCCall {
    // C++ new() call
    // Parents:  Anything above an expression
    // Children: Args to the function
public:
    AstCNew(FileLine* fl, AstCFunc* funcp, AstNode* argsp = nullptr)
        : ASTGEN_SUPER_CNew(fl, funcp, argsp) {
        statement(false);
    }
    virtual bool hasDType() const override { return true; }
    ASTGEN_MEMBERS_CNew;
};

// === AstNodeCase ===
class AstCase final : public AstNodeCase {
    // Case statement
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
private:
    VCaseType m_casex;  // 0=case, 1=casex, 2=casez
    bool m_fullPragma = false;  // Synthesis full_case
    bool m_parallelPragma = false;  // Synthesis parallel_case
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstCase(FileLine* fl, VCaseType casex, AstNode* exprp, AstNode* casesp)
        : ASTGEN_SUPER_Case(fl, exprp, casesp)
        , m_casex{casex} {}
    ASTGEN_MEMBERS_Case;
    virtual string verilogKwd() const override {
        return casez() ? "casez" : casex() ? "casex" : "case";
    }
    virtual bool same(const AstNode* samep) const override {
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
    // Parents:  {statement list}
    // exprp Children:  MATHs
    // casesp Children: CASEITEMs
public:
    AstGenCase(FileLine* fl, AstNode* exprp, AstNode* casesp)
        : ASTGEN_SUPER_GenCase(fl, exprp, casesp) {}
    ASTGEN_MEMBERS_GenCase;
};

// === AstNodeCoverOrAssert ===
class AstAssert final : public AstNodeCoverOrAssert {
public:
    ASTGEN_MEMBERS_Assert;
    AstAssert(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp, bool immediate,
              const string& name = "")
        : ASTGEN_SUPER_Assert(fl, propp, passsp, immediate, name) {
        addNOp3p(failsp);
    }
    AstNode* failsp() const { return op3p(); }  // op3 = if assertion fails
};
class AstAssertIntrinsic final : public AstNodeCoverOrAssert {
    // A $cast or other compiler inserted assert, that must run even without --assert option
public:
    ASTGEN_MEMBERS_AssertIntrinsic;
    AstAssertIntrinsic(FileLine* fl, AstNode* propp, AstNode* passsp, AstNode* failsp,
                       bool immediate, const string& name = "")
        : ASTGEN_SUPER_AssertIntrinsic(fl, propp, passsp, immediate, name) {
        addNOp3p(failsp);
    }
    AstNode* failsp() const { return op3p(); }  // op3 = if assertion fails
};
class AstCover final : public AstNodeCoverOrAssert {
public:
    ASTGEN_MEMBERS_Cover;
    AstCover(FileLine* fl, AstNode* propp, AstNode* stmtsp, bool immediate,
             const string& name = "")
        : ASTGEN_SUPER_Cover(fl, propp, stmtsp, immediate, name) {}
    AstNode* coverincp() const { return op3p(); }  // op3 = coverage node
    void coverincp(AstCoverInc* nodep) { addOp3p(nodep); }  // op3 = coverage node
    virtual bool immediate() const { return false; }
};
class AstRestrict final : public AstNodeCoverOrAssert {
public:
    ASTGEN_MEMBERS_Restrict;
    AstRestrict(FileLine* fl, AstNode* propp)
        : ASTGEN_SUPER_Restrict(fl, propp, nullptr, false, "") {}
};

// === AstNodeFTaskRef ===
class AstFuncRef final : public AstNodeFTaskRef {
    // A reference to a function
public:
    AstFuncRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
        : ASTGEN_SUPER_FuncRef(fl, false, namep, pinsp) {}
    AstFuncRef(FileLine* fl, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER_FuncRef(fl, false, name, pinsp) {}
    ASTGEN_MEMBERS_FuncRef;
    virtual bool hasDType() const override { return true; }
};
class AstMethodCall final : public AstNodeFTaskRef {
    // A reference to a member task (or function)
    // PARENTS: stmt/math
    // Not all calls are statments vs math.  AstNodeStmt needs isStatement() to deal.
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
public:
    AstMethodCall(FileLine* fl, AstNode* fromp, VFlagChildDType, const string& name,
                  AstNode* pinsp)
        : ASTGEN_SUPER_MethodCall(fl, false, name, pinsp) {
        setOp2p(fromp);
        dtypep(nullptr);  // V3Width will resolve
    }
    AstMethodCall(FileLine* fl, AstNode* fromp, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER_MethodCall(fl, false, name, pinsp) {
        setOp2p(fromp);
    }
    ASTGEN_MEMBERS_MethodCall;
    virtual const char* broken() const override {
        BROKEN_BASE_RTN(AstNodeFTaskRef::broken());
        BROKEN_RTN(!fromp());
        return nullptr;
    }
    virtual void dump(std::ostream& str) const override;
    virtual bool hasDType() const override { return true; }
    void makeStatement() {
        statement(true);
        dtypeSetVoid();
    }
    AstNode* fromp() const {
        return op2p();
    }  // op2 = Extracting what (nullptr=TBD during parsing)
    void fromp(AstNode* nodep) { setOp2p(nodep); }
};
class AstNew final : public AstNodeFTaskRef {
    // New as constructor
    // Don't need the class we are extracting from, as the "fromp()"'s datatype can get us to it
    // Parents: math|stmt
    // Children: varref|arraysel, math
public:
    AstNew(FileLine* fl, AstNode* pinsp)
        : ASTGEN_SUPER_New(fl, false, "new", pinsp) {}
    ASTGEN_MEMBERS_New;
    virtual bool cleanOut() const { return true; }
    virtual bool same(const AstNode* /*samep*/) const override { return true; }
    virtual bool hasDType() const override { return true; }
    virtual int instrCount() const override { return widthInstrs(); }
};
class AstTaskRef final : public AstNodeFTaskRef {
    // A reference to a task
public:
    AstTaskRef(FileLine* fl, AstParseRef* namep, AstNode* pinsp)
        : ASTGEN_SUPER_TaskRef(fl, true, namep, pinsp) {
        statement(true);
    }
    AstTaskRef(FileLine* fl, const string& name, AstNode* pinsp)
        : ASTGEN_SUPER_TaskRef(fl, true, name, pinsp) {}
    ASTGEN_MEMBERS_TaskRef;
};

// === AstNodeFor ===
class AstGenFor final : public AstNodeFor {
public:
    AstGenFor(FileLine* fl, AstNode* initsp, AstNode* condp, AstNode* incsp, AstNode* bodysp)
        : ASTGEN_SUPER_GenFor(fl, initsp, condp, incsp, bodysp) {}
    ASTGEN_MEMBERS_GenFor;
};

// === AstNodeIf ===
class AstGenIf final : public AstNodeIf {
public:
    AstGenIf(FileLine* fl, AstNode* condp, AstNode* ifsp, AstNode* elsesp)
        : ASTGEN_SUPER_GenIf(fl, condp, ifsp, elsesp) {}
    ASTGEN_MEMBERS_GenIf;
};
class AstIf final : public AstNodeIf {
private:
    bool m_uniquePragma = false;  // unique case
    bool m_unique0Pragma = false;  // unique0 case
    bool m_priorityPragma = false;  // priority case
public:
    AstIf(FileLine* fl, AstNode* condp, AstNode* ifsp = nullptr, AstNode* elsesp = nullptr)
        : ASTGEN_SUPER_If(fl, condp, ifsp, elsesp) {}
    ASTGEN_MEMBERS_If;
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
    AstReadMem(FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp, AstNode* lsbp,
               AstNode* msbp)
        : ASTGEN_SUPER_ReadMem(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTGEN_MEMBERS_ReadMem;
    virtual string verilogKwd() const override { return (isHex() ? "$readmemh" : "$readmemb"); }
    virtual const char* cFuncPrefixp() const override { return "VL_READMEM_"; }
};
class AstWriteMem final : public AstNodeReadWriteMem {
public:
    AstWriteMem(FileLine* fl, bool hex, AstNode* filenamep, AstNode* memp, AstNode* lsbp,
                AstNode* msbp)
        : ASTGEN_SUPER_WriteMem(fl, hex, filenamep, memp, lsbp, msbp) {}
    ASTGEN_MEMBERS_WriteMem;
    virtual string verilogKwd() const override { return (isHex() ? "$writememh" : "$writememb"); }
    virtual const char* cFuncPrefixp() const override { return "VL_WRITEMEM_"; }
};

// === AstNodeText ===
class AstScCtor final : public AstNodeText {
public:
    AstScCtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScCtor(fl, textp) {}
    ASTGEN_MEMBERS_ScCtor;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};
class AstScDtor final : public AstNodeText {
public:
    AstScDtor(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScDtor(fl, textp) {}
    ASTGEN_MEMBERS_ScDtor;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};
class AstScHdr final : public AstNodeText {
public:
    AstScHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScHdr(fl, textp) {}
    ASTGEN_MEMBERS_ScHdr;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};
class AstScImp final : public AstNodeText {
public:
    AstScImp(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScImp(fl, textp) {}
    ASTGEN_MEMBERS_ScImp;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};
class AstScImpHdr final : public AstNodeText {
public:
    AstScImpHdr(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScImpHdr(fl, textp) {}
    ASTGEN_MEMBERS_ScImpHdr;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};
class AstScInt final : public AstNodeText {
public:
    AstScInt(FileLine* fl, const string& textp)
        : ASTGEN_SUPER_ScInt(fl, textp) {}
    ASTGEN_MEMBERS_ScInt;
    virtual bool isPure() const override { return false; }  // SPECIAL: User may order w/other sigs
    virtual bool isOutputter() const override { return true; }
};

// === AstNodeSimpleText ===
class AstText final : public AstNodeSimpleText {
public:
    AstText(FileLine* fl, const string& textp, bool tracking = false)
        : ASTGEN_SUPER_Text(fl, textp, tracking) {}
    ASTGEN_MEMBERS_Text;
};
class AstTextBlock final : public AstNodeSimpleText {
private:
    bool m_commas;  // Comma separate emitted children
public:
    explicit AstTextBlock(FileLine* fl, const string& textp = "", bool tracking = false,
                          bool commas = false)
        : ASTGEN_SUPER_TextBlock(fl, textp, tracking)
        , m_commas(commas) {}
    ASTGEN_MEMBERS_TextBlock;
    void commas(bool flag) { m_commas = flag; }
    bool commas() const { return m_commas; }
    AstNode* nodesp() const { return op1p(); }
    void addNodep(AstNode* nodep) { addOp1p(nodep); }
    void addText(FileLine* fl, const string& textp, bool tracking = false) {
        addNodep(new AstText(fl, textp, tracking));
    }
};

#endif  // Guard
