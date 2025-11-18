// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode sub-types representing other constructs
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

class AstNodeCoverDecl VL_NOT_FINAL : public AstNode {
    // Coverage analysis point declaration
    //
    // [After V3CoverageJoin] Duplicate declaration to get data from instead
    // @astgen ptr := m_dataDeclp : Optional[AstNodeCoverDecl]
    string m_page;  // Coverage point's page tag
    string m_text;  // Coverage point's text
    string m_hier;  // Coverage point's hierarchy
    int m_binNum = 0;  // Set by V3EmitCSyms to tell final V3Emit what to increment
public:
    AstNodeCoverDecl(VNType t, FileLine* fl, const string& page, const string& comment)
        : AstNode(t, fl)
        , m_page{page}
        , m_text{comment} {}
    ASTGEN_MEMBERS_AstNodeCoverDecl;
    const char* broken() const override {
        if (m_dataDeclp
            && (m_dataDeclp == this || m_dataDeclp->m_dataDeclp)) {  // Avoid O(n^2) accessing
            v3fatalSrc("dataDeclp should point to real data, not be a list: " << cvtToHex(this));
        }
        return nullptr;
    }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int instrCount() const override { return 1 + 2 * INSTR_COUNT_LD; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    int binNum() const { return m_binNum; }
    void binNum(int flag) { m_binNum = flag; }
    virtual int size() const = 0;
    const string& comment() const { return m_text; }  // text to insert in code
    const string& page() const { return m_page; }
    const string& hier() const { return m_hier; }
    void hier(const string& flag) { m_hier = flag; }
    void comment(const string& flag) { m_text = flag; }
    bool sameNode(const AstNode* samep) const override {
        const AstNodeCoverDecl* const asamep = VN_DBG_AS(samep, NodeCoverDecl);
        return (fileline() == asamep->fileline() && hier() == asamep->hier()
                && comment() == asamep->comment() && page() == asamep->page());
    }
    bool isPredictOptimizable() const override { return false; }
    void dataDeclp(AstNodeCoverDecl* nodep) { m_dataDeclp = nodep; }
    // dataDecl nullptr means "use this one", but often you want "this" to
    // indicate to get data from here
    AstNodeCoverDecl* dataDeclNullp() const { return m_dataDeclp; }
    AstNodeCoverDecl* dataDeclThisp() { return dataDeclNullp() ? dataDeclNullp() : this; }
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
    string m_name;  // Name of task
    string m_cname;  // Name of task if DPI import
    uint64_t m_dpiOpenParent = 0;  // DPI import open array, if !=0, how many callees
    bool m_taskPublic : 1;  // Public task
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_classMethod : 1;  // Class method
    bool m_didProto : 1;  // Did prototype processing
    bool m_prototype : 1;  // Just a prototype
    bool m_dpiExport : 1;  // DPI exported
    bool m_dpiImport : 1;  // DPI imported
    bool m_dpiContext : 1;  // DPI import context
    bool m_dpiOpenChild : 1;  // DPI import open array child wrapper
    bool m_dpiTask : 1;  // DPI import task (vs. void function)
    bool m_isConstructor : 1;  // Class constructor
    bool m_isExternProto : 1;  // Extern prototype
    bool m_isExternDef : 1;  // Extern definition
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_dpiPure : 1;  // DPI import pure (vs. virtual pure)
    bool m_pureVirtual : 1;  // Pure virtual
    bool m_recursive : 1;  // Recursive or part of recursion
    bool m_static : 1;  // Static method in class
    bool m_underGenerate : 1;  // Under generate (for warning)
    bool m_verilogFunction : 1;  // Declared by user as function (versus internal-made)
    bool m_verilogTask : 1;  // Declared by user as task (versus internal-made)
    bool m_virtual : 1;  // Virtual method in class
    bool m_needProcess : 1;  // Needs access to VlProcess of the caller
    VBaseOverride m_baseOverride;  // BaseOverride (inital/final/extends)
    VLifetime m_lifetime;  // Default lifetime of local vars
    VIsCached m_purity;  // Pure state

protected:
    AstNodeFTask(VNType t, FileLine* fl, const string& name, AstNode* stmtsp)
        : AstNode{t, fl}
        , m_name{name}
        , m_taskPublic{false}
        , m_attrIsolateAssign{false}
        , m_classMethod{false}
        , m_didProto{false}
        , m_prototype{false}
        , m_dpiExport{false}
        , m_dpiImport{false}
        , m_dpiContext{false}
        , m_dpiOpenChild{false}
        , m_dpiTask{false}
        , m_isConstructor{false}
        , m_isExternProto{false}
        , m_isExternDef{false}
        , m_isHideLocal{false}
        , m_isHideProtected{false}
        , m_dpiPure{false}
        , m_pureVirtual{false}
        , m_recursive{false}
        , m_static{false}
        , m_underGenerate{false}
        , m_verilogFunction{false}
        , m_verilogTask{false}
        , m_virtual{false}
        , m_needProcess{false} {
        addStmtsp(stmtsp);
        cname(name);  // Might be overridden by dpi import/export
    }

public:
    ASTGEN_MEMBERS_AstNodeFTask;
    virtual AstNodeFTask* cloneType(const string& name) = 0;
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
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
    bool taskPublic() const { return m_taskPublic; }
    void taskPublic(bool flag) { m_taskPublic = flag; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    bool classMethod() const { return m_classMethod; }
    void classMethod(bool flag) { m_classMethod = flag; }
    bool didProto() const { return m_didProto; }
    void didProto(bool flag) { m_didProto = flag; }
    bool isExternProto() const { return m_isExternProto; }
    void isExternProto(bool flag) { m_isExternProto = flag; }
    bool isExternDef() const { return m_isExternDef; }
    void isExternDef(bool flag) { m_isExternDef = flag; }
    bool prototype() const { return m_prototype; }
    void prototype(bool flag) { m_prototype = flag; }
    bool dpiExport() const { return m_dpiExport; }
    void dpiExport(bool flag) { m_dpiExport = flag; }
    bool dpiImport() const { return m_dpiImport; }
    void dpiImport(bool flag) { m_dpiImport = flag; }
    bool dpiContext() const { return m_dpiContext; }
    void dpiContext(bool flag) { m_dpiContext = flag; }
    bool dpiOpenChild() const { return m_dpiOpenChild; }
    void dpiOpenChild(bool flag) { m_dpiOpenChild = flag; }
    bool dpiTask() const { return m_dpiTask; }
    void dpiTask(bool flag) { m_dpiTask = flag; }
    bool isConstructor() const { return m_isConstructor; }
    void isConstructor(bool flag) { m_isConstructor = flag; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    bool dpiPure() const { return m_dpiPure; }
    void dpiPure(bool flag) { m_dpiPure = flag; }
    bool pureVirtual() const { return m_pureVirtual; }
    void pureVirtual(bool flag) { m_pureVirtual = flag; }
    bool recursive() const { return m_recursive; }
    void recursive(bool flag) { m_recursive = flag; }
    bool isStatic() const { return m_static; }
    void isStatic(bool flag) { m_static = flag; }
    bool underGenerate() const { return m_underGenerate; }
    void underGenerate(bool flag) { m_underGenerate = flag; }
    bool verilogFunction() const { return m_verilogFunction; }
    void verilogFunction(bool flag) { m_verilogFunction = flag; }
    bool verilogTask() const { return m_verilogTask; }
    void verilogTask(bool flag) { m_verilogTask = flag; }
    bool isVirtual() const { return m_virtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool needProcess() const { return m_needProcess; }
    void setNeedProcess() { m_needProcess = true; }
    void baseOverride(const VBaseOverride& flag) { m_baseOverride = flag; }
    VBaseOverride baseOverride() const { return m_baseOverride; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    bool isPure() override;
    const char* broken() const override;
    void propagateAttrFrom(const AstNodeFTask* fromp) {
        // Creating a wrapper with e.g. cloneType(); preserve some attributes
        classMethod(fromp->classMethod());
        isHideLocal(fromp->isHideLocal());
        isHideProtected(fromp->isHideProtected());
        isVirtual(fromp->isVirtual());
        isStatic(fromp->isStatic());
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
    string m_name;  ///< Filename
public:
    AstNodeFile(VNType t, FileLine* fl, const string& name)
        : AstNode{t, fl}
        , m_name{name} {}
    ASTGEN_MEMBERS_AstNodeFile;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstNodeGen VL_NOT_FINAL : public AstNode {
    // Generate construct
public:
    AstNodeGen(VNType t, FileLine* fl)
        : AstNode{t, fl} {}
    ASTGEN_MEMBERS_AstNodeGen;
};
class AstNodeModule VL_NOT_FINAL : public AstNode {
    // A module, package, program or interface declaration;
    // something that can live directly under the TOP,
    // excluding $unit package stuff
    // @astgen op1 := inlinesp : List[AstNode]
    // @astgen op2 := stmtsp : List[AstNode]
    string m_name;  // Name of the module
    const string m_origName;  // Name of the module, ignoring name() changes, for dot lookup
    string m_someInstanceName;  // Hierarchical name of some arbitrary instance of this module.
                                // Used for user messages only.
    string m_libname;  // Work library
    int m_depth = 0;  // 1=top module, 2=cell off top, shared things low, for -depth options
    int m_level = 0;  // 1=top module, 2=cell off top, shared things have high number
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
    bool m_hierParams : 1;  // Block containing params for parameterized hier blocks
    bool m_internal : 1;  // Internally created
    bool m_recursive : 1;  // Recursive module
    bool m_recursiveClone : 1;  // If recursive, what module it clones, otherwise nullptr
protected:
    AstNodeModule(VNType t, FileLine* fl, const string& name, const string& libname)
        : AstNode{t, fl}
        , m_name{name}
        , m_origName{name}
        , m_libname{libname}
        , m_modPublic{false}
        , m_modTrace{false}
        , m_inLibrary{false}
        , m_dead{false}
        , m_hasGParam{false}
        , m_hasParameterList{false}
        , m_hierBlock{false}
        , m_hierParams{false}
        , m_internal{false}
        , m_recursive{false}
        , m_recursiveClone{false} {}

public:
    ASTGEN_MEMBERS_AstNodeModule;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    string name() const override VL_MT_STABLE { return m_name; }
    virtual bool timescaleMatters() const = 0;
    // ACCESSORS
    void name(const string& name) override { m_name = name; }
    string origName() const override { return m_origName; }
    string someInstanceName() const VL_MT_SAFE { return m_someInstanceName; }
    void someInstanceName(const string& name) { m_someInstanceName = name; }
    bool inLibrary() const { return m_inLibrary; }
    void inLibrary(bool flag) { m_inLibrary = flag; }
    void depth(int value) { m_depth = value; }
    int depth() const VL_MT_SAFE { return m_depth; }
    void level(int value) { m_level = value; }
    int level() const VL_MT_SAFE { return m_level; }
    string libname() const { return m_libname; }
    bool isTop() const VL_MT_SAFE { return level() == 1; }
    bool modPublic() const { return m_modPublic; }
    void modPublic(bool flag) { m_modPublic = flag; }
    bool modTrace() const { return m_modTrace; }
    void modTrace(bool flag) { m_modTrace = flag; }
    bool dead() const { return m_dead; }
    void dead(bool flag) { m_dead = flag; }
    bool hasGParam() const { return m_hasGParam; }
    void hasGParam(bool flag) { m_hasGParam = flag; }
    bool hasParameterList() const { return m_hasParameterList; }
    void hasParameterList(bool flag) { m_hasParameterList = flag; }
    bool hierBlock() const { return m_hierBlock; }
    void hierBlock(bool flag) { m_hierBlock = flag; }
    bool hierParams() const { return m_hierParams; }
    void hierParams(bool flag) { m_hierParams = flag; }
    bool internal() const { return m_internal; }
    void internal(bool flag) { m_internal = flag; }
    bool recursive() const { return m_recursive; }
    void recursive(bool flag) { m_recursive = flag; }
    void recursiveClone(bool flag) { m_recursiveClone = flag; }
    bool recursiveClone() const { return m_recursiveClone; }
    VLifetime lifetime() const { return m_lifetime; }
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VTimescale timeunit() const { return m_timeunit; }
    void timeunit(const VTimescale& flag) { m_timeunit = flag; }
    VOptionBool unconnectedDrive() const { return m_unconnectedDrive; }
    void unconnectedDrive(const VOptionBool flag) { m_unconnectedDrive = flag; }
};
class AstNodeProcedure VL_NOT_FINAL : public AstNode {
    // IEEE procedure: initial, final, always
    // @astgen op2 := stmtsp : List[AstNode] // Note: op1 is used in some sub-types only
    bool m_suspendable : 1;  // Is suspendable by a Delay, EventControl, etc.
    bool m_needProcess : 1;  // Uses VlProcess
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
    void dumpJson(std::ostream& str) const override;
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
    void dumpJson(std::ostream& str) const override;
};

// === Concrete node types =====================================================

// === AstNode ===
class AstActive final : public AstNode {
    // Block of code with sensitivity activation
    // Parents:  MODULE | CFUNC
    // @astgen op1 := senTreeStorep : Optional[AstSenTree] // Moved into m_sensesp in V3Active
    // @astgen op2 := stmtsp : List[AstNode] // Logic
    //
    // @astgen ptr := m_sentreep : Optional[AstSenTree]  // Sensitivity list for this process
    string m_name;

public:
    AstActive(FileLine* fl, const string& name, AstSenTree* sentreep)
        : ASTGEN_SUPER_Active(fl)
        , m_name{name}
        , m_sentreep{sentreep} {
        UASSERT(sentreep, "Sentreep required arg");
    }
    ASTGEN_MEMBERS_AstActive;
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    // Statements are broken into pieces, as some must come before others.
    void sentreep(AstSenTree* nodep) { m_sentreep = nodep; }
    AstSenTree* sentreep() const { return m_sentreep; }
    // METHODS
    inline bool hasClocked() const;
    inline bool hasCombo() const;
};
class AstAlias final : public AstNode {
    // Alias construct - Used for source level net alias, and also for variable aliases internally
    // @astgen op1 := itemsp : List[AstNodeExpr]  // Alias operands
public:
    AstAlias(FileLine* fl, AstNodeExpr* itemsp)
        : ASTGEN_SUPER_Alias(fl) {
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstAlias;
};
class AstAliasScope final : public AstNode {
    // Like AstAlias, but aliases two scopes instead of nets/variables
    // @astgen op1 := rhsp : AstNodeExpr
    // @astgen op2 := lhsp : AstNodeExpr
public:
    AstAliasScope(FileLine* fl, AstNodeExpr* lhsp, AstNodeExpr* rhsp)
        : ASTGEN_SUPER_AliasScope(fl) {
        this->lhsp(lhsp);
        this->rhsp(rhsp);
    }
    ASTGEN_MEMBERS_AstAliasScope;
};
class AstBind final : public AstNode {
    // Parents: MODULE
    // Children: CELL
    // @astgen op1 := cellsp : List[AstNode]
    string m_name;  // Binding to name
public:
    AstBind(FileLine* fl, const string& name, AstNode* cellsp)
        : ASTGEN_SUPER_Bind(fl)
        , m_name{name} {
        UASSERT_OBJ(VN_IS(cellsp, Cell), cellsp, "Only instances allowed to be bound");
        addCellsp(cellsp);
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
    // @astgen op1 := argsp : List[AstVar]  // Argument (and return value) variables
    // @astgen op2 := varsp : List[AstVar]  // Local variables
    // @astgen op3 := stmtsp : List[AstNode]
    //
    // @astgen ptr := m_scopep : Optional[AstScope]  // Scope that function is under
    string m_name;
    string m_cname;  // C name, for dpiExports
    string m_rtnType;  // void, bool, or other return type
    string m_argTypes;  // Argument types
    string m_ifdef;  // #ifdef symbol around this function
    VBoolOrUnknown m_isConst;  // Function is declared const (*this not changed)
    bool m_isStatic : 1;  // Function is static (no need for a 'this' pointer)
    bool m_isTrace : 1;  // Function is related to tracing
    bool m_dontCombine : 1;  // V3Combine shouldn't compare this func tree, it's special
    bool m_declPrivate : 1;  // Declare it private
    bool m_keepIfEmpty : 1;  // Keep declaration and definition separate, even if empty
    bool m_slow : 1;  // Slow routine, called once or just at init time
    bool m_funcPublic : 1;  // From user public task/function
    bool m_isConstructor : 1;  // Is C class constructor
    bool m_isDestructor : 1;  // Is C class destructor
    bool m_isMethod : 1;  // Is inside a class definition
    bool m_isLoose : 1;  // Semantically this is a method, but is implemented as a function with
                         // an explicitly passed 'self' pointer as the first argument.  This can
                         // be slightly faster due to __restrict, and we do not declare in header
                         // so adding/removing loose functions doesn't recompile everything.
    bool m_isVirtual : 1;  // Virtual function
    bool m_entryPoint : 1;  // User may call into this top level function
    bool m_dpiPure : 1;  // Pure DPI function
    bool m_dpiContext : 1;  // Declared as 'context' DPI import/export function
    bool m_dpiExportDispatcher : 1;  // This is the DPI export entry point (i.e.: called by user)
    bool m_dpiExportImpl : 1;  // DPI export implementation (called from DPI dispatcher via lookup)
    bool m_dpiImportPrototype : 1;  // This is the DPI import prototype (i.e.: provided by user)
    bool m_dpiImportWrapper : 1;  // Wrapper for invoking DPI import prototype from generated code
    bool m_needProcess : 1;  // Needs access to VlProcess of the caller
    bool m_recursive : 1;  // Recursive or part of recursion
    int m_cost;  // Function call cost
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
        m_keepIfEmpty = false;
        m_slow = false;
        m_funcPublic = false;
        m_isConstructor = false;
        m_isDestructor = false;
        m_isMethod = true;
        m_isLoose = false;
        m_isVirtual = false;
        m_needProcess = false;
        m_entryPoint = false;
        m_dpiPure = false;
        m_dpiContext = false;
        m_dpiExportDispatcher = false;
        m_dpiExportImpl = false;
        m_dpiImportPrototype = false;
        m_dpiImportWrapper = false;
        m_recursive = false;
        m_cost = v3Global.opt.instrCountDpi();  // As proxy for unknown general DPI cost
    }
    ASTGEN_MEMBERS_AstCFunc;
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    bool sameNode(const AstNode* samep) const override {
        const AstCFunc* const asamep = VN_DBG_AS(samep, CFunc);
        return ((isTrace() == asamep->isTrace()) && (rtnTypeVoid() == asamep->rtnTypeVoid())
                && (argTypes() == asamep->argTypes()) && isLoose() == asamep->isLoose()
                && (!(dpiImportPrototype() || dpiExportImpl()) || name() == asamep->name()));
    }
    //
    void name(const string& name) override { m_name = name; }
    int instrCount() const override { return m_cost; }
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
    bool declPrivate() const { return m_declPrivate; }
    void declPrivate(bool flag) { m_declPrivate = flag; }
    bool keepIfEmpty() const VL_MT_SAFE { return m_keepIfEmpty; }
    void keepIfEmpty(bool flag) { m_keepIfEmpty = flag; }
    bool slow() const VL_MT_SAFE { return m_slow; }
    void slow(bool flag) { m_slow = flag; }
    bool funcPublic() const { return m_funcPublic; }
    void funcPublic(bool flag) { m_funcPublic = flag; }
    void argTypes(const string& str) { m_argTypes = str; }
    string argTypes() const { return m_argTypes; }
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
    bool isCoroutine() const { return m_rtnType == "VlCoroutine"; }
    void recursive(bool flag) { m_recursive = flag; }
    bool recursive() const { return m_recursive; }
    void cost(int cost) { m_cost = cost; }
    // Special methods
    bool emptyBody() const {
        return !keepIfEmpty() && !argsp() && !varsp() && !stmtsp() && !isVirtual()
               && !dpiImportPrototype();
    }
};
class AstCLocalScope final : public AstNode {
    // Pack statements into an unnamed scope when generating C++
    // @astgen op1 := stmtsp : List[AstNode]
public:
    AstCLocalScope(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_CLocalScope(fl) {
        addStmtsp(stmtsp);
    }
    ASTGEN_MEMBERS_AstCLocalScope;
};
class AstCUse final : public AstNode {
    // C++ use of a class or #include; indicates need of forward declaration
    // Parents:  NODEMODULE
    const string m_name;
    const VUseType m_useType;  // What sort of use this is

public:
    AstCUse(FileLine* fl, VUseType useType, const string& name)
        : ASTGEN_SUPER_CUse(fl)
        , m_name{name}
        , m_useType{useType} {}
    ASTGEN_MEMBERS_AstCUse;
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    VUseType useType() const { return m_useType; }
};
class AstCell final : public AstNode {
    // A instantiation cell or interface call (don't know which until link)
    // @astgen op1 := pinsp : List[AstPin] // List of port assignments
    // @astgen op2 := paramsp : List[AstPin] // List of parameter assignments
    // @astgen op3 := rangep : Optional[AstRange] // Range for arrayed instances
    // @astgen op4 := intfRefsp : List[AstIntfRef] // List of interface references, for tracing
    //
    // @astgen ptr := m_modp : Optional[AstNodeModule]  // [AfterLink] Pointer to module instanced
    FileLine* m_modNameFileline;  // Where module the cell instances token was
    string m_name;  // Cell name
    string m_origName;  // Original name before dot addition
    string m_modName;  // Module the cell instances
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
        addPinsp(pinsp);
        addParamsp(paramsp);
        this->rangep(rangep);
    }
    ASTGEN_MEMBERS_AstCell;
    // No cloneRelink, we presume cloneee's want the same module linkages
    void cloneRelink() override {}  // TODO V3Param shouldn't require avoiding cloneRelinkGen
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
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
    // @astgen ptr := m_scopep : Optional[AstScope]  // The scope that the cell is inlined into
    string m_name;  // Cell name, possibly {a}__DOT__{b}...
    const string m_origModName;  // Original name of module, ignoring name() changes, for LinkDot
public:
    AstCellInline(FileLine* fl, const string& name, const string& origModName)
        : ASTGEN_SUPER_CellInline(fl)
        , m_name{name}
        , m_origModName{origModName} {}
    ASTGEN_MEMBERS_AstCellInline;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_name; }  // * = Cell name
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    string origModName() const { return m_origModName; }  // * = modp()->origName() before inlining
    void name(const string& name) override { m_name = name; }
};
class AstCellInlineScope final : public AstNode {
    // A particular scoped usage of a Cell Inline
    // Parents: Scope
    // Children: none
    //
    // @astgen ptr := m_scopep : Optional[AstScope]  // Scope variable is underneath
    // @astgen ptr := m_cellp : Optional[AstCellInline]  // Cell ref
    const string m_origModName;  // Original name of module, ignoring name() changes, for LinkDot
public:
    AstCellInlineScope(FileLine* fl, AstScope* scopep, AstCellInline* cellp)
        : ASTGEN_SUPER_CellInlineScope(fl)
        , m_scopep{scopep}
        , m_cellp{cellp} {
        UASSERT_OBJ(scopep, fl, "Scope must be non-null");
        UASSERT_OBJ(cellp, fl, "CellInline must be non-null");
    }
    ASTGEN_MEMBERS_AstCellInlineScope;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    // ACCESSORS
    string name() const override VL_MT_STABLE { return m_cellp->name(); }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    AstScope* scopep() const VL_MT_STABLE { return m_scopep; }  // Pointer to scope it's under
    string origModName() const {
        return m_cellp->origModName();
    }  // * = modp()->origName() before inlining
};
class AstCgOptionAssign final : public AstNode {
    // A covergroup set of option
    // Parents: CLASS(covergroup) or cross
    string m_name;  // Option name
    const bool m_typeOption;  // type_option vs option
    // @astgen op1 := valuep : AstNodeExpr
public:
    AstCgOptionAssign(FileLine* fl, bool typeOption, const string& name, AstNodeExpr* valuep)
        : ASTGEN_SUPER_CgOptionAssign(fl)
        , m_name{name}
        , m_typeOption{typeOption} {
        this->valuep(valuep);
    }
    ASTGEN_MEMBERS_AstCgOptionAssign;
    // ACCESSORS
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Bind Target name
    bool typeOption() const { return m_typeOption; }
};
class AstClassExtends final : public AstNode {
    // class extends class name, or class implements class name
    // Children: List of AstParseRef for packages/classes
    // during early parse, then moves to dtype
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := classOrPkgsp : Optional[AstNode]
    // @astgen op3 := argsp : List[AstNodeExpr]
    const bool m_isImplements;  // class implements
    bool m_parameterized = false;  // has parameters in its statement

public:
    AstClassExtends(FileLine* fl, AstNode* classOrPkgsp, bool isImplements)
        : ASTGEN_SUPER_ClassExtends(fl)
        , m_isImplements{isImplements} {
        this->classOrPkgsp(classOrPkgsp);  // Only for parser
    }
    ASTGEN_MEMBERS_AstClassExtends;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool hasDType() const override VL_MT_SAFE { return true; }
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
    // @astgen op2 := itemsp : List[AstNode]
    // @astgen op3 := eventp : Optional[AstVar]
    std::string m_name;  // Clocking block name
    const bool m_isDefault;  // True if default clocking
    const bool m_isGlobal;  // True if global clocking

public:
    AstClocking(FileLine* fl, const std::string& name, AstSenItem* sensesp, AstNode* itemsp,
                bool isDefault, bool isGlobal)
        : ASTGEN_SUPER_Clocking(fl)
        , m_name{name}
        , m_isDefault{isDefault}
        , m_isGlobal{isGlobal} {
        this->sensesp(sensesp);
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstClocking;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    bool isDefault() const { return m_isDefault; }
    bool isGlobal() const { return m_isGlobal; }
    AstVar* ensureEventp(bool childDType = false);
};
class AstClockingItem final : public AstNode {
    // Parents:  CLOCKING
    // Children: EXPRs, ASSIGNs, VARs
    // @astgen op1 := skewp : Optional[AstNodeExpr]
    // @astgen op2 := exprp : Optional[AstNodeExpr]
    // @astgen op3 := assignp : Optional[AstAssign]
    // @astgen op4 := varp : Optional[AstVar]
    // @astgen ptr := m_outputp : Optional[AstClockingItem]
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
    AstClockingItem* outputp() const { return m_outputp; }
    void outputp(AstClockingItem* outputp) { m_outputp = outputp; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
};
class AstConfig final : public AstNode {
    // Parents: NETLIST
    // @astgen op1 := designp : List[AstConfigCell]
    // @astgen op2 := itemsp : List[AstNode]
    std::string m_libname;  // Config library, or ""
    std::string m_configname;  // Config name within library

public:
    AstConfig(FileLine* fl, const std::string& libname, const std::string& cellname)
        : ASTGEN_SUPER_Config(fl)
        , m_libname{libname}
        , m_configname{cellname} {}
    ASTGEN_MEMBERS_AstConfig;
    std::string name() const override VL_MT_STABLE { return m_libname + "." + m_configname; }
    std::string libname() const VL_MT_STABLE { return m_libname; }
    std::string configname() const VL_MT_STABLE { return m_configname; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};
class AstConfigCell final : public AstNode {
    // Parents: CONFIGRULE
    std::string m_libname;  // Cell library, or ""
    std::string m_cellname;  // Cell name within library

public:
    AstConfigCell(FileLine* fl, const std::string& libname, const std::string& cellname)
        : ASTGEN_SUPER_ConfigCell(fl)
        , m_libname{libname}
        , m_cellname{cellname} {}
    ASTGEN_MEMBERS_AstConfigCell;
    std::string name() const override VL_MT_STABLE { return m_libname + "." + m_cellname; }
    std::string libname() const VL_MT_STABLE { return m_libname; }
    std::string cellname() const VL_MT_STABLE { return m_cellname; }
};
class AstConfigRule final : public AstNode {
    // Parents: CONFIG
    // @astgen op1 := cellp : Optional[AstNode]  // Cells to apply to, or nullptr=default
    // @astgen op2 := usep : List[AstNode]  // Use or design to apply
    const bool m_isCell;  // Declared as "cell" versus "instance"

public:
    AstConfigRule(FileLine* fl, AstNode* cellp, AstNode* usep, bool isCell)
        : ASTGEN_SUPER_ConfigRule(fl)
        , m_isCell{isCell} {
        this->cellp(cellp);
        addUsep(usep);
    }
    ASTGEN_MEMBERS_AstConfigRule;
    bool isCell() const VL_MT_STABLE { return m_isCell; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};
class AstConfigUse final : public AstNode {
    // Parents: CONFIGRULE
    // @astgen op1 := paramsp : List[AstPin]
    std::string m_libname;  // Use library, or ""
    std::string m_cellname;  // Use name within library
    const bool m_isConfig;  // ":config"; Config, not module/primitive name

public:
    AstConfigUse(FileLine* fl, const std::string& libname, const std::string& cellname,
                 AstPin* paramsp, bool isConfig)
        : ASTGEN_SUPER_ConfigUse(fl)
        , m_libname{libname}
        , m_cellname{cellname}
        , m_isConfig{isConfig} {
        addParamsp(paramsp);
    }
    ASTGEN_MEMBERS_AstConfigUse;
    std::string name() const override VL_MT_STABLE { return m_libname + "." + m_cellname; }
    std::string libname() const VL_MT_STABLE { return m_libname; }
    std::string cellname() const VL_MT_STABLE { return m_cellname; }
    bool isConfig() const VL_MT_STABLE { return m_isConfig; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};
class AstConstPool final : public AstNode {
    // Container for const static data
    // @astgen op1 := modulep : AstModule // m_modp below TODO: fix this mess
    //
    // @astgen ptr := m_modp : AstModule  // The Module holding the Scope below ...
    // @astgen ptr := m_scopep : AstScope  // Scope holding the constant variables
    std::unordered_multimap<uint32_t, AstVarScope*> m_tables;  // Constant tables (unpacked arrays)
    std::unordered_multimap<uint32_t, AstVarScope*> m_consts;  // Constant tables (scalars)

    AstVarScope* createNewEntry(const string& name, AstNodeExpr* initp);

public:
    explicit AstConstPool(FileLine* fl);
    ASTGEN_MEMBERS_AstConstPool;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void cloneRelink() override { V3ERROR_NA; }  // Not cloneable
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
class AstConstraint final : public AstNode {
    // Constraint
    // @astgen op1 := itemsp : List[AstNode]
    // @astgen op2 := classOrPackagep : Optional[AstNode]
    string m_name;  // Name of constraint
    VBaseOverride m_baseOverride;  // BaseOverride (inital/final/extends)
    bool m_isExternDef = false;  // Extern prototype definition
    bool m_isExternExplicit = false;  // Explicit prototype declaration (has extern)
    bool m_isExternProto = false;  // Prototype declaration (implicit or explicit)
    bool m_isKwdPure = false;  // Pure constraint
    bool m_isStatic = false;  // Static constraint
public:
    AstConstraint(FileLine* fl, const string& name, AstNode* itemsp)
        : ASTGEN_SUPER_Constraint(fl)
        , m_name{name} {
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstConstraint;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Scope name
    void name(const string& name) override { m_name = name; }  // * = Scope name
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    void baseOverride(const VBaseOverride& flag) { m_baseOverride = flag; }
    VBaseOverride baseOverride() const { return m_baseOverride; }
    bool isExternDef() const { return m_isExternDef; }
    void isExternDef(bool flag) { m_isExternDef = flag; }
    void isExternExplicit(bool flag) { m_isExternExplicit = flag; }
    bool isExternExplicit() const { return m_isExternExplicit; }
    void isExternProto(bool flag) { m_isExternProto = flag; }
    bool isExternProto() const { return m_isExternProto; }
    void isKwdPure(bool flag) { m_isKwdPure = flag; }
    bool isKwdPure() const { return m_isKwdPure; }
    void isStatic(bool flag) { m_isStatic = flag; }
    bool isStatic() const { return m_isStatic; }
};
class AstConstraintBefore final : public AstNode {
    // Constraint solve before item
    // @astgen op1 := lhssp : List[AstNodeExpr]
    // @astgen op2 := rhssp : List[AstNodeExpr]
public:
    AstConstraintBefore(FileLine* fl, AstNodeExpr* lhssp, AstNodeExpr* rhssp)
        : ASTGEN_SUPER_ConstraintBefore(fl) {
        addLhssp(lhssp);
        addRhssp(rhssp);
    }
    ASTGEN_MEMBERS_AstConstraintBefore;
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
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
    bool sameNode(const AstNode*) const override { return true; }
    string path() const { return m_path; }
};
class AstDefaultDisable final : public AstNode {
    // @astgen op1 := condp : AstNodeExpr

public:
    AstDefaultDisable(FileLine* fl, AstNodeExpr* condp)
        : ASTGEN_SUPER_DefaultDisable(fl) {
        this->condp(condp);
    }
    ASTGEN_MEMBERS_AstDefaultDisable;
};
class AstDpiExport final : public AstNode {
    // We could put an AstNodeFTaskRef instead of the verilog function name,
    // however we're not *calling* it, so that seems somehow wrong.
    // (Probably AstNodeFTaskRef should be renamed AstNodeFTaskCall and have-a AstNodeFTaskRef)
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
    VDisplayType m_displayType;

public:
    inline AstElabDisplay(FileLine* fl, VDisplayType dispType, AstNodeExpr* exprsp);
    ASTGEN_MEMBERS_AstElabDisplay;
    const char* broken() const override {
        BROKEN_RTN(!fmtp());
        return nullptr;
    }
    string verilogKwd() const override { return "$"s + string{displayType().ascii()}; }
    bool isGateOptimizable() const override { return false; }
    bool isPredictOptimizable() const override { return false; }
    bool isPure() override { return false; }  // SPECIAL: $display has 'visual' ordering
    bool isOutputter() override { return true; }  // SPECIAL: $display makes output
    bool isUnlikely() const override { return true; }
    bool sameNode(const AstNode* samep) const override {
        return displayType() == VN_DBG_AS(samep, ElabDisplay)->displayType();
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
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstGenCaseItem final : public AstNode {
    // Single item of an AstGenCase
    // @astgen op1 := condsp : List[AstNodeExpr]
    // @astgen op2 := itemsp : List[AstNode]
public:
    AstGenCaseItem(FileLine* fl, AstNodeExpr* condsp, AstNode* itemsp)
        : ASTGEN_SUPER_GenCaseItem(fl) {
        addCondsp(condsp);
        addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstGenCaseItem;
    bool isDefault() const { return condsp() == nullptr; }
};
class AstImplicit final : public AstNode {
    // Create implicit wires and do nothing else, for gates that are ignored
    // Parents: MODULE
    // @astgen op1 := exprsp : List[AstNode]
public:
    AstImplicit(FileLine* fl, AstNode* exprsp)
        : ASTGEN_SUPER_Implicit(fl) {
        addExprsp(exprsp);
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
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool hasDType() const override VL_MT_SAFE { return false; }  // See valuep()'s dtype instead
};
class AstIntfRef final : public AstNode {
    // An interface reference
    string m_name;  // Name of the reference
public:
    AstIntfRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER_IntfRef(fl)
        , m_name{name} {}
    string name() const override VL_MT_STABLE { return m_name; }
    ASTGEN_MEMBERS_AstIntfRef;
};
class AstLibrary final : public AstNode {
    // Parents: NETLIST
    // Library declaration from lib.map file
    // @astgen op1 := filesp : List[AstNodeExpr]
    // @astgen op2 := incdirsp : List[AstNodeExpr]
    std::string m_name;  // Library name

public:
    AstLibrary(FileLine* fl, const std::string& name, AstNodeExpr* filesp, AstNodeExpr* incdirsp)
        : ASTGEN_SUPER_Library(fl)
        , m_name{name} {
        addFilesp(filesp);
        addIncdirsp(incdirsp);
    }
    ASTGEN_MEMBERS_AstLibrary;
    std::string name() const override VL_MT_STABLE { return m_name; }
};
class AstModport final : public AstNode {
    // A modport in an interface
    // @astgen op1 := varsp : List[AstNode]
    string m_name;  // Name of the modport
public:
    AstModport(FileLine* fl, const string& name, AstNode* varsp)
        : ASTGEN_SUPER_Modport(fl)
        , m_name{name} {
        addVarsp(varsp);
    }
    string verilogKwd() const override { return "modport"; }
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    ASTGEN_MEMBERS_AstModport;
};
class AstModportClockingRef final : public AstNode {
    // A clocking block referenced under a modport
    // The storage for the clocking block itself is inside the interface, thus this is a reference
    // PARENT: AstModport
    //
    // @astgen ptr := m_clockingp : Optional[AstClocking]  // Link to the actual clocking block
    string m_name;  // Name of the clocking block referenced
public:
    AstModportClockingRef(FileLine* fl, const string& name)
        : ASTGEN_SUPER_ModportClockingRef(fl)
        , m_name{name} {}
    ASTGEN_MEMBERS_AstModportClockingRef;
    void dump(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    AstClocking* clockingp() const VL_MT_STABLE {
        return m_clockingp;
    }  // [After Link] Pointer to clocking block
    void clockingp(AstClocking* clockingp) { m_clockingp = clockingp; }
};
class AstModportFTaskRef final : public AstNode {
    // An import/export referenced under a modport
    // The storage for the function itself is inside the
    // interface/instantiator, thus this is a reference
    // PARENT: AstModport
    //
    // @astgen ptr := m_ftaskp : Optional[AstNodeFTask]  // Link to the function
    string m_name;  // Name of the variable referenced
    bool m_export;  // Type of the function (import/export)
public:
    AstModportFTaskRef(FileLine* fl, const string& name, bool isExport)
        : ASTGEN_SUPER_ModportFTaskRef(fl)
        , m_name{name}
        , m_export{isExport} {}
    ASTGEN_MEMBERS_AstModportFTaskRef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
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
    // @astgen op1 := exprp : Optional[AstNodeExpr]
    //
    // @astgen ptr := m_varp : Optional[AstVar]  // Link to the actual Var
    string m_name;  // Name of the variable referenced
    const VDirection m_direction;  // Direction of the variable (in/out)
public:
    AstModportVarRef(FileLine* fl, const string& name, VDirection::en direction)
        : ASTGEN_SUPER_ModportVarRef(fl)
        , m_name{name}
        , m_direction{direction} {}
    AstModportVarRef(FileLine* fl, const string& name, AstNodeExpr* exprp,
                     VDirection::en direction)
        : ASTGEN_SUPER_ModportVarRef(fl)
        , m_name{name}
        , m_direction{direction} {
        this->exprp(exprp);
    };
    ASTGEN_MEMBERS_AstModportVarRef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    VDirection direction() const { return m_direction; }
    AstVar* varp() const VL_MT_STABLE { return m_varp; }  // [After Link] Pointer to variable
    void varp(AstVar* varp) { m_varp = varp; }
};
class AstNetlist final : public AstNode {
    // All modules are under this single top node.
    // Parents:   none
    // Children:  MODULEs & CFILEs
    // @astgen op1 := modulesp : List[AstNodeModule]
    // @astgen op2 := filesp : List[AstNodeFile]
    // @astgen op3 := miscsp : List[AstNode]
    //
    // @astgen ptr := m_typeTablep : AstTypeTable  // Reference to type table, for faster lookup
    // @astgen ptr := m_constPoolp : AstConstPool  // Reference to constant pool, for faster lookup
    // @astgen ptr := m_dollarUnitPkgp : Optional[AstPackage]  // $unit
    // @astgen ptr := m_stdPackagep : Optional[AstPackage]  // SystemVerilog std package
    // @astgen ptr := m_evalp : Optional[AstCFunc]  // The '_eval' function
    // @astgen ptr := m_evalNbap : Optional[AstCFunc]  // The '_eval__nba' function
    // @astgen ptr := m_dpiExportTriggerp : Optional[AstVarScope]  // DPI export trigger variable
    // @astgen ptr := m_delaySchedulerp : Optional[AstVar]  // Delay scheduler variable
    // @astgen ptr := m_nbaEventp : Optional[AstVarScope]  // NBA event variable
    // @astgen ptr := m_nbaEventTriggerp : Optional[AstVarScope]  // NBA event trigger
    // @astgen ptr := m_topScopep : Optional[AstTopScope]  // Singleton AstTopScope
    VTimescale m_timeunit;  // Global time unit
    VTimescale m_timeprecision;  // Global time precision
    bool m_timescaleSpecified = false;  // Input HDL specified timescale
public:
    AstNetlist();
    ASTGEN_MEMBERS_AstNetlist;
    void deleteContents();
    void cloneRelink() override { V3ERROR_NA; }  // Not cloneable
    string name() const override VL_MT_STABLE { return "$root"; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
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
    AstVarScope* nbaEventp() const { return m_nbaEventp; }
    void nbaEventp(AstVarScope* const varScopep) { m_nbaEventp = varScopep; }
    AstVarScope* nbaEventTriggerp() const { return m_nbaEventTriggerp; }
    void nbaEventTriggerp(AstVarScope* const varScopep) { m_nbaEventTriggerp = varScopep; }
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
};
class AstPackageExport final : public AstNode {
    // A package export declaration
    //
    // @astgen ptr := m_packagep : Optional[AstPackage]  // Package hierarchy
    string m_name;  // What imported e.g. "*"
    string m_pkgName;  // Module the cell instances

public:
    AstPackageExport(FileLine* fl, const string& pkgName, const string& name)
        : ASTGEN_SUPER_PackageExport(fl)
        , m_name{name}
        , m_pkgName{pkgName}
        , m_packagep{nullptr} {}
    ASTGEN_MEMBERS_AstPackageExport;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    string pkgName() const VL_MT_STABLE { return m_pkgName; }
    string prettyPkgNameQ() const { return "'" + prettyName(pkgName()) + "'"; }
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
    // A package import declaration
    // @astgen op1 := resolvedClassp : Optional[AstClassOrPackageRef]
    //
    // @astgen ptr := m_packagep : Optional[AstPackage]  // Package hierarchy
    string m_name;  // What imported e.g. "*"
    string m_pkgName;  // Module the cell instances

public:
    AstPackageImport(FileLine* fl, AstPackage* packagep, const string& name)
        : ASTGEN_SUPER_PackageImport(fl)
        , m_name{name}
        , m_packagep{packagep} {
        pkgNameFrom();
    }
    AstPackageImport(FileLine* fl, const string& pkgName, const string& name)
        : ASTGEN_SUPER_PackageImport(fl)
        , m_name{name}
        , m_pkgName{pkgName}
        , m_packagep{nullptr} {}
    ASTGEN_MEMBERS_AstPackageImport;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    string name() const override VL_MT_STABLE { return m_name; }
    string pkgName() const VL_MT_STABLE { return m_pkgName; }
    string prettyPkgNameQ() const { return "'" + prettyName(pkgName()) + "'"; }
    AstPackage* packagep() const { return m_packagep; }
    void packagep(AstPackage* nodep) { m_packagep = nodep; }

private:
    void pkgNameFrom();
};
class AstPin final : public AstNode {
    // A port or parameter assignment on an instantiation
    // @astgen op1 := exprp : Optional[AstNode<AstNodeExpr|AstNodeDType>]  // nullptr=unconnected
    //
    // @astgen ptr := m_modVarp : Optional[AstVar]  // Input/output connects to on submodule
    // @astgen ptr := m_modPTypep : Optional[AstParamTypeDType]  // Param type connects to on sub
    int m_pinNum;  // Pin number
    string m_name;  // Pin name, or "" for number based interconnect
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
    ASTGEN_MEMBERS_AstPin;
    void cloneRelink() override {}  // TODO V3Param shouldn't require avoiding cloneRelinkGen
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
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
    const VTimescale m_timescale;  // For TIMEUNIT_SET
public:
    // Pragmas don't result in any output code, they're just flags that affect
    // other processing in verilator.
    AstPragma(FileLine* fl, VPragmaType pragType)
        : ASTGEN_SUPER_Pragma(fl)
        , m_pragType{pragType} {
        UASSERT_OBJ(pragType != VPragmaType::TIMEUNIT_SET, fl, "Should use other constructor");
    }
    AstPragma(FileLine* fl, const VTimescale& timescale)
        : ASTGEN_SUPER_Pragma(fl)
        , m_pragType{VPragmaType::TIMEUNIT_SET}
        , m_timescale{timescale} {}
    ASTGEN_MEMBERS_AstPragma;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    VPragmaType pragType() const { return m_pragType; }  // *=type of the pragma
    bool isPredictOptimizable() const override { return false; }
    bool sameNode(const AstNode* samep) const override {
        return pragType() == VN_DBG_AS(samep, Pragma)->pragType();
    }
    VTimescale timescale() const { return m_timescale; }
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
    bool hasDType() const override VL_MT_SAFE {
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
    bool sameNode(const AstNode* samep) const override {
        return direction() == VN_DBG_AS(samep, Pull)->direction();
    }
    uint32_t direction() const { return (uint32_t)m_direction; }
};
class AstScope final : public AstNode {
    // A particular usage of a cell
    // Parents: MODULE
    // Children: NODEBLOCK
    // @astgen op1 := varsp : List[AstVarScope]
    // @astgen op2 := blocksp : List[AstNode] // Logic blocks/AstActive/AstCFunc
    // @astgen op3 := inlinesp : List[AstCellInlineScope] // Cell Inlines
    //
    // Below scope and cell are nullptr if top scope
    // @astgen ptr := m_aboveScopep : Optional[AstScope]  // Scope above this one in the hierarchy
    // @astgen ptr := m_aboveCellp : Optional[AstCell]  // Cell above this in the hierarchy
    // @astgen ptr := m_modp : AstNodeModule  // Module scope corresponds to

    // An AstScope->name() is special: . indicates an uninlined scope, __DOT__ an inlined scope
    string m_name;  // Name
public:
    AstScope(FileLine* fl, AstNodeModule* modp, const string& name, AstScope* aboveScopep,
             AstCell* aboveCellp)
        : ASTGEN_SUPER_Scope(fl)
        , m_name{name}
        , m_aboveScopep{aboveScopep}
        , m_aboveCellp{aboveCellp}
        , m_modp{modp} {}
    ASTGEN_MEMBERS_AstScope;
    const char* broken() const override {
        BROKEN_RTN(!m_modp);
        return nullptr;
    }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    string name() const override VL_MT_STABLE { return m_name; }  // * = Scope name
    void name(const string& name) override { m_name = name; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    string nameDotless() const;
    AstNodeModule* modp() const { return m_modp; }
    //
    AstScope* aboveScopep() const VL_MT_SAFE { return m_aboveScopep; }
    AstCell* aboveCellp() const { return m_aboveCellp; }
    bool isTop() const VL_MT_SAFE { return aboveScopep() == nullptr; }  // At top of hierarchy
    // Create new MODULETEMP variable under this scope
    AstVarScope* createTemp(const string& name, unsigned width);
    AstVarScope* createTemp(const string& name, AstNodeDType* dtypep);
    AstVarScope* createTempLike(const string& name, const AstVarScope* vscp);
};
class AstSenItem final : public AstNode {
    // Parents:  SENTREE
    // @astgen op1 := sensp : Optional[AstNodeExpr] // Sensitivity expression
    // @astgen op2 := condp : Optional[AstNodeExpr] // Sensitivity condition
    VEdgeType m_edgeType;  // Edge type
public:
    class Combo {};  // for constructor type-overload selection
    class Static {};  // for constructor type-overload selection
    class Initial {};  // for constructor type-overload selection
    class Final {};  // for constructor type-overload selection
    class Never {};  // for constructor type-overload selection
    AstSenItem(FileLine* fl, VEdgeType edgeType, AstNodeExpr* senp, AstNodeExpr* condp = nullptr)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{edgeType} {
        this->sensp(senp);
        this->condp(condp);
    }
    AstSenItem(FileLine* fl, Combo)
        : ASTGEN_SUPER_SenItem(fl)
        , m_edgeType{VEdgeType::ET_COMBO} {}
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
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override {
        return edgeType() == VN_DBG_AS(samep, SenItem)->edgeType();
    }
    VEdgeType edgeType() const { return m_edgeType; }
    void edgeType(VEdgeType type) {
        m_edgeType = type;
        editCountInc();
    }
    AstNodeVarRef* varrefp() const { return VN_CAST(sensp(), NodeVarRef); }
    //
    bool isClocked() const { return edgeType().clockedStmt(); }
    bool isComboOrStar() const {
        return edgeType() == VEdgeType::ET_COMBO || edgeType() == VEdgeType::ET_COMBO_STAR;
    }
    bool isComboStar() const { return edgeType() == VEdgeType::ET_COMBO_STAR; }
    bool isHybrid() const { return edgeType() == VEdgeType::ET_HYBRID; }
    bool isStatic() const { return edgeType() == VEdgeType::ET_STATIC; }
    bool isInitial() const { return edgeType() == VEdgeType::ET_INITIAL; }
    bool isFinal() const { return edgeType() == VEdgeType::ET_FINAL; }
    bool isNever() const { return edgeType() == VEdgeType::ET_NEVER; }
};
class AstSenTree final : public AstNode {
    // A sensitivity list
    // @astgen op1 := sensesp : List[AstSenItem]
    bool m_multi = false;  // Created from combo logic by ORing multiple clock domains
public:
    AstSenTree(FileLine* fl, AstSenItem* sensesp)
        : ASTGEN_SUPER_SenTree(fl) {
        addSensesp(sensesp);
    }
    ASTGEN_MEMBERS_AstSenTree;
    bool sameNode(const AstNode* samep) const override {
        const AstSenTree* const asamep = VN_DBG_AS(samep, SenTree);
        return m_multi == asamep->m_multi;
    }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool isMulti() const { return m_multi; }
    void multi(bool flag) { m_multi = true; }
    // METHODS
    bool hasClocked() const;  // Includes a clocked statement
    bool hasEdge() const;  // Includes a posedge/negedge/bothedge clocked statement
    bool hasStatic() const;  // Includes a STATIC SenItem
    bool hasInitial() const;  // Includes a INITIAL SenItem
    bool hasFinal() const;  // Includes a FINAL SenItem
    bool hasCombo() const;  // Includes a COMBO SenItem
    bool hasHybrid() const;  // Includes a HYBRID SenItem
};
class AstStrengthSpec final : public AstNode {
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
    void dumpJson(std::ostream& str) const override;
};
class AstSystemCSection final : public AstNode {
    // Verilator specific "`systemc_* block". This is a "module item"
    // containing arbitrary text that is emitted to the C++ output in various
    // locations depending on the sectionType.
    const VSystemCSectionType m_sectionType;  // The section type
    const std::string m_text;  // The text content

public:
    AstSystemCSection(FileLine* fl, VSystemCSectionType sectionType, const std::string& text)
        : ASTGEN_SUPER_SystemCSection(fl)
        , m_sectionType{sectionType}
        , m_text{text} {
        v3Global.setHasSystemCSections();
    }
    ASTGEN_MEMBERS_AstSystemCSection;
    VSystemCSectionType sectionType() const { return m_sectionType; }
    const std::string& text() const { return m_text; }
    void dump(std::ostream&) const override;
    void dumpJson(std::ostream&) const override;
    bool sameNode(const AstNode*) const override { return false; }
    bool isPure() override { return false; }
    bool isOutputter() override { return true; }
};
class AstText final : public AstNode {
    // Represents a piece of text to be emitted into the output
    //
    // Avoid using this directly, internally usually want
    // AstCStmt::add("text") or AstCExpr::add("text") instead
    //
    const std::string m_text;  // The text to emit
public:
    AstText(FileLine* fl, const std::string& text)
        : ASTGEN_SUPER_Text(fl)
        , m_text{text} {}
    ASTGEN_MEMBERS_AstText;
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    bool sameNode(const AstNode* samep) const override {
        return text() == VN_DBG_AS(samep, Text)->text();
    }
    const std::string& text() const VL_MT_SAFE { return m_text; }
};
class AstTextBlock final : public AstNode {
    // Text block emitted into output, with some arbitrary nodes interspersed
    // @astgen op1 := nodesp : List[AstNode] // Nodes to print
    const std::string m_prefix;  // Prefix to print before first element in 'nodesp'
    const std::string m_separator;  // Separator to print between each element in 'nodesp'
    const std::string m_suffix;  // Suffix to pring after last element in 'nodesp'
public:
    explicit AstTextBlock(FileLine* fl,  //
                          const std::string& prefix = "",  //
                          const std::string& separator = "",  //
                          const std::string& suffix = "")
        : ASTGEN_SUPER_TextBlock(fl)
        , m_prefix{prefix}
        , m_separator{separator}
        , m_suffix{suffix} {}
    ASTGEN_MEMBERS_AstTextBlock;
    const std::string& prefix() const { return m_prefix; }
    const std::string& separator() const { return m_separator; }
    const std::string& suffix() const { return m_suffix; }
    // Add some text, or a node to this block
    void add(const string& text) { addNodesp(new AstText{fileline(), text}); }
    void add(AstNode* nodep) { addNodesp(nodep); }
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
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
};
class AstTypeTable final : public AstNode {
    // Container for hash of standard data types
    // @astgen op1 := typesp : List[AstNodeDType]
    //
    // @astgen ptr := m_constraintRefp : Optional[AstConstraintRefDType]
    // @astgen ptr := m_emptyQueuep : Optional[AstEmptyQueueDType]
    // @astgen ptr := m_queueIndexp : Optional[AstQueueDType]
    // @astgen ptr := m_streamp : Optional[AstStreamDType]
    // @astgen ptr := m_voidp : Optional[AstVoidDType]
    AstBasicDType* m_basicps[VBasicDTypeKwd::_ENUM_MAX]{};
    //
    using DetailedMap = std::map<VBasicTypeKey, AstBasicDType*>;
    DetailedMap m_detailedMap;

public:
    explicit AstTypeTable(FileLine* fl);
    ASTGEN_MEMBERS_AstTypeTable;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void cloneRelink() override { V3ERROR_NA; }  // Not cloneable
    AstBasicDType* findBasicDType(FileLine* fl, VBasicDTypeKwd kwd);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, int width, int widthMin,
                                     VSigning numeric);
    AstBasicDType* findLogicBitDType(FileLine* fl, VBasicDTypeKwd kwd, const VNumRange& range,
                                     int widthMin, VSigning numeric);
    AstBasicDType* findCreateSameDType(AstBasicDType& node);
    AstBasicDType* findInsertSameDType(AstBasicDType* nodep);
    AstConstraintRefDType* findConstraintRefDType(FileLine* fl);
    AstEmptyQueueDType* findEmptyQueueDType(FileLine* fl);
    AstQueueDType* findQueueIndexDType(FileLine* fl);
    AstStreamDType* findStreamDType(FileLine* fl);
    AstVoidDType* findVoidDType(FileLine* fl);
    void clearCache();
    void repairCache();
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
};
class AstTypedef final : public AstNode {
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op4 := attrsp : List[AstNode] // Attributes during early parse

    string m_name;
    string m_tag;  // Holds the string of the verilator tag -- used in JSON output.
    uint32_t m_declTokenNum;  // Declaration token number
    bool m_attrPublic = false;
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_isUnderClass : 1;  // Underneath class

public:
    AstTypedef(FileLine* fl, const string& name, AstNode* attrsp, VFlagChildDType,
               AstNodeDType* dtp)
        : ASTGEN_SUPER_Typedef(fl)
        , m_name{name}
        , m_declTokenNum{fl->tokenNum()}
        , m_isHideLocal{false}
        , m_isHideProtected{false}
        , m_isUnderClass{false} {
        childDTypep(dtp);  // Only for parser
        addAttrsp(attrsp);
        dtypep(nullptr);  // V3Width will resolve
    }
    ASTGEN_MEMBERS_AstTypedef;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    AstNodeDType* getChildDTypep() const override { return childDTypep(); }
    virtual AstNodeDType* subDTypep() const VL_MT_STABLE {
        return dtypep() ? dtypep() : childDTypep();
    }
    // METHODS
    uint32_t declTokenNum() const override { return m_declTokenNum; }
    void declTokenNumSetMin(uint32_t tokenNum) override {
        m_declTokenNum = std::min(m_declTokenNum, tokenNum);
    }
    string name() const override VL_MT_STABLE { return m_name; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    bool hasDType() const override VL_MT_SAFE { return true; }
    void name(const string& flag) override { m_name = flag; }
    bool attrPublic() const { return m_attrPublic; }
    void attrPublic(bool flag) { m_attrPublic = flag; }
    bool isHideLocal() const { return m_isHideLocal; }
    void isHideLocal(bool flag) { m_isHideLocal = flag; }
    bool isHideProtected() const { return m_isHideProtected; }
    void isHideProtected(bool flag) { m_isHideProtected = flag; }
    bool isUnderClass() const { return m_isUnderClass; }
    void isUnderClass(bool flag) { m_isUnderClass = flag; }
    void tag(const string& text) override { m_tag = text; }
    string tag() const override { return m_tag; }
};
class AstTypedefFwd final : public AstNode {
    // Forward declaration of a type; stripped after netlist parsing is complete
    string m_name;
    const VFwdType m_fwdType;  // Forward type for lint check

public:
    AstTypedefFwd(FileLine* fl, const string& name, const VFwdType& fwdType)
        : ASTGEN_SUPER_TypedefFwd(fl)
        , m_name{name}
        , m_fwdType{fwdType} {}
    ASTGEN_MEMBERS_AstTypedefFwd;
    // METHODS
    string name() const override VL_MT_STABLE { return m_name; }
    void dump(std::ostream& str = std::cout) const override;
    void dumpJson(std::ostream& str = std::cout) const override;
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    VFwdType fwdType() const { return m_fwdType; }
};
class AstUdpTable final : public AstNode {
    // @astgen op1 := linesp : List[AstUdpTableLine]
public:
    AstUdpTable(FileLine* fl, AstUdpTableLine* linesp)
        : ASTGEN_SUPER_UdpTable(fl) {
        this->addLinesp(linesp);
        if (!v3Global.hasTable()) v3Global.setHasTable();
    }
    ASTGEN_MEMBERS_AstUdpTable;
};
class AstUdpTableLine final : public AstNode {
    // @astgen op1 := iFieldsp : List[AstUdpTableLineVal]  // Input fields
    // @astgen op2 := oFieldsp : List[AstUdpTableLineVal]  // Output fields
private:
    const bool m_udpIsCombo;  // Combinational or sequential UDP

public:
    class UdpCombo {};
    AstUdpTableLine(UdpCombo, FileLine* fl, AstUdpTableLineVal* iFieldsp,
                    AstUdpTableLineVal* oFieldsp)
        : ASTGEN_SUPER_UdpTableLine(fl)
        , m_udpIsCombo{true} {
        addIFieldsp(iFieldsp);
        addOFieldsp(oFieldsp);
    }
    class UdpSequential {};
    AstUdpTableLine(UdpSequential, FileLine* fl, AstUdpTableLineVal* iFieldsp,
                    AstUdpTableLineVal* oFieldsp1, AstUdpTableLineVal* oFieldsp2)
        : ASTGEN_SUPER_UdpTableLine(fl)
        , m_udpIsCombo{false} {
        addIFieldsp(iFieldsp);
        addOFieldsp(oFieldsp1);
        addOFieldsp(oFieldsp2);
    }
    ASTGEN_MEMBERS_AstUdpTableLine;
    int udpIsCombo() const { return m_udpIsCombo; }
};
class AstUdpTableLineVal final : public AstNode {
    string m_text;  // Value character

public:
    AstUdpTableLineVal(FileLine* fl, const string& text)
        : ASTGEN_SUPER_UdpTableLineVal(fl)
        , m_text{text} {}
    ASTGEN_MEMBERS_AstUdpTableLineVal;
    string name() const override VL_MT_STABLE { return m_text; }
    void name(std::string const& text) override VL_MT_STABLE { m_text = text; }
    string text() const VL_MT_SAFE { return m_text; }
};
class AstVar final : public AstNode {
    // A variable (in/out/wire/reg/param) inside a module
    //
    // @astgen op1 := childDTypep : Optional[AstNodeDType]
    // @astgen op2 := delayp : Optional[AstDelay] // Net delay
    // Initial value that never changes (static const), or constructor argument for
    // MTASKSTATE variables
    // @astgen op3 := valuep : Optional[AstNode<AstNodeExpr|AstNodeDType>]
    //     Value is a DType for type parameter defaults
    // @astgen op4 := attrsp : List[AstNode] // Attributes during early parse
    // @astgen ptr := m_sensIfacep : Optional[AstIface]  // Interface type to which reads from this
    //                                                      var are sensitive

    string m_name;  // Name of variable
    string m_origName;  // Original name before dot addition
    string m_tag;  // Holds the string of the verilator tag -- used in JSON output.
    VVarType m_varType;  // Type of variable
    VDirection m_direction;  // Direction input/output etc
    VDirection m_declDirection;  // Declared direction input/output etc
    VLifetime m_lifetime;  // Lifetime
    VRandAttr m_rand;  // Randomizability of this variable (rand, randc, etc)
    int m_pinNum = 0;  // For JSON, if non-zero the connection pin number
    bool m_ansi : 1;  // Params or pins declared in the module header, rather than the body
    bool m_declTyped : 1;  // Declared as type (for dedup check)
    bool m_tristate : 1;  // Inout or triwire or trireg
    bool m_primaryIO : 1;  // In/out to top level (or directly assigned from same)
    bool m_primaryClock : 1;  // In/out to top level and is, or combinationally drives a SenItem
    bool m_sc : 1;  // SystemC variable
    bool m_scSensitive : 1;  // SystemC sensitive() needed
    bool m_sigPublic : 1;  // User C code accesses this signal or is top signal
    bool m_sigModPublic : 1;  // User C code accesses this signal and module
    bool m_sigUserRdPublic : 1;  // User C code accesses this signal, read only
    bool m_sigUserRWPublic : 1;  // User C code accesses this signal, read-write
    bool m_usedParam : 1;  // Parameter is referenced (on link; later signals not setup)
    bool m_usedLoopIdx : 1;  // Variable subject of for unrolling
    bool m_funcLocal : 1;  // Local variable for a function
    bool m_funcLocalSticky : 1;  // As m_funcLocal but remains set if var is moved to a static
    bool m_funcReturn : 1;  // Return variable for a function
    bool m_attrScBv : 1;  // User force bit vector attribute
    bool m_attrScBigUint : 1;  // User force sc_biguint attribute
    bool m_attrIsolateAssign : 1;  // User isolate_assignments attribute
    bool m_attrSFormat : 1;  // User sformat attribute
    bool m_attrSplitVar : 1;  // declared with split_var metacomment
    bool m_fileDescr : 1;  // File descriptor
    bool m_gotNansiType : 1;  // Linker saw Non-ANSI type declaration
    bool m_isConst : 1;  // Table contains constant data
    bool m_isContinuously : 1;  // Ever assigned continuously (for force/release)
    bool m_hasStrengthAssignment : 1;  // Is on LHS of assignment with strength specifier
    bool m_isStatic : 1;  // Static C variable (for Verilog see instead lifetime())
    bool m_isPulldown : 1;  // Tri0
    bool m_isPullup : 1;  // Tri1
    bool m_isIfaceParent : 1;  // dtype is reference to interface present in this module
    bool m_isInternal : 1;  // Internal state, don't add to method pinter
    bool m_isIfaceParam : 1;  // Parameter belongs to an interface/modport
    bool m_isDpiOpenArray : 1;  // DPI import open array
    bool m_isHideLocal : 1;  // Verilog local
    bool m_isHideProtected : 1;  // Verilog protected
    bool m_noReset : 1;  // Do not do automated reset/randomization
    bool m_noSubst : 1;  // Do not substitute out references
    bool m_substConstOnly : 1;  // Only substitute if constant
    bool m_overridenParam : 1;  // Overridden parameter by #(...) or defparam
    bool m_trace : 1;  // Trace this variable
    bool m_isLatched : 1;  // Not assigned in all control paths of combo always
    bool m_isForceable : 1;  // May be forced/released externally from user C code
    bool m_isForcedByCode : 1;  // May be forced/released from AstAssignForce/AstRelease
    bool m_isWrittenByDpi : 1;  // This variable can be written by a DPI Export
    bool m_isWrittenBySuspendable : 1;  // This variable can be written by a suspendable process
    bool m_ignorePostRead : 1;  // Ignore reads in 'Post' blocks during ordering
    bool m_ignorePostWrite : 1;  // Ignore writes in 'Post' blocks during ordering
    bool m_ignoreSchedWrite : 1;  // Ignore writes in scheduling (for special optimizations)
    bool m_dfgMultidriven : 1;  // Singal is multidriven, used by DFG to avoid repeat processing
    bool m_globalConstrained : 1;  // Global constraint per IEEE 1800-2023 18.5.8
    bool m_isStdRandomizeArg : 1;  // Argument variable created for std::randomize (__Varg*)
    void init() {
        m_ansi = false;
        m_declTyped = false;
        m_tristate = false;
        m_primaryIO = false;
        m_primaryClock = false;
        m_sc = false;
        m_scSensitive = false;
        m_usedParam = false;
        m_usedLoopIdx = false;
        m_sigPublic = false;
        m_sigModPublic = false;
        m_sigUserRdPublic = false;
        m_sigUserRWPublic = false;
        m_funcLocal = false;
        m_funcLocalSticky = false;
        m_funcReturn = false;
        m_attrScBv = false;
        m_attrScBigUint = false;
        m_attrIsolateAssign = false;
        m_attrSFormat = false;
        m_attrSplitVar = false;
        m_fileDescr = false;
        m_gotNansiType = false;
        m_isConst = false;
        m_isContinuously = false;
        m_hasStrengthAssignment = false;
        m_isStatic = false;
        m_isPulldown = false;
        m_isPullup = false;
        m_isIfaceParent = false;
        m_isInternal = false;
        m_isIfaceParam = false;
        m_isDpiOpenArray = false;
        m_isHideLocal = false;
        m_isHideProtected = false;
        m_noReset = false;
        m_noSubst = false;
        m_substConstOnly = false;
        m_overridenParam = false;
        m_trace = false;
        m_isLatched = false;
        m_isForceable = false;
        m_isForcedByCode = false;
        m_isWrittenByDpi = false;
        m_isWrittenBySuspendable = false;
        m_ignorePostRead = false;
        m_ignorePostWrite = false;
        m_ignoreSchedWrite = false;
        m_dfgMultidriven = false;
        m_globalConstrained = false;
        m_isStdRandomizeArg = false;
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
    }
    AstVar(FileLine* fl, VVarType type, const string& name, AstNodeDType* dtp)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        UASSERT(dtp, "AstVar created with no dtype");
        dtypep(dtp);
    }
    AstVar(FileLine* fl, VVarType type, const string& name, VFlagLogicPacked, int wantwidth)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetLogicSized(wantwidth, VSigning::UNSIGNED);
    }
    AstVar(FileLine* fl, VVarType type, const string& name, VFlagBitPacked, int wantwidth)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        dtypeSetBitSized(wantwidth, VSigning::UNSIGNED);
    }
    AstVar(FileLine* fl, VVarType type, const string& name, const AstVar* examplep)
        : ASTGEN_SUPER_Var(fl)
        , m_name{name}
        , m_origName{name} {
        init();
        combineType(type);
        if (examplep->childDTypep()) childDTypep(examplep->childDTypep()->cloneTree(true));
        dtypeFrom(examplep);
    }
    ASTGEN_MEMBERS_AstVar;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    inline bool sameNode(const AstNode* samep) const override;
    string name() const override VL_MT_STABLE { return m_name; }  // * = Var name
    bool hasDType() const override VL_MT_SAFE { return true; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
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
    void sensIfacep(AstIface* nodep) { m_sensIfacep = nodep; }
    void attrFileDescr(bool flag) { m_fileDescr = flag; }
    void attrScBv(bool flag) { m_attrScBv = flag; }
    void attrScBigUint(bool flag) { m_attrScBigUint = flag; }
    void attrIsolateAssign(bool flag) { m_attrIsolateAssign = flag; }
    void attrSFormat(bool flag) { m_attrSFormat = flag; }
    void attrSplitVar(bool flag) { m_attrSplitVar = flag; }
    void rand(const VRandAttr flag) { m_rand = flag; }
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
    void isConst(bool flag) { m_isConst = flag; }
    void isContinuously(bool flag) { m_isContinuously = flag; }
    void isStatic(bool flag) { m_isStatic = flag; }
    void isIfaceParent(bool flag) { m_isIfaceParent = flag; }
    void isInternal(bool flag) { m_isInternal = flag; }
    void isIfaceParam(bool flag) { m_isIfaceParam = flag; }
    void funcLocal(bool flag) {
        m_funcLocal = flag;
        if (flag) m_funcLocalSticky = true;
    }
    void funcReturn(bool flag) { m_funcReturn = flag; }
    void gotNansiType(bool flag) { m_gotNansiType = flag; }
    bool gotNansiType() { return m_gotNansiType; }
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
    void substConstOnly(bool flag) { m_substConstOnly = flag; }
    bool substConstOnly() const { return m_substConstOnly; }
    void overriddenParam(bool flag) { m_overridenParam = flag; }
    bool overriddenParam() const { return m_overridenParam; }
    void trace(bool flag) { m_trace = flag; }
    void isLatched(bool flag) { m_isLatched = flag; }
    bool isForceable() const { return m_isForceable; }
    void setForceable() { m_isForceable = true; }
    void setForcedByCode() { m_isForcedByCode = true; }
    bool isForced() const { return m_isForceable || m_isForcedByCode; }
    bool isWrittenByDpi() const { return m_isWrittenByDpi; }
    void setWrittenByDpi() { m_isWrittenByDpi = true; }
    bool isWrittenBySuspendable() const { return m_isWrittenBySuspendable; }
    void setWrittenBySuspendable() { m_isWrittenBySuspendable = true; }
    bool ignorePostRead() const { return m_ignorePostRead; }
    void setIgnorePostRead() { m_ignorePostRead = true; }
    bool ignorePostWrite() const { return m_ignorePostWrite; }
    void setIgnorePostWrite() { m_ignorePostWrite = true; }
    bool ignoreSchedWrite() const { return m_ignoreSchedWrite; }
    void setIgnoreSchedWrite() { m_ignoreSchedWrite = true; }
    bool dfgMultidriven() const { return m_dfgMultidriven; }
    void setDfgMultidriven() { m_dfgMultidriven = true; }
    void globalConstrained(bool flag) { m_globalConstrained = flag; }
    bool globalConstrained() const { return m_globalConstrained; }
    bool isStdRandomizeArg() const { return m_isStdRandomizeArg; }
    void setStdRandomizeArg() { m_isStdRandomizeArg = true; }
    // METHODS
    void name(const string& name) override { m_name = name; }
    void tag(const string& text) override { m_tag = text; }
    string tag() const override { return m_tag; }
    bool isAnsi() const { return m_ansi; }
    bool isContinuously() const { return m_isContinuously; }
    bool isDeclTyped() const { return m_declTyped; }
    bool isInout() const { return m_direction.isInout(); }
    bool isInoutOrRef() const { return m_direction.isInoutOrRef(); }
    bool isInput() const { return m_direction.isInput(); }
    bool isNonOutput() const { return m_direction.isNonOutput(); }
    bool isReadOnly() const VL_MT_SAFE { return m_direction.isReadOnly(); }
    bool isConstRef() const VL_MT_SAFE { return m_direction.isConstRef(); }
    bool isRef() const VL_MT_SAFE { return m_direction.isRef(); }
    bool isWritable() const VL_MT_SAFE { return m_direction.isWritable(); }
    bool isTristate() const { return m_tristate; }
    bool isPrimaryIO() const VL_MT_SAFE { return m_primaryIO; }
    bool isPrimaryInish() const { return isPrimaryIO() && isNonOutput(); }
    bool isPrimaryClock() const VL_MT_SAFE { return m_primaryClock; }
    void setPrimaryClock() { m_primaryClock = true; }
    bool isIfaceRef() const { return varType() == VVarType::IFACEREF; }
    void setIfaceRef() {
        m_direction = VDirection::NONE;
        m_varType = VVarType::IFACEREF;
    }
    bool isIfaceParent() const { return m_isIfaceParent; }
    bool isInternal() const { return m_isInternal; }
    bool isIfaceParam() const { return m_isIfaceParam; }
    bool isSignal() const { return varType().isSignal(); }
    bool isNet() const { return varType().isNet(); }
    bool isWor() const { return varType().isWor(); }
    bool isWiredNet() const { return varType().isWiredNet(); }
    bool isTemp() const { return varType().isTemp(); }
    bool isToggleCoverable() const {
        return ((isIO() || isSignal())
                && (isIO() || isBitLogic())
                // Wrapper would otherwise duplicate wrapped module's coverage
                && !isSc() && !isPrimaryIO() && !isConst() && !isDouble() && !isString());
    }
    bool isClassMember() const { return varType() == VVarType::MEMBER; }
    bool isVirtIface() const {
        if (AstIfaceRefDType* const dtp = VN_CAST(dtypep(), IfaceRefDType)) {
            return dtp->isVirtual();
        }
        return false;
    }
    bool isStatementTemp() const { return varType() == VVarType::STMTTEMP; }
    bool isXTemp() const { return varType() == VVarType::XTEMP; }
    bool isParam() const { return varType().isParam(); }
    bool isGParam() const { return varType() == VVarType::GPARAM; }
    bool isGenVar() const { return varType() == VVarType::GENVAR; }
    bool isBitLogic() const {
        const AstBasicDType* const bdtypep = basicp();
        return bdtypep && bdtypep->isBitLogic();
    }
    bool isUsedParam() const { return m_usedParam; }
    bool isUsedLoopIdx() const { return m_usedLoopIdx; }
    bool isSc() const VL_MT_SAFE { return m_sc; }
    bool isScQuad() const;
    bool isScBv() const VL_MT_STABLE;
    bool isScUint() const;
    bool isScUintBool() const;
    bool isScBigUint() const VL_MT_STABLE;
    bool isScSensitive() const { return m_scSensitive; }
    bool isSigPublic() const;
    bool isSigModPublic() const { return m_sigModPublic && !isIfaceRef(); }
    bool isSigUserRdPublic() const { return m_sigUserRdPublic && !isIfaceRef(); }
    bool isSigUserRWPublic() const { return m_sigUserRWPublic && !isIfaceRef(); }
    bool isTrace() const { return m_trace; }
    bool isRand() const { return m_rand.isRand(); }
    bool isRandC() const { return m_rand.isRandC(); }
    bool isConst() const VL_MT_SAFE { return m_isConst; }
    bool isStatic() const VL_MT_SAFE { return m_isStatic; }
    bool isLatched() const { return m_isLatched; }
    bool isFuncLocal() const { return m_funcLocal; }
    bool isFuncLocalSticky() const { return m_funcLocalSticky; }
    bool isFuncReturn() const { return m_funcReturn; }
    bool isPullup() const { return m_isPullup; }
    bool isPulldown() const { return m_isPulldown; }
    bool attrScBv() const { return m_attrScBv; }
    bool attrScBigUint() const { return m_attrScBigUint; }
    bool attrFileDescr() const { return m_fileDescr; }
    bool attrSFormat() const { return m_attrSFormat; }
    bool attrSplitVar() const { return m_attrSplitVar; }
    bool attrIsolateAssign() const { return m_attrIsolateAssign; }
    AstIface* sensIfacep() const { return m_sensIfacep; }
    VRandAttr rand() const { return m_rand; }
    string verilogKwd() const override;
    void lifetime(const VLifetime& flag) { m_lifetime = flag; }
    VLifetime lifetime() const { return m_lifetime; }
    void pinNum(int id) { m_pinNum = id; }
    int pinNum() const { return m_pinNum; }
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
    void combineType(const AstVar* otherp);
    void inlineAttrReset(const string& name) {
        if (direction() == VDirection::INOUT && varType() == VVarType::WIRE) {
            m_varType = VVarType::TRIWIRE;
        }
        m_direction = VDirection::NONE;
        m_name = name;
    }
    bool needsCReset() const {
        return !isIfaceParent() && !isIfaceRef() && !noReset() && !isParam() && !isStatementTemp()
               && !(basicp() && basicp()->isEvent());
    }
    static AstVar* scVarRecurse(AstNode* nodep);
};
class AstVarScope final : public AstNode {
    // A particular scoped usage of a variable
    // That is, as a module is used under multiple cells, we get a different
    // varscope for each var in the module
    // Parents: MODULE
    // Children: none
    //
    // @astgen ptr := m_scopep : Optional[AstScope]  // Scope variable is underneath
    // @astgen ptr := m_varp : Optional[AstVar]  // [AfterLink] Pointer to variable itself
    bool m_trace : 1;  // Tracing is turned on for this scope
    bool m_optimizeLifePost : 1;  // One half of an NBA pair using ShadowVariable scheme. Optimize.
public:
    AstVarScope(FileLine* fl, AstScope* scopep, AstVar* varp)
        : ASTGEN_SUPER_VarScope(fl)
        , m_scopep{scopep}
        , m_varp{varp} {
        UASSERT_OBJ(scopep, fl, "Scope must be non-null");
        UASSERT_OBJ(varp, fl, "Var must be non-null");
        m_trace = true;
        m_optimizeLifePost = false;
        dtypeFrom(varp);
    }
    ASTGEN_MEMBERS_AstVarScope;
    void cloneRelink() override {
        if (m_varp && m_varp->clonep()) {
            UASSERT(m_scopep->clonep(), "No clone cross link: " << this);
        }
        cloneRelinkGen();
    }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    string name() const override VL_MT_STABLE { return scopep()->name() + "->" + varp()->name(); }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool sameNode(const AstNode* samep) const override;
    bool hasDType() const override VL_MT_SAFE { return true; }
    AstVar* varp() const VL_MT_STABLE { return m_varp; }  // [After Link] Pointer to variable
    AstScope* scopep() const VL_MT_STABLE { return m_scopep; }  // Pointer to scope it's under
    void scopep(AstScope* nodep) { m_scopep = nodep; }
    bool isTrace() const { return m_trace; }
    void trace(bool flag) { m_trace = flag; }
    bool optimizeLifePost() const { return m_optimizeLifePost; }
    void optimizeLifePost(bool flag) { m_optimizeLifePost = flag; }
};

// === AstNodeCoverDecl ===
class AstCoverOtherDecl final : public AstNodeCoverDecl {
    // Coverage analysis point declaration
    // Used for other than toggle types of coverage
    string m_linescov;
    int m_offset;  // Offset column numbers to uniq-ify IFs
public:
    AstCoverOtherDecl(FileLine* fl, const string& page, const string& comment,
                      const string& linescov, int offset)
        : ASTGEN_SUPER_CoverOtherDecl(fl, page, comment)
        , m_linescov{linescov}
        , m_offset{offset} {}
    ASTGEN_MEMBERS_AstCoverOtherDecl;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int offset() const { return m_offset; }
    int size() const override { return 1; }
    const string& linescov() const { return m_linescov; }
    bool sameNode(const AstNode* samep) const override {
        const AstCoverOtherDecl* const asamep = VN_DBG_AS(samep, CoverOtherDecl);
        return AstNodeCoverDecl::sameNode(samep) && linescov() == asamep->linescov();
    }
};
class AstCoverToggleDecl final : public AstNodeCoverDecl {
    // Coverage analysis point declaration
    // Used for toggle coverage
    const VNumRange m_range;  // Packed array range covering each toggle bit
public:
    AstCoverToggleDecl(FileLine* fl, const string& page, const string& comment,
                       const VNumRange& range)
        : ASTGEN_SUPER_CoverToggleDecl(fl, page, comment)
        , m_range{range} {}
    ASTGEN_MEMBERS_AstCoverToggleDecl;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    int size() const override {
        // Changes 0 -> 1 and 1 -> 0 are counted separately
        return 2 * m_range.elements();
    }
    const VNumRange& range() const { return m_range; }
    bool sameNode(const AstNode* samep) const override {
        const AstCoverToggleDecl* const asamep = VN_DBG_AS(samep, CoverToggleDecl);
        return AstNodeCoverDecl::sameNode(samep) && range() == asamep->range();
    }
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
    bool hasDType() const override VL_MT_SAFE { return true; }
    AstNodeFTask* cloneType(const string& name) override {
        return new AstFunc{fileline(), name, nullptr, nullptr};
    }
    string verilogKwd() const override { return "function"; }
};
class AstLet final : public AstNodeFTask {
    // Verilog "let" statement
    // Parents: MODULE
    // stmtp list first item is returned StmtExpr, as Let always returns AstNodeExpr
public:
    AstLet(FileLine* fl, const string& name)
        : ASTGEN_SUPER_Let(fl, name, nullptr) {}
    ASTGEN_MEMBERS_AstLet;
    bool hasDType() const override VL_MT_SAFE { return true; }
    const char* broken() const override {
        BROKEN_RTN(!VN_IS(stmtsp(), StmtExpr));
        return nullptr;
    }
    AstNodeFTask* cloneType(const string& name) override { return new AstLet{fileline(), name}; }
    string verilogKwd() const override { return "let"; }
};
class AstProperty final : public AstNodeFTask {
    // A property inside a module
public:
    AstProperty(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER_Property(fl, name, stmtp) {}
    ASTGEN_MEMBERS_AstProperty;
    bool hasDType() const override VL_MT_SAFE { return true; }
    AstNodeFTask* cloneType(const string& name) override {
        return new AstProperty{fileline(), name, nullptr};
    }
    string verilogKwd() const override { return "property"; }
};
class AstSequence final : public AstNodeFTask {
    // A sequence inside a module
    // TODO when supported might not want to be a NodeFTask
    bool m_referenced = false;  // Ever referenced (for unsupported check)
public:
    AstSequence(FileLine* fl, const string& name, AstNode* stmtp)
        : ASTGEN_SUPER_Sequence(fl, name, stmtp) {}
    ASTGEN_MEMBERS_AstSequence;
    bool hasDType() const override VL_MT_SAFE { return true; }
    AstNodeFTask* cloneType(const string& name) override {
        return new AstSequence{fileline(), name, nullptr};
    }
    string verilogKwd() const override { return "sequence"; }
    bool isReferenced() const { return m_referenced; }
    void isReferenced(bool flag) { m_referenced = flag; }
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
    string verilogKwd() const override { return "task"; }
};

// === AstNodeFile ===
class AstCFile final : public AstNodeFile {
    // C++ output file
    // Parents:  NETLIST
    uint64_t m_complexityScore = 0;
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
    void dumpJson(std::ostream& str = std::cout) const override;
    uint64_t complexityScore() const { return m_complexityScore; }
    void complexityScore(uint64_t newScore) { m_complexityScore = newScore; }
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
    void dumpJson(std::ostream& str = std::cout) const override;
};

// === AstNodeGen ===
class AstGenBlock final : public AstNodeGen {
    // Generate 'begin'
    // @astgen op1 := genforp : Optional[AstNode]
    // @astgen op2 := itemsp : List[AstNode]
    std::string m_name;  // Name of block
    const bool m_unnamed;  // Originally unnamed (name change does not affect this)
    const bool m_implied;  // Not inserted by user

public:
    AstGenBlock(FileLine* fl, const string& name, AstNode* itemsp, bool implied)
        : ASTGEN_SUPER_GenBlock(fl)
        , m_name{name}
        , m_unnamed{name.empty()}
        , m_implied{implied} {
        this->addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstGenBlock;
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    std::string name() const override VL_MT_STABLE { return m_name; }
    void name(const std::string& name) override { m_name = name; }
    bool unnamed() const { return m_unnamed; }
    bool implied() const { return m_implied; }
};
class AstGenCase final : public AstNodeGen {
    // Generate 'case'
    // @astgen op1 := exprp : AstNodeExpr // Condition (scurtinee) expression
    // @astgen op2 := itemsp : List[AstGenCaseItem]
public:
    AstGenCase(FileLine* fl, AstNodeExpr* exprp, AstGenCaseItem* itemsp)
        : ASTGEN_SUPER_GenCase(fl) {
        this->exprp(exprp);
        this->addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstGenCase;
};
class AstGenFor final : public AstNodeGen {
    // Generate 'for'
    // @astgen op1 := initsp : List[AstNode]
    // @astgen op2 := condp : AstNodeExpr
    // @astgen op3 := incsp : List[AstNode]
    // @astgen op4 := itemsp : List[AstNode]
public:
    AstGenFor(FileLine* fl, AstNode* initsp, AstNodeExpr* condp, AstNode* incsp, AstNode* itemsp)
        : ASTGEN_SUPER_GenFor(fl) {
        this->addInitsp(initsp);
        this->condp(condp);
        this->addIncsp(incsp);
        this->addItemsp(itemsp);
    }
    ASTGEN_MEMBERS_AstGenFor;
};
class AstGenIf final : public AstNodeGen {
    // Generate 'if'
    // @astgen op1 := condp : AstNodeExpr
    // @astgen op2 := thensp : List[AstNode]
    // @astgen op3 := elsesp : List[AstNode]
public:
    AstGenIf(FileLine* fl, AstNodeExpr* condp, AstNode* thensp, AstNode* elsesp)
        : ASTGEN_SUPER_GenIf(fl) {
        this->condp(condp);
        this->addThensp(thensp);
        this->addElsesp(elsesp);
    }
    ASTGEN_MEMBERS_AstGenIf;
};

// === AstNodeModule ===
class AstClass final : public AstNodeModule {
    // @astgen op4 := extendsp : List[AstClassExtends]
    // MEMBERS
    // @astgen ptr := m_classOrPackagep : Optional[AstClassPackage]  // Package to be emitted with
    uint32_t m_declTokenNum;  // Declaration token number
    VBaseOverride m_baseOverride;  // BaseOverride (inital/final/extends)
    bool m_covergroup = false;  // Is covergroup (TODO perhaps make a new Ast node type for CG?)
    bool m_extended = false;  // Is extension or extended by other classes
    bool m_interfaceClass = false;  // Interface class
    bool m_needRNG = false;  // Need RNG, uses srandom/randomize
    bool m_useVirtualPublic = false;  // Subclasses need virtual public as uses interface class
    bool m_virtual = false;  // Virtual class

public:
    AstClass(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_Class(fl, name, libname)
        , m_declTokenNum{fl->tokenNum()} {}
    ASTGEN_MEMBERS_AstClass;
    string verilogKwd() const override { return isCovergroup() ? "covergroup" : "class"; }
    bool maybePointedTo() const override VL_MT_SAFE { return true; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    bool timescaleMatters() const override { return false; }
    AstClassPackage* classOrPackagep() const VL_MT_STABLE { return m_classOrPackagep; }
    void classOrPackagep(AstClassPackage* classpackagep) { m_classOrPackagep = classpackagep; }
    AstNode* membersp() const VL_MT_STABLE { return stmtsp(); }
    void addMembersp(AstNode* nodep) { addStmtsp(nodep); }
    bool isCovergroup() const { return m_covergroup; }
    void isCovergroup(bool flag) { m_covergroup = flag; }
    bool isExtended() const { return m_extended; }
    void isExtended(bool flag) { m_extended = flag; }
    bool isInterfaceClass() const { return m_interfaceClass; }
    void isInterfaceClass(bool flag) { m_interfaceClass = flag; }
    bool isVirtual() const { return m_virtual; }
    void isVirtual(bool flag) { m_virtual = flag; }
    bool needRNG() const { return m_needRNG; }
    void needRNG(bool flag) { m_needRNG = flag; }
    bool useVirtualPublic() const { return m_useVirtualPublic; }
    void useVirtualPublic(bool flag) { m_useVirtualPublic = flag; }
    // Return true if this class is an extension of base class (SLOW)
    // Accepts nullptrs
    static bool isClassExtendedFrom(const AstClass* refClassp, const AstClass* baseClassp);
    uint32_t declTokenNum() const override { return m_declTokenNum; }
    void declTokenNumSetMin(uint32_t tokenNum) override {
        m_declTokenNum = std::min(m_declTokenNum, tokenNum);
    }
    void baseOverride(const VBaseOverride& flag) { m_baseOverride = flag; }
    VBaseOverride baseOverride() const { return m_baseOverride; }
    // Return the lowest class extended from, or this class
    AstClass* baseMostClassp();
    static bool isCacheableChild(const AstNode* nodep);
    // Iterates top level members of the class, taking into account inheritance (starting from the
    // root superclass). Note: after V3Scope, several children are moved under an AstScope and will
    // not be found by this.
    template <typename T_Callable>
    void foreachMember(const T_Callable& f) {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 1>::type;
        static_assert(
            vlstd::is_invocable<T_Callable, AstClass*, T_Node*>::value
                && std::is_base_of<AstNode, T_Node>::value,
            "T_Callable 'f' must have a signature compatible with 'void(AstClass*, T_Node*)', "
            "with 'T_Node' being a subtype of 'AstNode'");
        if (const AstClassExtends* const cextendsp = this->extendsp()) {
            cextendsp->classp()->foreachMember(f);
        }
        for (AstNode* stmtp = stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstNode::privateTypeTest<T_Node>(stmtp)) f(this, static_cast<T_Node*>(stmtp));
        }
    }
    // Same as above, but stops after first match
    template <typename T_Callable>
    bool existsMember(const T_Callable& p) const {
        using T_Node = typename FunctionArgNoPointerNoCV<T_Callable, 1>::type;
        static_assert(
            vlstd::is_invocable_r<bool, T_Callable, const AstClass*, const T_Node*>::value
                && std::is_base_of<AstNode, T_Node>::value,
            "Predicate 'p' must have a signature compatible with 'bool(const AstClass*, "
            "const T_Node*)', with 'T_Node' being a subtype of 'AstNode'");
        if (const AstClassExtends* const cextendsp = this->extendsp()) {
            if (cextendsp->classp()->existsMember(p)) return true;
        }
        for (AstNode* stmtp = stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstNode::privateTypeTest<T_Node>(stmtp)) {
                if (p(this, static_cast<T_Node*>(stmtp))) return true;
            }
        }
        return false;
    }
};
class AstClassPackage final : public AstNodeModule {
    // The static information portion of a class (treated similarly to a package)
    //
    // @astgen ptr := m_classp : Optional[AstClass]  // Class package this is under
    //                                     // (weak pointer, hard link is other way)
public:
    AstClassPackage(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_ClassPackage(fl, name, libname) {}
    ASTGEN_MEMBERS_AstClassPackage;
    string verilogKwd() const override { return "classpackage"; }
    bool timescaleMatters() const override { return false; }
    AstClass* classp() const VL_MT_SAFE { return m_classp; }
    void classp(AstClass* classp) { m_classp = classp; }
};
class AstIface final : public AstNodeModule {
    // An interface declaration
    bool m_hasVirtualRef = false;  // There exists a virtual interface reference for this interface
public:
    AstIface(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_Iface(fl, name, libname) {}
    ASTGEN_MEMBERS_AstIface;
    // Interfaces have `timescale applicability but lots of code seems to
    // get false warnings if we enable this
    string verilogKwd() const override { return "interface"; }
    bool timescaleMatters() const override { return false; }
    bool hasVirtualRef() const { return m_hasVirtualRef; }
    void setHasVirtualRef() { m_hasVirtualRef = true; }
};
class AstModule final : public AstNodeModule {
    // A module declaration
    const bool m_isChecker;  // Module represents a checker
    const bool m_isProgram;  // Module represents a program
    bool m_hasGenericIface = false;  // Module contains a generic interface

public:
    class Checker {};  // for constructor type-overload selection
    class Program {};  // for constructor type-overload selection
    AstModule(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_Module(fl, name, libname)
        , m_isChecker{false}
        , m_isProgram{false} {}
    AstModule(FileLine* fl, const string& name, const string& libname, Checker)
        : ASTGEN_SUPER_Module(fl, name, libname)
        , m_isChecker{true}
        , m_isProgram{false} {}
    AstModule(FileLine* fl, const string& name, const string& libname, Program)
        : ASTGEN_SUPER_Module(fl, name, libname)
        , m_isChecker{false}
        , m_isProgram{true} {}
    ASTGEN_MEMBERS_AstModule;
    string verilogKwd() const override {
        return m_isChecker ? "checker" : m_isProgram ? "program" : "module";
    }
    bool timescaleMatters() const override { return true; }
    bool isChecker() const { return m_isChecker; }
    bool isProgram() const { return m_isProgram; }
    bool hasGenericIface() const { return m_hasGenericIface; }
    void hasGenericIface(bool hasGenericIface) { m_hasGenericIface = hasGenericIface; }
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
};
class AstNotFoundModule final : public AstNodeModule {
    // A missing module declaration
public:
    AstNotFoundModule(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_NotFoundModule(fl, name, libname) {}
    ASTGEN_MEMBERS_AstNotFoundModule;
    string verilogKwd() const override { return "/*not-found-*/ module"; }
    bool timescaleMatters() const override { return false; }
};
class AstPackage final : public AstNodeModule {
    // A package declaration
public:
    AstPackage(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_Package(fl, name, libname) {}
    ASTGEN_MEMBERS_AstPackage;
    string verilogKwd() const override { return "package"; }
    bool timescaleMatters() const override { return !isDollarUnit(); }
    static string dollarUnitName() { return AstNode::encodeName("$unit"); }
    bool isDollarUnit() const { return name() == dollarUnitName(); }
};
class AstPrimitive final : public AstNodeModule {
    // A primitive declaration
public:
    AstPrimitive(FileLine* fl, const string& name, const string& libname)
        : ASTGEN_SUPER_Primitive(fl, name, libname) {}
    ASTGEN_MEMBERS_AstPrimitive;
    string verilogKwd() const override { return "primitive"; }
    bool timescaleMatters() const override { return false; }
};

// === AstNodeProcedure ===
class AstAlways final : public AstNodeProcedure {
    // @astgen op1 := sentreep : Optional[AstSenTree] // Sensitivity list iff clocked
    const VAlwaysKwd m_keyword;

public:
    AstAlways(FileLine* fl, VAlwaysKwd keyword, AstSenTree* sentreep, AstNode* stmtsp = nullptr)
        : ASTGEN_SUPER_Always(fl, stmtsp)
        , m_keyword{keyword} {
        this->sentreep(sentreep);
    }
    explicit inline AstAlways(AstAssignW* assignp);
    ASTGEN_MEMBERS_AstAlways;
    //
    void dump(std::ostream& str) const override;
    void dumpJson(std::ostream& str) const override;
    VAlwaysKwd keyword() const { return m_keyword; }
};
class AstAlwaysObserved final : public AstNodeProcedure {
    // Like always but Observed scheduling region
    // @astgen op1 := sentreep : Optional[AstSenTree] // Sensitivity list, removed in V3Active

public:
    AstAlwaysObserved(FileLine* fl, AstSenTree* sentreep, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysObserved(fl, bodysp) {
        this->sentreep(sentreep);
    }
    ASTGEN_MEMBERS_AstAlwaysObserved;
};
class AstAlwaysPost final : public AstNodeProcedure {
    // Like always but 'post' scheduled, e.g. for array NBA commits

public:
    explicit AstAlwaysPost(FileLine* fl)
        : ASTGEN_SUPER_AlwaysPost(fl, nullptr) {}
    ASTGEN_MEMBERS_AstAlwaysPost;
};
class AstAlwaysPostponed final : public AstNodeProcedure {
    // Like always but Postponed scheduling region

public:
    AstAlwaysPostponed(FileLine* fl, AstNode* stmtsp)
        : ASTGEN_SUPER_AlwaysPostponed(fl, stmtsp) {}
    ASTGEN_MEMBERS_AstAlwaysPostponed;
};
class AstAlwaysPre final : public AstNodeProcedure {
    // Like always but 'pre' scheduled, e.g. for implementing NBAs

public:
    explicit AstAlwaysPre(FileLine* fl)
        : ASTGEN_SUPER_AlwaysPre(fl, nullptr) {}
    ASTGEN_MEMBERS_AstAlwaysPre;
};
class AstAlwaysReactive final : public AstNodeProcedure {
    // Like always but Reactive scheduling region
    // @astgen op1 := sentreep : Optional[AstSenTree] // Sensitivity list, removed in V3Active

public:
    AstAlwaysReactive(FileLine* fl, AstSenTree* sentreep, AstNode* bodysp)
        : ASTGEN_SUPER_AlwaysReactive(fl, bodysp) {
        this->sentreep(sentreep);
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
    // Parser only concept C-style "[lhsp]", an AstUnknownRange, QueueRange or Range,
    // unknown until lhsp type is determined
    // @astgen op1 := elementsp : AstNode<AstNodeExpr|AstNodeDType>
public:
    AstBracketRange(FileLine* fl, AstNode* elementsp)
        : ASTGEN_SUPER_BracketRange(fl) {
        this->elementsp(elementsp);
    }
    ASTGEN_MEMBERS_AstBracketRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { V3ERROR_NA_RETURN(""); }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
    // Will be removed in V3Width, which relies on this
    // being a child not a dtype pointed node
    bool maybePointedTo() const override VL_MT_SAFE { return false; }
};
class AstRange final : public AstNodeRange {
    // Range specification, for use under variables and cells
    // @astgen op1 := leftp : AstNodeExpr
    // @astgen op2 := rightp : AstNodeExpr
    const bool m_fromBracket = false;  // From C-style '[x]' declaration
public:
    AstRange(FileLine* fl, AstNodeExpr* leftp, AstNodeExpr* rightp, bool fromBracket = false)
        : ASTGEN_SUPER_Range(fl)
        , m_fromBracket{fromBracket} {
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
    void dumpJson(std::ostream& str) const override;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    bool sameNode(const AstNode* samep) const override {
        const AstRange* const asamep = VN_DBG_AS(samep, Range);
        return fromBracket() == asamep->fromBracket();
    }
    bool fromBracket() const { return m_fromBracket; }
};
class AstUnsizedRange final : public AstNodeRange {
    // Unsized range specification, for open arrays
public:
    explicit AstUnsizedRange(FileLine* fl)
        : ASTGEN_SUPER_UnsizedRange(fl) {}
    ASTGEN_MEMBERS_AstUnsizedRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[]"; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};
class AstWildcardRange final : public AstNodeRange {
    // Wildcard range specification, for wildcard index type associative arrays
public:
    explicit AstWildcardRange(FileLine* fl)
        : ASTGEN_SUPER_WildcardRange(fl) {}
    ASTGEN_MEMBERS_AstWildcardRange;
    virtual string emitC() { V3ERROR_NA_RETURN(""); }
    virtual string emitVerilog() { return "[*]"; }
    bool sameNode(const AstNode* /*samep*/) const override { return true; }
};

#endif  // Guard
