// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for task nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Task's Transformations:
//
// Each module:
//      Look for TASKREF
//          Insert task's statements into the referrer
//          Look for getters (class methods that can be replaced
//          with a member reference)
//      Look for TASKs
//          Remove them, they're inlined
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Task.h"

#include "V3Const.h"
#include "V3ConstPool.h"
#include "V3Control.h"
#include "V3EmitCBase.h"
#include "V3Graph.h"
#include "V3LanguageWords.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <tuple>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Graph subclasses

class TaskBaseVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(TaskBaseVertex, V3GraphVertex);
    AstNode* m_impurep = nullptr;  // Node causing impure function w/ outside references
    bool m_noInline = false;  // Marked with pragma
public:
    explicit TaskBaseVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    ~TaskBaseVertex() override = default;
    bool pure() const { return m_impurep == nullptr; }
    AstNode* impureNode() const { return m_impurep; }
    void impure(AstNode* nodep) { m_impurep = nodep; }
    bool noInline() const { return m_noInline; }
    void noInline(bool flag) { m_noInline = flag; }
};

class TaskFTaskVertex final : public TaskBaseVertex {
    VL_RTTI_IMPL(TaskFTaskVertex, TaskBaseVertex);
    // Every task gets a vertex, and we link tasks together based on funcrefs.
    AstNodeFTask* const m_nodep;
    AstCFunc* m_cFuncp = nullptr;  // Function created for this task
    bool m_needsNonInlineCFunc = false;  // Needs CFunc for selected non-inlined call sites

public:
    TaskFTaskVertex(V3Graph* graphp, AstNodeFTask* nodep)
        : TaskBaseVertex{graphp}
        , m_nodep{nodep} {}
    ~TaskFTaskVertex() override = default;
    AstNodeFTask* nodep() const VL_MT_STABLE { return m_nodep; }
    string name() const override VL_MT_STABLE { return nodep()->name(); }
    string dotColor() const override { return pure() ? "black" : "red"; }
    AstCFunc* cFuncp() const { return m_cFuncp; }
    void cFuncp(AstCFunc* nodep) { m_cFuncp = nodep; }
    bool needsNonInlineCFunc() const { return m_needsNonInlineCFunc; }
    void needsNonInlineCFunc(bool flag) { m_needsNonInlineCFunc = flag; }
};

class TaskCodeVertex final : public TaskBaseVertex {
    VL_RTTI_IMPL(TaskCodeVertex, TaskBaseVertex);
    // Top vertex for all calls not under another task
public:
    explicit TaskCodeVertex(V3Graph* graphp)
        : TaskBaseVertex{graphp} {}
    ~TaskCodeVertex() override = default;
    string name() const override VL_MT_STABLE { return "*CODE*"; }
    string dotColor() const override { return "green"; }
};

class TaskEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(TaskEdge, V3GraphEdge)
public:
    TaskEdge(V3Graph* graphp, TaskBaseVertex* fromp, TaskBaseVertex* top)
        : V3GraphEdge{graphp, fromp, top, 1, false} {}
    ~TaskEdge() override = default;
    string dotLabel() const override { return "w" + cvtToStr(weight()); }
};

//######################################################################

class TaskStateVisitor final : public VNVisitor {
    // NODE STATE
    //  Output:
    //   AstNodeFTask::user3p   // AstScope* this FTask is under
    //   AstNodeFTask::user4p   // GraphFTaskVertex* this FTask is under
    //   AstVar::user4p         // GraphFTaskVertex* this variable is declared in
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;

    // TYPES
    using VarToScopeMap = std::map<std::pair<AstScope*, AstVar*>, AstVarScope*>;
    using FuncToClassMap = std::unordered_map<const AstNodeFTask*, AstClass*>;
    // MEMBERS
    VarToScopeMap m_varToScopeMap;  // Map for Var -> VarScope mappings
    FuncToClassMap m_funcToClassMap;  // Map for ctor func -> class
    AstNodeFTask* m_ctorp = nullptr;  // Class constructor
    AstClass* m_classp = nullptr;  // Current class
    V3Graph m_callGraph;  // Task call graph
    TaskBaseVertex* m_curVxp;  // Current vertex we're adding to
    std::vector<AstInitialAutomatic*> m_initialps;  // Initial blocks to move
    bool m_underPortVar = false;  // Visiting under a port AstVar; any expression there
                                  // is a default value, evaluated at call sites only

public:
    // METHODS
    static bool isVirtualIfaceMethodCall(const AstNodeFTaskRef* refp) {
        const AstMethodCall* const mrefp = VN_CAST(refp, MethodCall);
        if (!mrefp) return false;
        const AstNodeExpr* const fromp = mrefp->fromp();
        if (!fromp || !fromp->dtypep()) return false;
        const AstIfaceRefDType* const ifrefp = VN_CAST(fromp->dtypep()->skipRefp(), IfaceRefDType);
        return ifrefp && ifrefp->isVirtual();
    }
    static bool isIfaceFTaskScope(const AstScope* scopep) {
        return scopep && VN_IS(scopep->modp(), Iface);
    }
    AstScope* getScope(AstNodeFTask* nodep) {
        AstScope* const scopep = VN_AS(nodep->user3p(), Scope);
        UASSERT_OBJ(scopep, nodep, "No scope for function");
        return scopep;
    }
    AstVarScope* findVarScope(AstScope* scopep, AstVar* nodep) {
        const auto iter = m_varToScopeMap.find(std::make_pair(scopep, nodep));
        UASSERT_OBJ(iter != m_varToScopeMap.end(), nodep, "No scope for var");
        return iter->second;
    }
    AstClass* getClassp(AstNodeFTask* nodep) {
        AstClass* const classp = m_funcToClassMap[nodep];
        UASSERT_OBJ(classp, nodep, "No class for ctor func");
        return classp;
    }
    void remapFuncClassp(AstNodeFTask* nodep, AstNodeFTask* newp) {
        m_funcToClassMap[newp] = getClassp(nodep);
    }
    bool ftaskNoInline(AstNodeFTask* nodep) { return getFTaskVertex(nodep)->noInline(); }
    bool ftaskNeedsNonInlineCFunc(AstNodeFTask* nodep) {
        return getFTaskVertex(nodep)->needsNonInlineCFunc();
    }
    AstCFunc* ftaskCFuncp(AstNodeFTask* nodep) { return getFTaskVertex(nodep)->cFuncp(); }
    void ftaskCFuncp(AstNodeFTask* nodep, AstCFunc* cfuncp) {
        getFTaskVertex(nodep)->cFuncp(cfuncp);
    }
    // Returns pointer to node that makes the given FTask impure
    AstNode* checkImpure(AstNodeFTask* nodep) { return getFTaskVertex(nodep)->impureNode(); }

private:
    TaskFTaskVertex* getFTaskVertex(AstNodeFTask* nodep) {
        if (!nodep->user4p()) nodep->user4p(new TaskFTaskVertex{&m_callGraph, nodep});
        return static_cast<TaskFTaskVertex*>(nodep->user4u().toGraphVertex());
    }

    void propagateImpureReason() {
        std::vector<TaskFTaskVertex*> workList;
        // Gather all impure FTask vertices
        for (V3GraphVertex& vtx : m_callGraph.vertices()) {
            if (TaskFTaskVertex* const ftVtxp = vtx.cast<TaskFTaskVertex>()) {
                if (!ftVtxp->pure()) workList.emplace_back(ftVtxp);
            }
        }
        // Mark every pure caller as impure and enqueue them - this propagates impureness
        while (!workList.empty()) {
            TaskFTaskVertex* const calleep = workList.back();
            workList.pop_back();
            UASSERT_OBJ(!calleep->pure(), calleep->nodep(), "Should not enqueue pure vertex");
            for (V3GraphEdge& edge : calleep->inEdges()) {
                if (TaskFTaskVertex* const callerp = edge.fromp()->cast<TaskFTaskVertex>()) {
                    if (!callerp->pure()) continue;  // Already processed or on workList
                    callerp->impure(calleep->impureNode());
                    workList.emplace_back(callerp);
                }
            }
        }
    }

    void decideInlining() {
        for (V3GraphVertex& vtx : m_callGraph.vertices()) {
            TaskFTaskVertex* const ftVtxp = vtx.cast<TaskFTaskVertex>();
            if (!ftVtxp) continue;
            // Move on if already decided not to inline
            if (ftVtxp->noInline()) continue;
            // If inlining blanked disabled, don't do it. Note this usually
            // results in large amounts of breakage so is mostly for testing.
            if (!v3Global.opt.fInlineFuncs()) {
                ftVtxp->noInline(true);
                continue;
            }

            // If eagerly inlining (historic - and still default - behaviour) then nothing to do
            if (v3Global.opt.fInlineFuncsEager()) continue;

            AstNodeFTask* const ftaskp = ftVtxp->nodep();
            // We are relying on inlining of some internal functions for
            // functional corretness. Probably that's not a good thing?
            if (!ftaskp->verilogFunction()) continue;
            // Non-inlned public functions are a bit broken right now, so keep
            // inlining them (internal calls are inlined + keep public version)
            if (ftaskp->taskPublic()) continue;
            // If the function is pure, it's OK not to inline, so don't do it
            if (ftVtxp->pure()) ftVtxp->noInline(true);
        }
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        // Each FTask is unique per-scope, so AstNodeFTaskRefs do not need
        // pointers to what scope the FTask is to be invoked under.
        // However, to create variables, we need to track the scopes involved.
        // Find all var->varscope mappings, for later cleanup
        for (AstNode* const stmtp : nodep->varspList()) {
            if (AstVarScope* const vscp = VN_CAST(stmtp, VarScope)) {
                AstVar* const varp = vscp->varp();
                if (varp->isFuncLocal() || varp->isUsedLoopIdx()
                    || varp->lifetime().isAutomatic()) {
                    UINFO(9, "   funcvsc " << vscp);
                    m_varToScopeMap.emplace(std::make_pair(nodep, varp), vscp);
                }
            }
        }
        // Likewise, all FTask->scope mappings
        for (AstNode* const stmtp : nodep->blockspList()) {
            if (AstNodeFTask* const taskp = VN_CAST(stmtp, NodeFTask)) taskp->user3p(nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // We make multiple edges if a task is called multiple times from another task.
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked task");
        TaskFTaskVertex* const taskVtxp = getFTaskVertex(nodep->taskp());
        new TaskEdge{&m_callGraph, m_curVxp, taskVtxp};
        // Virtual-interface method calls dispatch through a runtime handle and
        // must not be inlined.
        if (isVirtualIfaceMethodCall(nodep)) taskVtxp->needsNonInlineCFunc(true);
        // Do we have to disable inlining the function?
        const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        if (!taskVtxp->noInline()) {  // Else short-circuit below
            for (const auto& itr : tconnects) {
                const AstVar* const portp = itr.first;
                const AstArg* const argp = itr.second;
                if (const AstNodeExpr* const pinp = argp->exprp()) {
                    if ((portp->isRef() || portp->isConstRef()) && !VN_IS(pinp, VarRef)) {
                        UINFO(9, "No function inline due to ref " << pinp);
                        taskVtxp->noInline(true);
                    }
                }
            }
        }
    }
    void visit(AstNodeFTask* nodep) override {
        UINFO(9, "  TASK " << nodep);
        VL_RESTORER(m_curVxp);
        m_curVxp = getFTaskVertex(nodep);
        if (nodep->dpiImport()) m_curVxp->noInline(true);
        if (nodep->classMethod()) m_curVxp->noInline(true);  // Until V3Task supports it
        if (nodep->recursive()) m_curVxp->noInline(true);
        if (nodep->isConstructor()) {
            m_curVxp->noInline(true);
            m_ctorp = nodep;
            UASSERT_OBJ(m_classp, nodep, "Ctor not under class");
            m_funcToClassMap[nodep] = m_classp;
        }
        iterateChildren(nodep);
    }
    void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::NO_INLINE_TASK) {
            // Just mark for the next steps, and we're done with it.
            m_curVxp->noInline(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    void visit(AstVar* nodep) override {
        VL_RESTORER(m_underPortVar);
        if (nodep->isIO()) m_underPortVar = true;
        iterateChildren(nodep);
        nodep->user4p(m_curVxp);  // Remember what task it's under
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_underPortVar) return;
        AstVar* const varp = nodep->varp();
        // Reading a constant pool entry does not depend on external runtime state.
        if (nodep->access().isReadOnly() && varp->constPoolEntry()) return;
        if (varp->user4u().toGraphVertex() != m_curVxp) {
            if (m_curVxp->pure() && !varp->isXTemp() && !varp->isParam()) m_curVxp->impure(nodep);
        }
    }
    void visit(AstClass* nodep) override {
        // Move initial statements into the constructor
        VL_RESTORER_CLEAR(m_initialps);
        VL_RESTORER(m_ctorp);
        VL_RESTORER(m_classp);
        m_ctorp = nullptr;
        m_classp = nodep;
        {  // Find m_initialps, m_ctor
            iterateChildren(nodep);
        }
        UASSERT_OBJ(m_ctorp, nodep, "class constructor missing");  // LinkDot always makes it
        AstNode* insertp = nullptr;
        for (AstInitialAutomatic* initialp : m_initialps) {
            if (AstNode* const movep = initialp->stmtsp()) {
                movep->unlinkFrBackWithNext();
                // Next InitialAutomatic must go in order after what we inserted
                insertp = AstNode::addNextNull(insertp, movep);
            }
            VL_DO_DANGLING(pushDeletep(initialp->unlinkFrBack()), initialp);
        }
        m_initialps.clear();
        m_ctorp->prependStmtsp(insertp);
    }
    void visit(AstInitialAutomatic* nodep) override {
        m_initialps.push_back(nodep);
        iterateChildren(nodep);
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TaskStateVisitor(AstNetlist* nodep) {
        m_curVxp = new TaskCodeVertex{&m_callGraph};
        //
        iterate(nodep);
        //
        m_callGraph.removeRedundantEdgesSum(&TaskEdge::followAlwaysTrue);
        propagateImpureReason();
        decideInlining();
        if (dumpGraphLevel()) m_callGraph.dumpDotFilePrefixed("task_call");
    }
    ~TaskStateVisitor() override = default;
    VL_UNCOPYABLE(TaskStateVisitor);
};

//######################################################################
// DPI related utility functions

struct TaskDpiUtils final {
    // Returns a vector of ('elements', 'stride') pairs for each unpacked dimension
    static std::vector<std::pair<int, int>> unpackDimsAndStrides(AstVar* varp) {
        AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
        std::vector<std::pair<int, int>> dimStrides;
        AstUnpackArrayDType* const unpackp = VN_CAST(dtypep->skipRefp(), UnpackArrayDType);
        if (!unpackp) return dimStrides;

        const std::vector<AstUnpackArrayDType*> dims = unpackp->unpackDimensions();
        const size_t nDims = dims.size();
        dimStrides.resize(nDims);
        // Stride of fastest varying dimension is 1.
        dimStrides[nDims - 1].first = dims.back()->elementsConst();
        dimStrides[nDims - 1].second = 1;
        // Rest are densly packed
        for (ssize_t i = nDims - 2; i >= 0; --i) {
            dimStrides[i].first = dims[i]->elementsConst();
            dimStrides[i].second = dimStrides[i + 1].first * dimStrides[i + 1].second;
        }
        return dimStrides;
    }
    // Returns the prefix of a function-call like statement used to convert
    // from IEEE DPI data types to internal types, and a bool that is true
    // if type uses svBitVecVal/svLogicVecVal and ther result is returned via
    // an output parameter, o false if uses C primitive type and result is the
    // return value.
    static std::pair<std::string, bool> dpiToInternalCvtStmt(const AstNodeDType* dtypep) {
        const AstBasicDType* const basicp = dtypep->basicp();

        // DPI types using Primitive C types
        if (basicp->keyword() == VBasicDTypeKwd::CHANDLE) return {"VL_CVT_VP_Q(", false};
        if (basicp->keyword() == VBasicDTypeKwd::STRING) return {"VL_CVT_N_CSTR(", false};
        if (dtypep->isDpiPrimitive()) return {"(", false};

        // DPI types using svBitVecVal/svLogicVecVal
        const std::string vecType = dtypep->isDpiBitVec() ? "SVBV" : "SVLV";
        dtypep = dtypep->skipRefp();
        const char sizeChar = dtypep->width() <= 8    ? 'C'
                              : dtypep->width() <= 16 ? 'S'
                                                      : *dtypep->charIQWN();
        const std::string& size = std::to_string(dtypep->width());
        // cppcheck-suppress strPlusChar
        return {"VL_SET_"s + sizeChar + "_" + vecType + "(" + size + ", ", true};
    }
};

//######################################################################
// Task state, as a visitor of each AstNode

class TaskVisitor final : public VNVisitor {
    // NODE STATE
    // Each module:
    //    AstNodeFTask::user1   // True if its been expanded
    // Each funccall
    //  to 'relink' function:
    //    AstVar::user2p        // AstVarScope* to replace varref with
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // TYPES
    using DpiCFuncs = std::map<const string, std::tuple<AstNodeFTask*, std::string, AstCFunc*>>;

    // STATE
    TaskStateVisitor* const m_statep;  // Common state between visitors
    AstNodeModule* m_modp = nullptr;  // Current module
    AstTopScope* const m_topScopep = v3Global.rootp()->topScopep();  // The AstTopScope
    AstScope* m_scopep = nullptr;  // Current scope
    AstNode* m_insStmtp = nullptr;  // Where to insert statement
    bool m_inSensesp = false;  // Are we under a senitem?
    bool m_inNew = false;  // Are we under a constructor?
    // Variables created by createVarScope, shared by instances
    V3SharedTmps m_funcTmps{"__Vfunc", VVarType::BLOCKTEMP};  // For function calls
    V3SharedTmps m_taskTmps{"__Vtask", VVarType::BLOCKTEMP};  // For task calls
    V3SharedTmps m_consArrayTmps{"__VconsArrayTemp", VVarType::BLOCKTEMP};  // For ConsArray args
    V3SharedTmps m_forceTmps{"__Vforcefuncout", VVarType::VAR};  // For calls in force statements
    int m_unconVarNum = 0;  // Unique bad connection variable

    // STATE - across all visitors
    DpiCFuncs m_dpiNames;  // Map of all created DPI functions
    std::map<std::string, const AstStructDType*> m_dpiStructs;  // C names of DPI structures
    VDouble0 m_statInlines;  // Statistic tracking
    VDouble0 m_statGetters;  // Statistic tracking
    VDouble0 m_statHierDpisWithCosts;  // Statistic tracking

    // METHODS

    AstVarScope* createFuncVar(AstCFunc* funcp, const string& name, AstNodeDType* dtypep) {
        AstVar* const newvarp = new AstVar{funcp->fileline(), VVarType::BLOCKTEMP, name, dtypep};
        newvarp->funcLocal(true);
        funcp->addVarsp(newvarp);
        AstVarScope* const newvscp = new AstVarScope{funcp->fileline(), m_scopep, newvarp};
        m_scopep->addVarsp(newvscp);
        return newvscp;
    }
    AstVarScope* createFuncVar(AstCFunc* funcp, const string& name, AstVar* examplep) {
        return createFuncVar(funcp, name, examplep->dtypep());
    }
    AstVarScope* createInputVar(AstCFunc* funcp, const string& name, VBasicDTypeKwd kwd) {
        AstVar* const newvarp
            = new AstVar{funcp->fileline(), VVarType::BLOCKTEMP, name, funcp->findBasicDType(kwd)};
        newvarp->funcLocal(true);
        newvarp->direction(VDirection::INPUT);
        funcp->addArgsp(newvarp);
        AstVarScope* const newvscp = new AstVarScope{funcp->fileline(), m_scopep, newvarp};
        m_scopep->addVarsp(newvscp);
        return newvscp;
    }
    static AstVarScope* constPoolTable(AstVar* paramp) {
        // Move array params in functions into constant pool, return the VarScope of the entry
        AstVarRef* const refp = V3ConstPool::find(VN_AS(paramp->valuep(), ConsArray));
        AstVarScope* const vscp = refp->varScopep();
        VL_DO_DANGLING(refp->deleteTree(), refp);
        return vscp;
    }
    // Create variable for 'invarp' of the call 'refp', named after the called task and 'suffix'
    AstVarScope* createVarScope(const AstNodeFTaskRef* refp, AstVar* invarp,
                                const std::string& suffix) {
        if (invarp->isParam() && VN_IS(invarp->valuep(), ConsArray)) {
            return constPoolTable(invarp);
        } else {
            // We could create under either the ref's scope or the ftask's scope.
            // It shouldn't matter, as they are only local variables.
            // We choose to do it under whichever called this function, which results
            // in more cache locality.
            // Share the variable with the other scopes of the module, so the same calls in
            // instances use the same variables
            V3SharedTmps& tmps = VN_IS(refp, FuncRef) ? m_funcTmps : m_taskTmps;
            AstVarScope* const newvscp = tmps.make(invarp->fileline(), m_scopep, invarp->dtypep(),
                                                   refp->taskp()->shortName() + suffix);
            AstVar* const newvarp = newvscp->varp();
            newvarp->funcLocal(false);
            newvarp->propagateAttrFrom(invarp);
            newvarp->isInternal(true);
            return newvscp;
        }
    }

    // Replace varrefs with new var pointer
    void relink(AstNode* nodep) {
        nodep->foreachAndNext([](AstVarRef* refp) {
            if (refp->varp()->user2p()) {  // It's being converted to an alias.
                AstVarScope* const newvscp = VN_AS(refp->varp()->user2p(), VarScope);
                refp->varScopep(newvscp);
                refp->varp(refp->varScopep()->varp());
            }
        });
    }

    AstAssign* connectPortMakeInAssign(AstNodeExpr* pinp, AstVarScope* newvscp, bool pureCheck) {
        // Create input assignment to go in FRONT of function call
        AstNodeExpr* inPinp = pinp;
        if (AstResizeLValue* sinPinp = VN_CAST(inPinp, ResizeLValue)) inPinp = sinPinp->lhsp();
        AstNodeExpr* inPinClonep
            = pureCheck ? inPinp->cloneTreePure(true) : inPinp->cloneTree(true);
        // A reversed array is assigned by the left-to-right order of elements (IEEE 1800-2023 7.6)
        const AstUnpackArrayDType* const arrayp
            = VN_CAST(newvscp->dtypep()->skipRefp(), UnpackArrayDType);
        if (arrayp && arrayp->isReverseOf(inPinClonep->dtypep())) {
            inPinClonep
                = new AstCvtUnpackToUnpack{pinp->fileline(), inPinClonep, newvscp->dtypep()};
        }
        AstAssign* const assp = new AstAssign{
            pinp->fileline(), new AstVarRef{newvscp->fileline(), newvscp, VAccess::WRITE},
            inPinClonep};
        assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
        return assp;
    }
    AstAssign* connectPortMakeOutAssign(AstVar* portp, AstNodeExpr* pinp, AstVarScope* newvscp,
                                        bool pureCheck) {
        // If needed, remap size of function to caller's output size
        AstNodeExpr* outPinp = pinp;
        AstNodeExpr* postRhsp = new AstVarRef{newvscp->fileline(), newvscp, VAccess::READ};
        if (AstResizeLValue* soutPinp = VN_CAST(outPinp, ResizeLValue)) {
            outPinp = soutPinp->lhsp();
            if (VN_IS(outPinp, RToIRoundS) || VN_IS(outPinp, RToIS)) {
                outPinp = VN_AS(outPinp, NodeUniop)->lhsp();
                if (postRhsp->isSigned()) {
                    postRhsp = new AstISToRD{pinp->fileline(), postRhsp};
                } else {
                    postRhsp = new AstIToRD{pinp->fileline(), postRhsp};
                }
            } else {
                if (AstNodeUniop* aoutPinp = VN_CAST(outPinp, Extend)) {
                    outPinp = aoutPinp->lhsp();
                } else if (AstNodeUniop* aoutPinp = VN_CAST(outPinp, ExtendS)) {
                    outPinp = aoutPinp->lhsp();
                } else if (AstSel* aoutPinp = VN_CAST(outPinp, Sel)) {
                    outPinp = aoutPinp->fromp();
                } else {
                    outPinp->v3fatalSrc("Inout pin resizing should have had extend or select");
                }
                if (outPinp->width() < portp->width()) {
                    postRhsp = new AstSel{pinp->fileline(), postRhsp, 0, pinp->width()};
                } else {  // pin width > port width
                    if (pinp->isSigned() && postRhsp->isSigned()) {
                        postRhsp = new AstExtendS{pinp->fileline(), postRhsp};
                    } else {
                        postRhsp = new AstExtend{pinp->fileline(), postRhsp};
                    }
                }
            }
            postRhsp->dtypeFrom(outPinp);
        }
        if (VN_IS(outPinp, IToRD) || VN_IS(outPinp, ISToRD)) {
            outPinp = VN_AS(outPinp, NodeUniop)->lhsp();
            postRhsp = new AstRToIRoundS{pinp->fileline(), postRhsp};
            postRhsp->dtypeFrom(outPinp);
        }
        // Put output assignment AFTER function call
        AstNodeExpr* const outPinClonep
            = pureCheck ? outPinp->cloneTreePure(true) : outPinp->cloneTree(true);
        // A reversed array is assigned by the left-to-right order of elements (IEEE 1800-2023 7.6)
        const AstUnpackArrayDType* const arrayp
            = VN_CAST(outPinp->dtypep()->skipRefp(), UnpackArrayDType);
        if (arrayp && arrayp->isReverseOf(postRhsp->dtypep())) {
            postRhsp = new AstCvtUnpackToUnpack{pinp->fileline(), postRhsp, outPinp->dtypep()};
        }
        AstAssign* const assp = new AstAssign{pinp->fileline(), outPinClonep, postRhsp};
        assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
        return assp;
    }

    void changeAtWriteRecurse(AstNodeExpr* const exprp) {
        // Change nested at methods to writable variant
        if (AstCMethodHard* const cMethodp = VN_CAST(exprp, CMethodHard)) {
            if (cMethodp->method() == VCMethod::ARRAY_AT) {
                cMethodp->method(VCMethod::ARRAY_AT_WRITE);
            }
            changeAtWriteRecurse(cMethodp->fromp());
        }
    }

    void connectPort(const AstNodeFTaskRef* refp, AstVar* portp, AstArg* argp, AstNode* beginp,
                     bool inlineTask) {
        AstNodeExpr* pinp = argp->exprp();
        if (inlineTask) {
            portp->unlinkFrBack();
            pushDeletep(portp);  // Remove it from the clone (not original)
        }
        if (!pinp) {
            // Too few arguments in function call
        } else {
            UINFO(9, "     Port " << portp);
            UINFO(9, "      pin " << pinp);
            if (portp->isWritable() && VN_IS(pinp, Const)) {
                pinp->v3error("Function/task " + portp->direction().prettyName()  // e.g. "output"
                              + " connected to constant instead of variable: "
                              + portp->prettyNameQ());
                // Make temp pin to tie it off
                AstVar* const varp = new AstVar{pinp->fileline(), VVarType::STMTTEMP,
                                                "__VfuncUnconn_" + portp->name() + "__"
                                                    + std::to_string(m_unconVarNum++),
                                                portp->dtypep()};
                m_modp->addStmtsp(varp);
                AstVarScope* const newvscp = new AstVarScope{pinp->fileline(), m_scopep, varp};
                m_scopep->addVarsp(newvscp);
                AstVarRef* const repp = new AstVarRef{pinp->fileline(), newvscp, VAccess::WRITE};
                pinp->replaceWith(repp);
                VL_DO_DANGLING(pushDeletep(pinp), pinp);
                pinp = repp;
            }
            if (inlineTask) {
                pushDeletep(pinp->unlinkFrBack());  // Cloned in assignment below
                VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);  // Args no longer needed
            }
            if (portp->isRef() || portp->isConstRef()) {
                bool refArgOk = false;
                if (VN_IS(pinp, VarRef) || VN_IS(pinp, MemberSel) || VN_IS(pinp, StructSel)
                    || VN_IS(pinp, ArraySel)) {
                    refArgOk = true;
                } else if (AstCMethodHard* const cMethodp = VN_CAST(pinp, CMethodHard)) {
                    if (VN_IS(cMethodp->fromp()->dtypep()->skipRefp(), QueueDType)) {
                        refArgOk = cMethodp->method() == VCMethod::DYN_AT_WRITE_APPEND
                                   || cMethodp->method() == VCMethod::DYN_AT_WRITE_APPEND_BACK;
                    } else {
                        changeAtWriteRecurse(cMethodp);
                        refArgOk = cMethodp->method() == VCMethod::ARRAY_AT_WRITE;
                    }
                }
                if (refArgOk) {
                    if (AstVarRef* const varrefp = VN_CAST(pinp, VarRef)) {
                        varrefp->access(VAccess::READWRITE);
                    }
                } else {
                    pinp->v3error("Function/task ref argument is not of allowed type");
                }
                if (inlineTask) {
                    if (AstVarRef* const varrefp = VN_CAST(pinp, VarRef)) {
                        // Connect to this exact variable
                        AstVarScope* const localVscp = varrefp->varScopep();
                        UASSERT_OBJ(localVscp, varrefp, "Null var scope");
                        portp->user2p(localVscp);
                    } else {
                        pinp->v3fatalSrc("ref argument should have caused non-inline of function");
                    }
                }
            } else if (portp->isInout()) {
                // UINFOTREE(9, pinp, "", "pinrsize-");

                AstVarScope* const newvscp
                    = createVarScope(refp, portp, "__" + portp->shortName());
                portp->user2p(newvscp);
                if (!inlineTask) {
                    pinp->replaceWith(
                        new AstVarRef{newvscp->fileline(), newvscp, VAccess::READWRITE});
                    pushDeletep(pinp);  // Cloned by connectPortMakeInAssign
                }
                // Put input assignment in FRONT of all other statements
                AstAssign* const preassp = connectPortMakeInAssign(pinp, newvscp, true);
                beginp->addNextHere(preassp);

                AstAssign* const postassp = connectPortMakeOutAssign(portp, pinp, newvscp, true);
                beginp->addNext(postassp);
                // if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-pinrsize-out- ");
            } else if (portp->isWritable()) {
                // Even if it's referencing a varref, we still make a temporary
                // Else task(x,x,x) might produce incorrect results
                AstVarScope* const newvscp
                    = createVarScope(refp, portp, "__" + portp->shortName());
                portp->user2p(newvscp);
                if (!inlineTask) {
                    pinp->replaceWith(new AstVarRef{newvscp->fileline(), newvscp, VAccess::WRITE});
                    pushDeletep(pinp);  // Cloned by connectPortMakeOutAssign
                }
                AstAssign* const postassp = connectPortMakeOutAssign(portp, pinp, newvscp, false);
                // Put assignment BEHIND of all other statements
                beginp->addNext(postassp);
            } else if (inlineTask && portp->isNonOutput()) {
                // Make input variable
                AstVarScope* const newvscp
                    = createVarScope(refp, portp, "__" + portp->shortName());
                portp->user2p(newvscp);
                AstAssign* const preassp = connectPortMakeInAssign(pinp, newvscp, false);
                // Put assignment in FRONT of all other statements
                beginp->addNextHere(preassp);
            }
        }
    }

    bool hasRefArgument(AstNodeFTask* nodep) {
        for (AstNode* const stmtp : nodep->stmtspList()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (varp->isRef() || varp->isConstRef()) return true;
            }
        }
        return false;
    }

    AstNode* createInlinedFTask(AstNodeFTaskRef* refp, AstVarScope* outvscp) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstNode* const newbodysp
            = refp->taskp()->stmtsp() ? refp->taskp()->stmtsp()->cloneTree(true) : nullptr;
        AstNode* const beginp
            = new AstComment{refp->fileline(), "Function: "s + refp->name(), true};
        if (newbodysp) beginp->addNext(newbodysp);
        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-  newbegi: ");
        //
        // Create input variables
        AstNode::user2ClearTree();
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(refp, beginp);
            for (const auto& itr : tconnects) {
                AstVar* const portp = itr.first;
                AstArg* const argp = itr.second;
                connectPort(refp, portp, argp, beginp, true);
            }
        }
        UASSERT_OBJ(!refp->argsp(), refp, "Arg wasn't removed by above loop");
        {
            AstNode* nextstmtp;
            for (AstNode* stmtp = beginp; stmtp; stmtp = nextstmtp) {
                nextstmtp = stmtp->nextp();
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    // Any I/O variables that fell out of above loop were already linked
                    if (!portp->user2p()) {
                        // Move it to a new localized variable
                        AstVarScope* const localVscp
                            = createVarScope(refp, portp, "__" + portp->shortName());
                        portp->user2p(localVscp);
                        if (portp->needsCReset() && portp->lifetime().isAutomatic()
                            && !portp->valuep()) {
                            // Reset automatic var to its default, on each invocation of function
                            AstNode* const crstp = new AstAssign{
                                portp->fileline(),
                                new AstVarRef{portp->fileline(), portp, VAccess::WRITE},
                                new AstCReset{portp->fileline(), portp, false}};
                            portp->replaceWith(crstp);
                        } else {
                            portp->unlinkFrBack();
                        }
                        pushDeletep(portp);  // Remove it from the clone (not original)
                    }
                }
            }
        }
        // Create function output variables
        if (outvscp) {
            // UINFO(0, "setflag on " << funcp->fvarp() << " to " << outvscp);
            refp->taskp()->fvarp()->user2p(outvscp);
        }
        // Replace variable refs
        relink(beginp);
        //
        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-  iotask: ");
        return beginp;
    }

    AstNode* createNonInlinedFTask(AstNodeFTaskRef* refp, AstVarScope* outvscp, AstCNew*& cnewpr) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstCFunc* const cfuncp = m_statep->ftaskCFuncp(refp->taskp());
        UASSERT_OBJ(cfuncp, refp, "No non-inline task associated with this task call?");
        //
        AstNode* const beginp
            = new AstComment{refp->fileline(), "Function: "s + refp->name(), true};
        AstNodeCCall* ccallp;
        if (VN_IS(refp, New)) {
            AstCNew* const cnewp = new AstCNew{refp->fileline(), cfuncp};
            cnewp->dtypep(refp->dtypep());
            ccallp = cnewp;
            // Parent AstNew will replace with this CNew
            cnewpr = cnewp;
        } else if (const AstMethodCall* const mrefp = VN_CAST(refp, MethodCall)) {
            ccallp = new AstCMethodCall{refp->fileline(), mrefp->fromp()->unlinkFrBack(), cfuncp};
            ccallp->dtypeSetVoid();
            beginp->addNext(ccallp->makeStmt());
        } else {
            ccallp = new AstCCall{refp->fileline(), cfuncp};
            ccallp->dtypeSetVoid();
            beginp->addNext(ccallp->makeStmt());
        }

        if (const AstFuncRef* const funcRefp = VN_CAST(refp, FuncRef)) {
            ccallp->superReference(funcRefp->superReference());
        } else if (const AstTaskRef* const taskRefp = VN_CAST(refp, TaskRef)) {
            ccallp->superReference(taskRefp->superReference());
        } else if (const AstMethodCall* const methodCallp = VN_CAST(refp, MethodCall)) {
            ccallp->superReference(methodCallp->superReference());
        }

        // Convert complicated outputs to temp signals
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(refp, refp->taskp()->stmtsp());
            for (const auto& itr : tconnects) {
                AstVar* const portp = itr.first;
                AstArg* const argp = itr.second;
                connectPort(refp, portp, argp, beginp, false);
            }
        }
        // First argument is symbol table, then output if a function
        const bool needSyms = !refp->taskp()->dpiImport() || v3Global.opt.profExec();
        if (needSyms) ccallp->argTypes("vlSymsp");

        if (refp->taskp()->dpiContext()) {
            AstScopeName* const snp = refp->scopeNamep();
            UASSERT_OBJ(snp, refp, "Missing scoping context");
            snp->unlinkFrBack();
            FileLine* const flp = refp->fileline();
            // __Vscopep
            ccallp->addArgsp(snp);
            // __Vfilenamep
            ccallp->addArgsp(
                new AstCExpr{flp, AstCExpr::Pure{}, "\"" + flp->filenameEsc() + "\"", 64});
            // __Vlineno
            ccallp->addArgsp(new AstConst(flp, flp->lineno()));
        }

        // Move artument expression to the CCall, without AstArg
        for (AstArg* const argp : refp->argspList()) {
            ccallp->addArgsp(argp->exprp()->unlinkFrBack());
        }

        if (outvscp) ccallp->addArgsp(new AstVarRef{refp->fileline(), outvscp, VAccess::WRITE});

        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-  nitask: ");
        return beginp;
    }

    string dpiSignature(AstNodeFTask* nodep, AstVar* rtnvarp) const {
        // Return fancy signature for DPI function. Variable names are not included so differences
        // in only argument names will not matter (as required by the standard).
        string dpiproto;
        if (nodep->dpiPure()) dpiproto += "pure ";
        if (nodep->dpiContext()) dpiproto += "context ";
        dpiproto += rtnvarp ? rtnvarp->dpiArgType(true, true) : "void";
        dpiproto += " " + nodep->cname() + " (";
        string args;
        for (AstNode* const stmtp : nodep->stmtspList()) {
            if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
                    if (args != "") {
                        args += ", ";
                        dpiproto += ", ";
                    }
                    // Include both the Verilator and C type names, as if either
                    // differ we may get C compilation problems later. An unpacked structure
                    // has one layout per C name (checkDpiStructArgs), so its C name and
                    // elements suffice, as e.g. specializations differ only in Verilator names.
                    const std::string dpiType = portp->dpiArgType(false, false);
                    dpiproto += dpiType;
                    const std::string vType = portp->dtypep()->containsUnpackedStruct()
                                                  ? portp->dpiTmpVarType("")
                                                  : portp->dtypep()->prettyDTypeName(false);
                    if (!portp->isDpiOpenArray() && dpiType != vType) {
                        dpiproto += " /* " + vType + " */ ";
                    }
                    args += portp->name();  // Leftover so ,'s look nice
                }
            }
        }
        dpiproto += ")";
        return dpiproto;
    }

    static void checkLegalCIdentifier(AstNode* nodep, const string& name) {
        if (name.end() != std::find_if(name.begin(), name.end(), [](char c) {
                return !std::isalnum(c) && c != '_';
            })) {
            nodep->v3error("DPI function has illegal characters in C identifier name '" << name
                                                                                        << '\'');
        }
    }

    static AstNode* createDpiTemp(AstVar* portp, const string& suffix) {
        const string stmt = portp->dpiTmpVarType(portp->name() + suffix) + ";";
        return new AstCStmt{portp->fileline(), stmt};
    }

    void unlinkAndClone(AstNodeFTask* funcp, AstNode* nodep, bool withNext) {
        UASSERT_OBJ(nodep, funcp, "null in function object clone");
        if (funcp->recursive()) {
            VNRelinker relinkHandle;
            if (withNext) {
                nodep->unlinkFrBackWithNext(&relinkHandle);
            } else {
                nodep->unlinkFrBack(&relinkHandle);
            }
            // Recursive functions require the original argument list to
            // still be live for linking purposes.
            // The old function gets clone, so that node pointers are mostly
            // retained through the V3Task transformations
            AstNode* const newp = nodep->cloneTree(withNext);
            relinkHandle.relink(newp);
        } else {
            if (withNext) {
                nodep->unlinkFrBackWithNext();
            } else {
                nodep->unlinkFrBack();
            }
        }
    }

    static AstNode* createAssignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix,
                                              const string& toSuffix) {
        const string stmt = V3Task::assignInternalToDpi(portp, isPtr, frSuffix, toSuffix);
        return new AstCStmt{portp->fileline(), stmt};
    }

    // Create statement converting between 'internalp' and the DPI C expression 'dpip' of type
    // 'dtypep', neither an unpacked array nor an unpacked structure, to DPI if 'toDpi', else from
    // DPI. If the DPI type is svBitVecVal/svLogicVecVal, 'dpip' is a pointer to the value.
    static AstNodeStmt* createDpiScalarCvt(AstNodeExpr* internalp, AstCExpr* dpip,
                                           const AstNodeDType* dtypep, bool toDpi) {
        FileLine* const flp = internalp->fileline();
        const AstBasicDType* const basicp = dtypep->basicp();
        if (toDpi) {
            AstCStmt* const cstmtp = new AstCStmt{flp};
            if (dtypep->isDpiPrimitive()) {
                cstmtp->add(dpip);
                cstmtp->add(basicp->isCHandle() ? " = VL_CVT_Q_VP(" : " = ");
                cstmtp->add(internalp);
                cstmtp->add(basicp->isCHandle() ? ");" : basicp->isString() ? ".c_str();" : ";");
            } else {
                cstmtp->add((dtypep->isDpiBitVec() ? "VL_SET_SVBV_"s : "VL_SET_SVLV_"s)
                            + dtypep->skipRefp()->charIQWN() + "("
                            + std::to_string(dtypep->width()) + ", ");
                cstmtp->add(dpip);
                cstmtp->add(", ");
                cstmtp->add(internalp);
                cstmtp->add(");");
            }
            return cstmtp;
        }
        std::string cvt;
        bool useSvVec;
        std::tie(cvt, useSvVec) = TaskDpiUtils::dpiToInternalCvtStmt(dtypep);
        if (useSvVec) {
            AstCStmt* const cstmtp = new AstCStmt{flp};
            cstmtp->add(cvt);
            cstmtp->add(internalp);
            cstmtp->add(", ");
            cstmtp->add(dpip);
            cstmtp->add(");");
            return cstmtp;
        }
        // Number of bits in the C expression result, for masking.
        const int cwidth = basicp->widthWords() * VL_EDATASIZE;
        AstCExpr* const rhsp = new AstCExpr{flp, cvt, cwidth};
        rhsp->add(dpip);
        rhsp->add(")");
        return new AstAssign{flp, internalp, new AstSel{flp, rhsp, 0, dtypep->width()}};
    }

    // Create statements converting between 'internalp' and the DPI C expression 'dpip' of type
    // 'dtypep'. Unpacked arrays and unpacked structures are converted by their elements and
    // members, as DPI passes them as C arrays and C structures (IEEE 1800-2023 H.7.3).
    static AstNodeStmt* createDpiCvt(AstNodeExpr* internalp, AstCExpr* dpip,
                                     const AstNodeDType* dtypep, bool toDpi) {
        FileLine* const flp = internalp->fileline();
        dtypep = dtypep->skipRefp();
        // The DPI C expression with 'suffix' appended
        const auto suffixed = [&](const std::string& suffix) {
            AstCExpr* const newp = new AstCExpr{flp};
            newp->add(dpip->cloneTree(false));
            newp->add(suffix);
            return newp;
        };
        AstNodeStmt* stmtsp = nullptr;
        if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
            // Internal index 0 is of the lowest SystemVerilog index, as C index 0 is
            for (int i = 0; i < arrayp->elementsConst(); ++i) {
                AstNodeExpr* const elemp = new AstArraySel{flp, internalp->cloneTree(false), i};
                stmtsp = AstNode::addNext(
                    stmtsp, createDpiCvt(elemp, suffixed("[" + std::to_string(i) + "]"),
                                         arrayp->subDTypep(), toDpi));
            }
        } else if (dtypep->containsUnpackedStruct()) {
            for (const AstMemberDType* const itemp : VN_AS(dtypep, StructDType)->memberspList()) {
                AstStructSel* const selp
                    = new AstStructSel{flp, internalp->cloneTree(false), itemp->name()};
                selp->dtypeFrom(itemp->dtypep());
                stmtsp = AstNode::addNext(stmtsp,
                                          createDpiCvt(selp, suffixed("." + itemp->prettyName()),
                                                       itemp->subDTypep(), toDpi));
            }
        } else {
            return createDpiScalarCvt(internalp, dpip, dtypep, toDpi);
        }
        VL_DO_DANGLING(internalp->deleteTree(), internalp);
        VL_DO_DANGLING(dpip->deleteTree(), dpip);
        return stmtsp;
    }

    // Create statements converting between the internal variable 'vscp' and the DPI temporary or
    // argument 'dpiName'. Converts to DPI if 'toDpi', else from DPI. Internal representation is
    // scalar, 1D, or multi-dimensional array (similar to SV). DPI value is scalar or 1D array (if
    // unpacked array), always an array if of unpacked structures, as passed by reference.
    AstNodeStmt* createDpiArgCvt(AstCFunc* funcp, AstVarScope* vscp, const std::string& dpiName,
                                 bool toDpi) {
        AstVar* const varp = vscp->varp();
        FileLine* const flp = vscp->fileline();
        const VAccess access = toDpi ? VAccess::READ : VAccess::WRITE;
        const bool isStruct = varp->dtypep()->containsUnpackedStruct();
        AstCExpr* const dpip = new AstCExpr{flp, dpiName};
        AstUnpackArrayDType* const arrayp = VN_CAST(varp->dtypep()->skipRefp(), UnpackArrayDType);
        if (!arrayp) {
            if (isStruct) dpip->add("[0]");
            return createDpiCvt(new AstVarRef{flp, vscp, access}, dpip, varp->dtypep(), toDpi);
        }

        // One loop per dimension. Index names include the direction, as inout converts both ways.
        const std::string idxName = varp->name() + (toDpi ? "__VidxToDpi" : "__VidxFromDpi");
        const auto readp
            = [&](AstVarScope* idxp) { return new AstVarRef{flp, idxp, VAccess::READ}; };
        const std::vector<AstUnpackArrayDType*> dims = arrayp->unpackDimensions();
        std::vector<AstVarScope*> idxps;
        AstNodeExpr* internalp = new AstVarRef{flp, vscp, access};
        AstNodeExpr* linearp = new AstConst{flp, 0U};  // Index of the element in the 1D DPI value
        for (const AstUnpackArrayDType* const dimp : dims) {
            AstVarScope* const idxp = createFuncVar(funcp, idxName + std::to_string(idxps.size()),
                                                    funcp->findUInt32DType());
            idxps.push_back(idxp);
            internalp = new AstArraySel{flp, internalp, readp(idxp)};
            const uint32_t elements = dimp->elementsConst();
            linearp = new AstAdd{flp, new AstMul{flp, new AstConst{flp, elements}, linearp},
                                 readp(idxp)};
        }
        const AstNodeDType* const elemDTypep = varp->dtypep()->elemDTypep();
        if (isStruct || elemDTypep->isDpiPrimitive()) {
            dpip->add("[");
            dpip->add(linearp);
            dpip->add("]");
        } else {  // svBitVecVal/svLogicVecVal
            const uint32_t widthWords = elemDTypep->widthWords();
            dpip->add(" + ");
            dpip->add(new AstMul{flp, linearp, new AstConst{flp, widthWords}});
        }
        AstNodeStmt* stmtsp = createDpiCvt(internalp, dpip, elemDTypep, toDpi);

        // Wrap in the loops, innermost first
        for (size_t dim = dims.size(); dim-- > 0;) {
            AstVarScope* const idxp = idxps[dim];
            AstLoop* const loopp = new AstLoop{flp};
            loopp->unroll(VOptionBool::OPT_FALSE);
            const uint32_t elements = dims[dim]->elementsConst();
            loopp->addStmtsp(new AstLoopTest{
                flp, loopp, new AstGt{flp, new AstConst{flp, elements}, readp(idxp)}});
            loopp->addStmtsp(stmtsp);
            loopp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, idxp, VAccess::WRITE},
                                           new AstAdd{flp, readp(idxp), new AstConst{flp, 1U}}});
            stmtsp = new AstAssign{flp, new AstVarRef{flp, idxp, VAccess::WRITE},
                                   new AstConst{flp, 0U}};
            stmtsp->addNext(loopp);
        }
        return stmtsp;
    }

    // Create dispatch wrapper
    AstCFunc* makeDpiExportDispatcher(AstNodeFTask* const nodep, AstVar* const rtnvarp) {
        // Verilog name has __ conversion and other tricks, to match DPI C code, back that out
        FileLine* const flp = nodep->fileline();
        const std::string cname = AstNode::prettyName(nodep->cname());
        checkLegalCIdentifier(nodep, cname);
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();
        const std::string rtnType = rtnvarp ? rtnvarp->dpiArgType(true, true) : "";
        // The function we are building
        AstCFunc* const funcp = new AstCFunc{flp, cname, m_scopep, rtnType};
        funcp->dpiExportDispatcher(true);
        funcp->dpiContext(nodep->dpiContext());
        funcp->dontCombine(true);
        funcp->entryPoint(true);
        funcp->isStatic(true);
        funcp->protect(false);
        funcp->cname(cname);
        // Add DPI Export to top, since it's a global function
        m_topScopep->scopep()->addBlocksp(funcp);
        // Check the arguments before converting them
        if (!makePortList(nodep, funcp)) return nullptr;

        // Note this function may dispatch on a different class.
        // Thus we need to be careful not to assume a particular function layout.
        //
        // Func numbers must be the same for each function, even when there are
        // completely different models with the same function name.
        // Thus we can't just use a constant computed at Verilation time.
        // We could use 64-bits of a MD5/SHA hash rather than a string here,
        // but the compare is only done on first call then memoized, so
        // it's not worth optimizing.

        // Peramble - fetch the exproted function from the scope table
        AstCStmt* const prep = new AstCStmt{flp};
        funcp->addStmtsp(prep);
        // Static doesn't need save-restore as if below will re-fill proper value
        prep->add("static int __Vfuncnum = -1;\n");
        // First time init (faster than what the compiler does if we did a singleton
        prep->add("if (VL_UNLIKELY(__Vfuncnum == -1)) {\n");
        prep->add("__Vfuncnum = Verilated::exportFuncNum(\"" + nodep->cname() + "\");\n");
        prep->add("}\n");
        // If the find fails, it will throw an error
        prep->add("const VerilatedScope* const __Vscopep = Verilated::dpiScope();\n");
        // If 'dpiScope()' fails and '__Vscopep' is null; the exportFind function throws an error
        // If __Vcb is null the exportFind function throws and error
        const std::string cbtype
            = VIdProtect::protect(v3Global.opt.prefix() + "__Vcb_" + nodep->cname() + "_t");
        prep->add(cbtype + " __Vcb = reinterpret_cast<" + cbtype
                  + ">(VerilatedScope::exportFind(__Vscopep, __Vfuncnum));");

        // Convert input/inout DPI arguments to Internal types, and construct the call
        AstCStmt* const callp = new AstCStmt{flp};
        const auto addFuncArg = [&](AstVar* portp) -> AstVarScope* {
            // No createDpiTemp; we make a real internal variable instead
            AstVarScope* const vscp = createFuncVar(funcp, portp->name() + tmpSuffixp, portp);
            // No information exposure; is already visible in import/export func template
            vscp->varp()->protect(false);
            portp->protect(false);
            // Add argument to call
            const VAccess access = portp->direction().pinAccess();
            callp->add(", ");
            callp->add(new AstVarRef{portp->fileline(), vscp, access});
            return vscp;
        };
        // Call callback
        callp->add("(*__Vcb)(");
        // First argument is the Syms
        callp->add("(" + EmitCUtil::symClassName() + "*)(__Vscopep->symsp())");
        // Add function arguments
        AstNode* outCvtsp = nullptr;  // Conversions of output/inout arguments, after the call
        for (AstNode* const stmtp : nodep->stmtspList()) {
            AstVar* const portp = VN_CAST(stmtp, Var);
            if (!portp) continue;
            if (!portp->isIO()) continue;
            if (portp->isFuncReturn()) continue;
            if (portp == rtnvarp) continue;  // Handled below
            // Add argument to call
            AstVarScope* const outvscp = addFuncArg(portp);
            const bool isStruct = portp->dtypep()->containsUnpackedStruct();
            if (portp->isWritable()) {
                outCvtsp = AstNode::addNext(
                    outCvtsp, isStruct ? createDpiArgCvt(funcp, outvscp, portp->name(), true)
                                       : createAssignInternalToDpi(portp, true, tmpSuffixp, ""));
            }
            if (!portp->isNonOutput()) continue;
            // Convert input/inout arguments to dpi type
            const std::string deref
                = portp->isInout() && !isStruct  //
                          && portp->dtypep()->isDpiPrimitive()  //
                          && portp->dtypep()->skipRefp()->dimensions(false).second == 0
                      ? "*"
                      : "";
            funcp->addStmtsp(createDpiArgCvt(funcp, outvscp, deref + portp->name(), false));
        }
        // Return value argument goes last
        if (rtnvarp) addFuncArg(rtnvarp);
        // Close statement
        callp->add(");");
        // Call the user function
        funcp->addStmtsp(callp);
        // Convert output/inout arguments back to internal type
        if (outCvtsp) funcp->addStmtsp(outCvtsp);
        // Convert return value
        if (rtnvarp) {
            funcp->addStmtsp(createDpiTemp(rtnvarp, ""));
            funcp->addStmtsp(createAssignInternalToDpi(rtnvarp, false, tmpSuffixp, ""));
            const std::string index = rtnvarp->dtypep()->isDpiPrimitive() ? "" : "[0]";
            funcp->addStmtsp(new AstCStmt{flp, "return " + rtnvarp->name() + index + ";"});
        }
        return funcp;
    }

    AstCFunc* makeDpiImportPrototype(AstNodeFTask* nodep, AstVar* rtnvarp) {
        // Verilog name has __ conversion and other tricks, to match DPI C code, back that out
        const string name = AstNode::prettyName(nodep->cname());
        checkLegalCIdentifier(nodep, name);
        // Tasks (but not void functions) return a boolean 'int' indicating disabled
        const string rtnType = rtnvarp            ? rtnvarp->dpiArgType(true, true)
                               : nodep->dpiTask() ? "int"
                                                  : "";
        AstCFunc* const funcp = new AstCFunc{nodep->fileline(), name, m_scopep, rtnType};
        funcp->dpiContext(nodep->dpiContext());
        funcp->dpiImportPrototype(true);
        funcp->dontCombine(true);
        funcp->entryPoint(false);
        funcp->isMethod(false);
        funcp->protect(false);
        funcp->dpiPure(nodep->dpiPure());

        const int cost = static_cast<int>(V3Control::getProfileData(funcp->name()));
        m_statHierDpisWithCosts += (cost != 0);
        funcp->cost(cost);

        // Add DPI Import to top, since it's a global function
        m_topScopep->scopep()->addBlocksp(funcp);
        funcp->dpiCDecl(nodep->dpiCDecl());
        if (!makePortList(nodep, funcp)) return nullptr;
        return funcp;
    }

    AstCFunc* getDpiFunc(AstNodeFTask* nodep, AstVar* rtnvarp) {
        UASSERT_OBJ(nodep->dpiImport() || nodep->dpiExport(), nodep, "Not a DPI function");
        // Compute unique signature of this DPI function
        const string signature = dpiSignature(nodep, rtnvarp);
        // Only create one DPI Import prototype or DPI Export entry point for each unique cname as
        // it is illegal for the user to attach multiple tasks with different signatures to one DPI
        // cname.
        const auto pair = m_dpiNames.emplace(std::piecewise_construct,  //
                                             std::forward_as_tuple(nodep->cname()),
                                             std::forward_as_tuple(nodep, signature, nullptr));
        if (pair.second) {
            // First time encountering this cname. Create Import prototype / Export entry point
            AstCFunc* const funcp = nodep->dpiExport() ? makeDpiExportDispatcher(nodep, rtnvarp)
                                                       : makeDpiImportPrototype(nodep, rtnvarp);
            std::get<2>(pair.first->second) = funcp;
            return funcp;
        } else {
            // Seen this cname import before. Check if it's the same prototype.
            const AstNodeFTask* firstNodep;
            string firstSignature;
            AstCFunc* firstFuncp;
            std::tie(firstNodep, firstSignature, firstFuncp) = pair.first->second;
            if (signature != firstSignature) {
                // Different signature, so error.
                nodep->v3error("Duplicate declaration of DPI function with different signature: '"
                               << nodep->cname() << "'\n"
                               << nodep->warnContextPrimary() << '\n'
                               << nodep->warnMore()  //
                               << "... New signature:      " << signature << '\n'  //
                               << firstNodep->warnOther()
                               << "... Original signature: " << firstSignature << '\n'  //
                               << firstNodep->warnContextSecondary());
                return nullptr;
            } else {
                // Same signature, return the previously created CFunc
                return firstFuncp;
            }
        }
    }

    static bool makePortList(AstNodeFTask* nodep, AstCFunc* dpip) {
        bool allOk = true;
        // Copy nodep's list of function I/O to the new dpip c function
        for (AstNode* const stmtp : nodep->stmtspList()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    // Move it to new function
                    AstVar* const newPortp = portp->cloneTree(false);
                    newPortp->funcLocal(true);
                    dpip->addArgsp(newPortp);
                    // Unpacked structures were checked by checkDpiStruct
                    if (!portp->basicp() && !portp->dtypep()->containsUnpackedStruct()) {
                        allOk = false;
                        portp->v3warn(
                            E_UNSUPPORTED,
                            "Unsupported: DPI argument of type "
                                << portp->dtypep()->prettyTypeName() << '\n'
                                << portp->warnMore()
                                << "... For best portability, use bit, byte, int, or longint");
                        // We don't warn on logic either, although the 4-stateness is lost.
                        // That's what other simulators do.
                    }
                }
            }
        }
        return allOk;
    }

    // Whether C code, and the C++ Verilator generates, can use 'name' as an identifier
    static bool isDpiCIdentifier(const string& name) {
        return !name.empty() && VString::isIdentifier(name)
               && !std::isdigit(name[0])
               // C reserves names beginning with '__', or '_' and an uppercase letter
               && !(name[0] == '_' && (name[1] == '_' || std::isupper(name[1])))
               && V3LanguageWords::isKeyword(name).empty();
    }

    // Check DPI can pass the unpacked structure 'sdtypep' of argument 'portp', else report.
    // If 'nested' in another structure, it may be anonymous, as declared where used.
    bool checkDpiStruct(const AstVar* portp, const AstStructDType* sdtypep, bool nested) {
        const std::string name = sdtypep->dpiName();
        if (!(nested && name.empty()) && !isDpiCIdentifier(name)) {
            portp->v3warn(E_UNSUPPORTED,
                          "Unsupported: DPI argument of unpacked structure type "
                          "without a typedef name usable in C: "
                              << sdtypep->prettyDTypeNameQ(true) << "\n"
                              << portp->warnMore()
                              << "... Suggest use a typedef with a C identifier name");
            return false;
        }
        for (const AstMemberDType* const itemp : sdtypep->memberspList()) {
            if (!isDpiCIdentifier(itemp->prettyName())) {
                portp->v3warn(E_UNSUPPORTED, "Unsupported: DPI argument of unpacked structure "
                                             "type with member name not usable in C: "
                                                 << itemp->prettyNameQ());
                return false;
            }
            // Of the types of arguments, or unpacked arrays of them (IEEE 1800-2023 35.5.6)
            const AstNodeDType* dtypep = itemp->subDTypep()->skipRefp();
            while (const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType)) {
                dtypep = arrayp->subDTypep()->skipRefp();
            }
            const AstNodeUOrStructDType* const subp = VN_CAST(dtypep, NodeUOrStructDType);
            const AstBasicDType* const basicp = VN_CAST(dtypep, BasicDType);
            // Neither an unpacked array nor an unpacked structure, as createDpiScalarCvt converts
            const bool isScalar = (subp && subp->packed()) || VN_IS(dtypep, PackArrayDType)
                                  || (basicp && !basicp->isEvent());
            if (dtypep->containsUnpackedStruct()) {
                if (!checkDpiStruct(portp, VN_AS(dtypep, StructDType), true)) return false;
            } else if (!isScalar) {
                portp->v3error("DPI argument " << portp->prettyNameQ()
                                               << " has unpacked structure member "
                                               << itemp->prettyNameQ() << " of type "
                                               << itemp->subDTypep()->prettyDTypeNameQ(true)
                                               << ", which DPI does not allow"
                                               << " (IEEE 1800-2023 35.5.6)");
                return false;
            }
        }
        // C has no scopes, so cannot have different structures of the same name
        if (name.empty()) return true;
        const AstStructDType* const firstp = m_dpiStructs.emplace(name, sdtypep).first->second;
        if (firstp->dpiTypedef() == sdtypep->dpiTypedef()) return true;
        portp->v3warn(E_UNSUPPORTED, "Unsupported: DPI arguments of different unpacked "
                                     "structure types with the same name '"
                                         << name << "'\n"
                                         << portp->warnContextPrimary() << '\n'
                                         << firstp->warnOther()
                                         << "... Location of the other structure type\n"
                                         << firstp->warnContextSecondary());
        return false;
    }

    // Check DPI can pass the unpacked structure arguments of 'nodep', else report
    bool checkDpiStructArgs(const AstNodeFTask* nodep) {
        bool allOk = true;
        for (const AstNode* const stmtp : nodep->stmtspList()) {
            const AstVar* const portp = VN_CAST(stmtp, Var);
            if (portp && portp->isIO() && portp->dtypep()->containsUnpackedStruct()) {
                allOk = checkDpiStruct(portp, VN_AS(portp->dtypep()->elemDTypep(), StructDType),
                                       false)
                        && allOk;
            }
        }
        return allOk;
    }

    void bodyDpiImportFunc(AstNodeFTask* nodep, AstVarScope* rtnvscp, AstCFunc* cfuncp,
                           AstCFunc* dpiFuncp) {
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();

        if (v3Global.opt.profExec()) {
            cfuncp->addStmtsp(AstCStmt::profExecSectionPush(nodep->fileline(), "dpiimports"));
        }

        // Convert input/inout arguments to DPI types
        string args;
        for (AstNode* const stmtp : cfuncp->argspList()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                AstVarScope* const portvscp
                    = VN_AS(portp->user2p(), VarScope);  // Remembered when we created it earlier
                if (portp->isIO() && !portp->isFuncReturn() && portvscp != rtnvscp
                    && portp->name() != "__Vscopep"  // Passed to dpiContext, not callee
                    && portp->name() != "__Vfilenamep" && portp->name() != "__Vlineno") {

                    if (args != "") args += ", ";

                    if (portp->isDpiOpenArray()) {
                        AstNodeDType* const dtypep = portp->dtypep()->skipRefp();
                        UASSERT_OBJ(!VN_IS(dtypep, DynArrayDType) && !VN_IS(dtypep, QueueDType),
                                    portp,
                                    "Passing dynamic array or queue as actual argument to DPI "
                                    "open array is not yet supported");
                        // Ideally we'd make a table of variable
                        // characteristics, and reuse it wherever we can
                        // At least put them into the module's CTOR as static?
                        const string propName = portp->name() + "__Vopenprops";
                        const string propCode = portp->vlPropDecl(propName);
                        cfuncp->addStmtsp(new AstCStmt{portp->fileline(), propCode});
                        //
                        // At runtime we need the svOpenArrayHandle to
                        // point to this task & thread's data, in addition
                        // to static info about the variable
                        const string name = portp->name() + "__Vopenarray";
                        const string varCode
                            = ("VerilatedDpiOpenVar "
                               // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                               + name + " (&" + propName + ", &" + portp->name() + ");\n");
                        cfuncp->addStmtsp(new AstCStmt{portp->fileline(), varCode});
                        args += "&" + name;
                    } else {
                        // Unpacked structures are passed by reference from a C array
                        const bool isStruct = portp->dtypep()->containsUnpackedStruct();
                        if (portp->isWritable() && !isStruct
                            && portp->dtypep()->isDpiPrimitive()) {
                            if (!VN_IS(portp->dtypep()->skipRefp(), UnpackArrayDType)) args += "&";
                        }

                        args += portp->name() + tmpSuffixp;

                        cfuncp->addStmtsp(createDpiTemp(portp, tmpSuffixp));
                        if (portp->isNonOutput()) {
                            cfuncp->addStmtsp(
                                isStruct
                                    ? createDpiArgCvt(cfuncp, portvscp, portp->name() + tmpSuffixp,
                                                      true)
                                    : createAssignInternalToDpi(portp, false, "", tmpSuffixp));
                        }
                    }
                }
            }
        }

        // Store context, if needed
        if (nodep->dpiContext()) {
            const string stmt = "Verilated::dpiContext(__Vscopep, __Vfilenamep, __Vlineno);";
            cfuncp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
        }

        {  // Call the imported function
            AstCCall* const callp = new AstCCall{nodep->fileline(), dpiFuncp};
            callp->dtypeSetVoid();
            callp->argTypes(args);
            if (rtnvscp) {
                // If it has a return value, capture it
                cfuncp->addStmtsp(createDpiTemp(rtnvscp->varp(), tmpSuffixp));
                const std::string sel = rtnvscp->varp()->dtypep()->isDpiPrimitive() ? "" : "[0]";
                AstCStmt* const cstmtp = new AstCStmt{nodep->fileline()};
                cstmtp->add(rtnvscp->varp()->name() + tmpSuffixp + sel);  // LHS
                cstmtp->add(" = ");
                cstmtp->add(callp);  // RHS
                cstmtp->add(";");
                cfuncp->addStmtsp(cstmtp);
            } else {
                // Othervise just call it
                cfuncp->addStmtsp(callp->makeStmt());
            }
        }

        // Convert output/inout arguments back to internal type
        for (AstNode* const stmtp : cfuncp->argspList()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                portp->protect(false);  // No additional exposure - already part of shown proto
                if (portp->isIO() && (portp->isWritable() || portp->isFuncReturn())
                    && !portp->isDpiOpenArray()) {
                    AstVarScope* const portvscp = VN_AS(
                        portp->user2p(), VarScope);  // Remembered when we created it earlier
                    cfuncp->addStmtsp(
                        createDpiArgCvt(cfuncp, portvscp, portp->name() + tmpSuffixp, false));
                }
            }
        }

        if (v3Global.opt.profExec()) {
            cfuncp->addStmtsp(AstCStmt::profExecSectionPop(nodep->fileline(), "dpiimports"));
        }
    }

    AstVarScope* getDpiExporTrigger() {
        AstNetlist* const netlistp = v3Global.rootp();
        AstVarScope* dpiExportTriggerp = netlistp->dpiExportTriggerp();
        if (!dpiExportTriggerp) {
            // Create the global DPI export trigger flag the first time we encounter a DPI export.
            // This flag is set any time a DPI export is invoked, and cleared at the end of eval.
            dpiExportTriggerp = m_topScopep->createTemp("__Vdpi_export_trigger", 1);
            netlistp->dpiExportTriggerp(dpiExportTriggerp);
        }
        return dpiExportTriggerp;
    }

    AstCFunc* makeUserFunc(AstNodeFTask* nodep, bool ftaskNoInline) {
        // Given a already cloned node, make a public C function, or a non-inline C function
        // Probably some of this work should be done later, but...
        // should the type of the function be bool/uint32/64 etc (based on lookup) or IData?
        AstNode::user2ClearTree();
        AstVar* rtnvarp = nullptr;
        if (nodep->isFunction()) {
            AstVar* const portp = VN_AS(nodep->fvarp(), Var);
            UASSERT_OBJ(portp, nodep, "function without function output variable");
            UASSERT_OBJ(portp->isFuncReturn(), nodep, "Not marked as function return var");
            if (nodep->dpiImport() || nodep->dpiExport()) {
                AstBasicDType* const bdtypep = portp->dtypep()->basicp();
                if (!bdtypep) {
                    portp->v3error("DPI function may not return type "
                                   << portp->dtypep()->prettyDTypeNameQ(true)
                                   << " (IEEE 1800-2023 35.5.5)");
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return nullptr;
                }
                if (!portp->dtypep()->isDpiPrimitive()) {
                    if (portp->dtypep()->isDpiBitVec() && portp->width() > 32) {
                        portp->v3error("DPI function may not return a > 32 bits wide type "
                                       "other than basic types.\n"
                                       + portp->warnMore()
                                       + "... Suggest make it an output argument instead?");
                    }
                    if (portp->dtypep()->isDpiLogicVec()) {
                        portp->v3error("DPI function may not return a 4-state type "
                                       "other than a single 'logic' (IEEE 1800-2023 35.5.5)");
                    }
                }
            } else if (nodep->taskPublic()) {
                if (portp->isWide()) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Public functions with return > 64 bits wide.\n"
                                      + nodep->warnMore()
                                      + "... Suggest make it an output argument instead?");
                }
            }

            if (ftaskNoInline || nodep->dpiExport()) {
                portp->funcReturn(false);  // Converting return to 'outputs'
            }
            unlinkAndClone(nodep, portp, false);
            rtnvarp = portp;
            rtnvarp->funcLocal(true);
            rtnvarp->noCReset(true);  // As made for port in V3LinkResolve
            rtnvarp->name(rtnvarp->name()
                          + "__Vfuncrtn");  // Avoid conflict with DPI function name
            if (nodep->dpiImport() || nodep->dpiExport()) rtnvarp->protect(false);
        }

        // Create/pick up the DPI CFunc for DPI Import/ DPI Export.
        AstCFunc* dpiFuncp = nullptr;
        if (nodep->dpiImport() || nodep->dpiExport()) {
            UASSERT_OBJ(!(nodep->dpiOpenParent() && nodep->dpiOpenChild()), nodep,
                        "DPI task should not be both parent and child");
            dpiFuncp = checkDpiStructArgs(nodep) ? getDpiFunc(nodep, rtnvarp) : nullptr;
            if (!dpiFuncp || (nodep->dpiImport() && nodep->dpiOpenParent())) {
                // No need to make more than just the DPI Import prototype, the children will
                // create the wrapper implementations.
                if (rtnvarp) VL_DO_DANGLING(pushDeletep(rtnvarp), rtnvarp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return nullptr;
            }
        }

        AstVarScope* rtnvscp = nullptr;
        if (rtnvarp) {
            rtnvscp = new AstVarScope{rtnvarp->fileline(), m_scopep, rtnvarp};
            m_scopep->addVarsp(rtnvscp);
            rtnvarp->user2p(rtnvscp);
        }

        string prefix;
        if (nodep->dpiImport()) {
            prefix = "__Vdpiimwrap_";
        } else if (nodep->dpiExport()) {
            prefix = "__Vdpiexp_";
        } else if (ftaskNoInline) {
            prefix = "__VnoInFunc_";
        }
        // Unless public, v3Descope will not uniquify function names even if duplicate per-scope,
        // so make it unique now.
        string suffix;  // So, make them unique
        if (!nodep->taskPublic() && !nodep->classMethod()) suffix = "_" + m_scopep->nameDotless();
        const string name = ((nodep->name() == "new") ? "new" : prefix + nodep->name() + suffix);
        AstCFunc* const cfuncp = new AstCFunc{
            nodep->fileline(), name, m_scopep,
            ((nodep->taskPublic() && rtnvarp) ? rtnvarp->cPubArgType(true, true) : "")};
        // It's ok to combine imports because this is just a wrapper;
        // duplicate wrappers can get merged.
        cfuncp->dontCombine(!nodep->dpiImport());
        cfuncp->entryPoint(!nodep->dpiImport());
        cfuncp->funcPublic(nodep->taskPublic());
        cfuncp->dpiContext(nodep->dpiContext());
        cfuncp->dpiExportImpl(nodep->dpiExport());
        cfuncp->dpiImportWrapper(nodep->dpiImport());
        cfuncp->recursive(nodep->recursive());
        // Hardcoded based on UVM usage; TODO make a verilated_std.vlt control for these
        cfuncp->unlikely(nodep->name() == "uvm_report_error" || nodep->name() == "uvm_report_info"
                         || nodep->name() == "uvm_report_fatal"
                         || nodep->name() == "uvm_report_warning");
        if (nodep->dpiImport() || nodep->dpiExport()) {
            cfuncp->isStatic(true);
            cfuncp->isLoose(true);
        } else {
            cfuncp->isStatic(false);
        }
        cfuncp->isVirtual(nodep->isVirtual());
        cfuncp->dpiPure(nodep->dpiPure());
        if (nodep->name() == "new") cfuncp->isConstructor(true);
        if (nodep->isCovergroupSample()) cfuncp->isCovergroupSample(true);
        if (cfuncp->dpiExportImpl()) cfuncp->cname(nodep->cname());

        if (cfuncp->dpiImportWrapper()) cfuncp->cname(nodep->cname());

        const bool needSyms
            = nodep->needsSyms()
              && ((!nodep->dpiImport() && !nodep->taskPublic()) || v3Global.opt.profExec());
        if (needSyms) cfuncp->argTypes(EmitCUtil::symClassVar());

        if (!nodep->dpiImport() && !nodep->taskPublic()) {
            // Need symbol table
            if (cfuncp->isConstructor()) {
                bool isInterfaceClass = false;
                if (const AstClass* const classp = VN_CAST(m_modp, Class)) {
                    isInterfaceClass = classp->isInterfaceClass();
                }
                if (!isInterfaceClass) {
                    const string stmt = VIdProtect::protect("_ctor_var_reset") + "(vlSymsp);";
                    cfuncp->addStmtsp(
                        new AstCStmt{nodep->fileline(), stmt, VCStmtType::CTOR_VAR_RESET_CALL});
                }
            }
        }
        if (nodep->dpiContext()) {
            // First three args go to dpiContext call
            createInputVar(cfuncp, "__Vscopep", VBasicDTypeKwd::SCOPEPTR);
            createInputVar(cfuncp, "__Vfilenamep", VBasicDTypeKwd::CHARPTR);
            createInputVar(cfuncp, "__Vlineno", VBasicDTypeKwd::INT);
        }

        if (nodep->dpiExport()) {
            AstScopeName* const snp = nodep->scopeNamep();
            UASSERT_OBJ(snp, nodep, "Missing scoping context");
            snp->dpiExport(true);
            snp->unlinkFrBack();
            cfuncp->scopeNamep(snp);
        }

        // Create list of arguments and move to function
        for (AstNode* const stmtp : nodep->stmtspList()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isParam() && VN_IS(portp->valuep(), ConsArray)) {
                    // Move array parameters in functions into constant pool
                    portp->unlinkFrBack();
                    pushDeletep(portp);
                    portp->user2p(constPoolTable(portp));
                } else {
                    if (portp->isIO()) {
                        // Move it to new function
                        unlinkAndClone(nodep, portp, false);
                        portp->funcLocal(true);
                        if (portp->valuep()) pushDeletep(portp->valuep()->unlinkFrBack());
                        cfuncp->addArgsp(portp);
                        // Pass inputs to DPI import wrappers by reference, unless fits in register
                        if (cfuncp->dpiImportWrapper() && portp->isReadOnly()) {
                            AstNodeDType* const dtypep = portp->dtypep()->skipRefp();
                            if (dtypep->isCompound() || dtypep->isWide()) {
                                portp->direction(VDirection::CONSTREF);
                            }
                        }
                    } else {
                        // "Normal" variable, mark inside function
                        portp->funcLocal(true);
                    }
                    AstVarScope* const newvscp
                        = new AstVarScope{portp->fileline(), m_scopep, portp};
                    m_scopep->addVarsp(newvscp);
                    portp->user2p(newvscp);
                }
            }
        }

        // Fake output variable if was a function.  It's more efficient to
        // have it last, rather than first, as the C compiler can sometimes
        // avoid copying variables when calling shells if argument 1
        // remains argument 1 (which it wouldn't if a return got added).
        if (rtnvarp) cfuncp->addArgsp(rtnvarp);

        // Move body
        AstNode* bodysp = nodep->stmtsp();
        if (bodysp) {
            unlinkAndClone(nodep, bodysp, true);
            AstBegin* const tempp
                = new AstBegin{nodep->fileline(), "[EditWrapper]", bodysp, false};
            VL_DANGLING(bodysp);
            // If we cloned due to recursion, now need to rip out the ports
            // (that remained in place) then got cloned
            for (AstNode* const stmtp : tempp->stmtspList()) {
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    if (portp->isIO()) VL_DO_DANGLING(pushDeletep(portp->unlinkFrBack()), portp);
                }
            }
            if (tempp->stmtsp()) cfuncp->addStmtsp(tempp->stmtsp()->unlinkFrBackWithNext());
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        if (nodep->dpiImport()) bodyDpiImportFunc(nodep, rtnvscp, cfuncp, dpiFuncp);

        // Return statement
        if (rtnvscp && nodep->taskPublic()) {
            cfuncp->addStmtsp(new AstCReturn{
                rtnvscp->fileline(), new AstVarRef{rtnvscp->fileline(), rtnvscp, VAccess::READ}});
        }
        // Replace variable refs
        relink(cfuncp);

        if (cfuncp->dpiExportImpl()) {
            // Mark all non-local variables written by the DPI exported function as being updated
            // by DPI exports. This ensures correct ordering and change detection later.

            // Mark non-local variables written by the exported function
            bool writesNonLocals = false;
            cfuncp->foreach([&writesNonLocals](AstVarRef* refp) {
                AstVar* const varp = refp->varScopep()->varp();
                // We are ignoring function locals as they should not be referenced anywhere
                // outside the enclosing AstCFunc, hence they are irrelevant for code ordering.
                if (varp->isFuncLocal()) return;
                // Check if written
                if (refp->access().isWriteOrRW()) {
                    // Mark it as written by DPI export
                    varp->setWrittenByDpi();
                    // Remember we had some
                    writesNonLocals = true;
                }
                // Check if read
                if (refp->access().isReadOrRW()) {
                    // Mark it as read by DPI export
                    varp->setReadByDpi();
                }
            });

            // If this DPI export writes some non-local variables, set the DPI Export Trigger flag
            // in the function.
            if (writesNonLocals) {
                AstVarScope* const dpiExportTriggerp = getDpiExporTrigger();
                FileLine* const flp = cfuncp->fileline();

                // Set DPI export trigger flag every time the DPI export is called.
                AstAssign* const assignp
                    = new AstAssign{flp, new AstVarRef{flp, dpiExportTriggerp, VAccess::WRITE},
                                    new AstConst{flp, AstConst::BitTrue{}}};

                // Add as first statement (to avoid issues with early returns) to exported function
                cfuncp->prependStmtsp(assignp);

                // With --sc, also wake the SystemC wrapper: it cannot see the flag, and may
                // otherwise sleep until its next timed slot. (usesTiming() is not known yet.)
                if (v3Global.opt.systemC()) {
                    assignp->addNextHere(new AstCStmt{
                        flp, "vlSymsp->__Vm_wakeEvent.notify(sc_core::SC_ZERO_TIME);\n"});
                }
            }
        }

        // Mark the fact that this function allocates std::process
        if (nodep->needProcess()) cfuncp->setNeedProcess();

        // Delete rest of cloned task and return new func
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        UINFOTREE(9, cfuncp, "", "userFunc");
        return cfuncp;
    }

    void iterateIntoFTask(AstNodeFTask* nodep) {
        // Iterate into the FTask we are calling.  Note it may be under a different
        // scope then the caller, so we need to restore state.
        VL_RESTORER(m_scopep);
        VL_RESTORER(m_modp);
        VL_RESTORER(m_insStmtp);
        m_scopep = m_statep->getScope(nodep);
        m_modp = m_scopep->modp();
        iterate(nodep);
    }
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        UINFOTREE(9, nodep, "", "newstmt");
        UASSERT_OBJ(m_insStmtp, nodep, "Function call not underneath a statement");
        UINFOTREE(9, newp, "", "newfunc");
        m_insStmtp->addHereThisAsNext(newp);
    }
    void processArgs(AstNodeFTaskRef* nodep) {
        // Create a fresh variable for each concat array present in pins list
        for (AstArg* const argp : nodep->argspList()) {
            AstConsArray* const arrayp = VN_CAST(argp->exprp(), ConsArray);
            if (!arrayp) continue;

            FileLine* const flp = arrayp->fileline();
            AstVarScope* const substvscp = m_consArrayTmps.make(flp, m_scopep, arrayp->dtypep());
            substvscp->varp()->isInternal(true);

            AstAssign* const assignp
                = new AstAssign{flp, new AstVarRef{arrayp->fileline(), substvscp, VAccess::WRITE},
                                arrayp->unlinkFrBack()};

            AstExprStmt* const exprstmtp = new AstExprStmt{
                flp, assignp, new AstVarRef{arrayp->fileline(), substvscp, VAccess::READ}};
            argp->exprp(exprstmtp);
        }
    }

    bool isIfaceLocalImpure(AstNodeFTask* nodep, AstNode* impurep) {
        const AstScope* const scopep = m_statep->getScope(nodep);
        if (!TaskStateVisitor::isIfaceFTaskScope(scopep)) return false;

        const AstVarRef* const refp = VN_CAST(impurep, VarRef);
        if (!refp || !refp->varScopep()) return false;

        return refp->varScopep()->scopep() == scopep;
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
        UASSERT_OBJ(!m_insStmtp, nodep, "Didn't finish out last statement");
    }
    void visit(AstWith* nodep) override {
        if (nodep->user1SetOnce()) {
            // Make sure that the return expression is converted only once
            return;
        }
        AstNodeExpr* const withExprp = VN_AS(nodep->exprp()->unlinkFrBack(), NodeExpr);
        nodep->addExprp(new AstCReturn{withExprp->fileline(), withExprp});
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
        UASSERT_OBJ(!m_insStmtp, nodep, "Didn't finish out last statement");
    }
    void visit(AstCNew* nodep) override {
        VL_RESTORER(m_inNew);
        m_inNew = true;
        iterateChildren(nodep);
    }
    // If taskp is a getter, return the reference to the member variable it returns
    static AstVarRef* getterVarRefp(AstNodeFTask* taskp) {
        AstNode* stmtp = taskp->stmtsp();
        // Skip the default initialization of the function's return value
        const AstVar* const fvarp = VN_AS(taskp->fvarp(), Var);
        if (const AstAssign* const initp = VN_CAST(stmtp, Assign)) {
            const AstVarRef* const lvarrefp = VN_CAST(initp->lhsp(), VarRef);
            if (lvarrefp && lvarrefp->varp() == fvarp && VN_IS(initp->rhsp(), Const))
                stmtp = initp->nextp();
        }
        // Arguments are statements too, so a function with any is rejected here
        const AstAssign* const assignp = VN_CAST(stmtp, Assign);
        if (!assignp || assignp->nextp()) return nullptr;
        AstVarRef* const rhsp = VN_CAST(assignp->rhsp(), VarRef);
        if (!rhsp || !rhsp->varp()->isClassMember()) return nullptr;
        const AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef);
        if (!lhsp || lhsp->varp() != fvarp) return nullptr;
        if (!fvarp->dtypep()->skipRefp()->sameTree(rhsp->varp()->dtypep()->skipRefp())) {
            return nullptr;
        }
        return rhsp;
    }
    // Replace call with a read of the member variable returned by the getter, if possible
    bool replaceGetterCall(AstNodeFTaskRef* nodep) {
        if (!v3Global.opt.fInlineGetters() || m_inSensesp) return false;
        // Calls as statements keep the existing path, which handles the ignored return value
        if (VN_IS(nodep->backp(), StmtExpr)) return false;
        AstNodeFTask* const taskp = nodep->taskp();
        if (!taskp->isFunction() || !taskp->classMethod() || taskp->isVirtual()
            || taskp->taskPublic()) {
            return false;
        }
        AstVarRef* const readp = getterVarRefp(taskp);
        if (!readp) return false;
        AstNodeExpr* newp;
        AstMethodCall* const mcallp = VN_CAST(nodep, MethodCall);
        if (readp->varp()->lifetime().isStatic()) {
            // The object expression is not needed, but must not be dropped if it has side effects
            if (mcallp && !mcallp->fromp()->isPure()) return false;
            newp = readp->cloneTree(false);
        } else if (mcallp) {
            // A derived class receiver might shadow the member by name, and the emitted
            // access is by name, so only use the exact class that owns the variable
            const AstClassRefDType* const dtp
                = VN_CAST(mcallp->fromp()->dtypep()->skipRefp(), ClassRefDType);
            if (!dtp || dtp->classp() != readp->varScopep()->scopep()->modp()) return false;
            newp = new AstMemberSel{nodep->fileline(), mcallp->fromp()->unlinkFrBack(),
                                    readp->varp()};
        } else {
            // Implicit 'this' call from another method of the class
            newp = readp->cloneTree(false);
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        ++m_statGetters;
        // No need to iterate the object expression; V3LiftExpr already moved calls out of it
        return true;
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (m_inSensesp && !nodep->isPure()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Impure function calls in sensitivity lists");
            nodep->taskp(nullptr);  // So V3Broken doesn't complain
            return;
        }
        // Includes handling AstMethodCall, AstNew
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked?");
        if (replaceGetterCall(nodep)) return;
        iterateIntoFTask(nodep->taskp());  // First, do hierarchical funcs
        if (m_statep->ftaskNoInline(nodep->taskp()) && !m_statep->ftaskCFuncp(nodep->taskp())) {
            // An earlier error (e.g. a DPI import declared twice with conflicting
            // signatures) prevented creating the function, so remove the call
            UASSERT_OBJ(V3Error::errorCount(), nodep, "No non-inline task, but no error issued");
            if (VN_IS(nodep->backp(), StmtExpr)) {
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            } else {
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalseErroring{}});
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
            return;
        }
        UINFO(4, " FTask REF   " << nodep);
        UINFOTREE(9, nodep, "", "inlfunc");
        UASSERT_OBJ(m_scopep, nodep, "func ref not under scope");
        // Create output variable
        AstVarScope* outvscp = nullptr;
        if (nodep->taskp()->isFunction()) {
            AstVar* const fvarp = VN_AS(nodep->taskp()->fvarp(), Var);
            // If the call is on the RHS of a simple assignment 'lhs = call()',
            // the LHS variable can be reused as the output variable iff it has
            // the same type, and the function does not read the output variable itself.
            // This can be proven cheaply if the LHS is an automatic variable and the
            // function does not have any ref arguments. This arises a lot after V3LiftExpr.
            if (AstAssign* const assignp = VN_CAST(nodep->backp(), Assign)) {
                if (AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef)) {
                    AstVarScope* const vscp = lhsp->varScopep();
                    if (vscp->varp()->lifetime().isAutomatic()
                        && vscp->varp()->dtypep()->skipRefp()->sameTree(
                            fvarp->dtypep()->skipRefp())
                        && !hasRefArgument(nodep->taskp())) {
                        outvscp = vscp;
                    }
                }
            }
            // Otherwise create a new variable for the result
            if (!outvscp) outvscp = createVarScope(nodep, fvarp, "__Vfuncout");
        }
        // Create cloned statements
        AstNode* beginp;
        AstCNew* cnewp = nullptr;
        // getScope() is safe here: TaskStateVisitor stamped all FTask scopes before this pass.
        const bool virtualIfaceCall
            = TaskStateVisitor::isVirtualIfaceMethodCall(nodep)
              && TaskStateVisitor::isIfaceFTaskScope(m_statep->getScope(nodep->taskp()));
        if (m_statep->ftaskNoInline(nodep->taskp()) || virtualIfaceCall) {
            processArgs(nodep);
            // This may share VarScope's with a public task, if any.  Yuk.
            beginp = createNonInlinedFTask(nodep, outvscp, cnewp /*ref*/);
        } else {
            beginp = createInlinedFTask(nodep, outvscp);
            ++m_statInlines;
        }

        if (VN_IS(nodep, New)) {  // New not legal as while() condition
            insertBeforeStmt(nodep, beginp);
            UASSERT_OBJ(cnewp, nodep, "didn't create cnew for new");
            nodep->replaceWith(cnewp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (VN_IS(nodep->backp(), NodeAssign)) {
            UASSERT_OBJ(nodep->taskp()->isFunction(), nodep,
                        "funcref-like assign to non-function");
            insertBeforeStmt(nodep, beginp);
            AstVarRef* const outrefp = new AstVarRef{nodep->fileline(), outvscp, VAccess::READ};
            nodep->replaceWith(outrefp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (!VN_IS(nodep->backp(), StmtExpr)) {
            UASSERT_OBJ(nodep->taskp()->isFunction(), nodep,
                        "funcref-like expression to non-function");
            AstVarRef* const outrefp = new AstVarRef{nodep->fileline(), outvscp, VAccess::READ};
            AstExprStmt* lambdap = new AstExprStmt{nodep->fileline(), beginp, outrefp};

            if (m_inNew) {
                AstVar* varp = outvscp->varp();

                // Create a new var that will be inside the lambda
                AstVar* newvarp = varp->cloneTree(false);
                newvarp->funcLocal(true);

                // Create a new VarScope for the new variable
                AstVarScope* const newvscp
                    = new AstVarScope{newvarp->fileline(), m_scopep, newvarp};
                m_scopep->addVarsp(newvscp);

                // Replace all references so they point to the new var and varscope
                lambdap->stmtsp()->foreachAndNext([outvscp, newvscp](AstVarRef* refp) {
                    if (refp->varScopep() == outvscp) {
                        refp->varScopep(newvscp);
                        refp->varp(newvscp->varp());
                    }
                });

                // Add variable initialization
                lambdap->prependStmtsp(newvarp);
                lambdap->hasResult(false);

                // Add return statement - TODO: Why not VarRef(outvscp)?
                AstCExpr* const exprp = new AstCExpr{nodep->fileline(), varp->name()};
                exprp->dtypeSetString();
                lambdap->addStmtsp(new AstCReturn{nodep->fileline(), exprp});
            }

            // AstExprStmt is currently treated as impure, so clear the cached purity of its
            // parents
            nodep->replaceWith(lambdap);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            VIsCached::clearCacheTree();
        } else {  // VN_IS(nodep->backp(), StmtExpr)
            insertBeforeStmt(nodep, beginp);
            if (nodep->taskp()->isFunction()
                && !nodep->backp()->fileline()->warnIsOff(V3ErrorCode::IGNOREDRETURN)) {
                nodep->v3warn(
                    IGNOREDRETURN,
                    "Ignoring return value of non-void function (IEEE 1800-2023 13.4.1)");
            }
            nodep->unlinkFrBack();
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
        UINFO(4, "  FTask REF Done.");
    }
    void visit(AstNodeFTask* const nodep) override {
        UINFO(4, " visitFTask   " << nodep);
        VL_RESTORER(m_insStmtp);
        m_insStmtp = nodep->stmtsp();  // Might be null if no statements, but we won't use it
        if (!nodep->user1SetOnce()) {  // Just one creation needed per function
            // Expand functions in it
            int modes = 0;
            if (nodep->dpiImport()) modes++;
            if (nodep->dpiExport()) modes++;
            if (nodep->taskPublic()) modes++;
            if (nodep->classMethod()) modes++;
            if (v3Global.opt.protectIds() && nodep->taskPublic()) {
                // We always call protect() on names, we don't check if public or not
                // Hence any external references wouldn't be able to find the refed public object.
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Using --protect-ids with public function");
            }
            if (modes > 1) {
                nodep->v3error("Cannot mix DPI import, DPI export, class methods, and/or public "
                               "on same function: "
                               << nodep->prettyNameQ());
            }

            const bool noInline = m_statep->ftaskNoInline(nodep);
            const bool needsNonInlineCFunc = m_statep->ftaskNeedsNonInlineCFunc(nodep);
            // Warn if not inlining an impure ftask (unless method, recursive,
            // or interface-local member access, which is not truly external).
            // Will likely not schedule correctly.
            // TODO: Why not if recursive? It will not work ...
            if (noInline && !nodep->classMethod() && !nodep->recursive()) {
                if (AstNode* const impurep = m_statep->checkImpure(nodep)) {
                    if (!isIfaceLocalImpure(nodep, impurep)) {
                        nodep->v3warn(IMPURE, "Unsupported: External variable referenced by "
                                              "non-inlined function/task: "
                                                  << nodep->prettyNameQ() << '\n'
                                                  << nodep->warnContextPrimary() << '\n'
                                                  << impurep->warnOther()
                                                  << "... Location of the external reference: "
                                                  << impurep->prettyNameQ() << '\n'
                                                  << impurep->warnContextSecondary());
                    }
                }
            }

            if (noInline || needsNonInlineCFunc || nodep->dpiImport() || nodep->dpiExport()
                || nodep->taskPublic()) {
                // Clone it first, because we may have later FTaskRef's that still need
                // the original version.
                AstNodeFTask* const clonedFuncp = nodep->cloneTree(false);
                if (nodep->isConstructor()) m_statep->remapFuncClassp(nodep, clonedFuncp);
                const bool makeNonInlineFunc = noInline || needsNonInlineCFunc;
                if (AstCFunc* const cfuncp = makeUserFunc(clonedFuncp, makeNonInlineFunc)) {
                    nodep->addNextHere(cfuncp);
                    if (nodep->dpiImport() || makeNonInlineFunc) {
                        m_statep->ftaskCFuncp(nodep, cfuncp);
                    }
                    iterateIntoFTask(clonedFuncp);  // Do the clone too
                }
            }

            // Any variables inside the function still have varscopes pointing to them.
            // We're going to delete the vars, so delete the varscopes.
            if (nodep->isFunction()) {
                if (AstVar* const portp = VN_CAST(nodep->fvarp(), Var)) {
                    AstVarScope* const vscp = m_statep->findVarScope(m_scopep, portp);
                    UINFO(9, "   funcremovevsc " << vscp);
                    VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
                }
            }
            for (AstNode* const stmtp : nodep->stmtspList()) {
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    AstVarScope* const vscp = m_statep->findVarScope(m_scopep, portp);
                    UINFO(9, "   funcremovevsc " << vscp);
                    VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
                }
            }
            // Just push for deletion, as other references to func may
            // remain until visitor exits
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstAssignForce* nodep) override {
        // Force statements cannot be converted to always blocks outside of a logic block
        // This causes function calls on RHS of force assignments to be improperly inlined and
        // called just once. To prevent this, we create a temporary variable for each function
        // reference on RHS. This variable is declared in the nearest scope and gets a continuous
        // assignment of the function, so it can be converted to always and properly inlined This
        // temporary variable becomes the RHS of the force assignment
        std::vector<AstNodeFTaskRef*> refs;
        nodep->rhsp()->foreach([&refs](AstNodeFTaskRef* refp) { refs.push_back(refp); });
        for (AstNodeFTaskRef* const refp : refs) {

            // Create the temporary variable and its scope. Every function call gets its own
            // variable in each scope, which is shared with the same call in other instances.
            AstVarScope* const interVscp
                = m_forceTmps.make(refp->fileline(), m_scopep, refp->dtypep(), refp->name());

            // Recompute the helper in a combo block so any inlined function body stays
            // inside schedulable logic rather than spilling statements at module scope.
            AstAssign* const assignp = new AstAssign{
                nodep->fileline(), new AstVarRef{nodep->fileline(), interVscp, VAccess::WRITE},
                nodep->rhsp()->cloneTreePure(false)};
            AstSenTree* const senTreep = new AstSenTree{
                nodep->fileline(), new AstSenItem{nodep->fileline(), AstSenItem::Combo{}}};
            AstActive* const activep
                = new AstActive{nodep->fileline(), "force-func-update", senTreep};
            activep->senTreeStorep(activep->sentreep());
            activep->addStmtsp(
                new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, nullptr, assignp});
            m_scopep->addBlocksp(activep);

            // Replace RHS of force assignment with the temporary variable
            refp->replaceWith(new AstVarRef{nodep->fileline(), interVscp, VAccess::READ});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        }
    }
    void visit(AstNodeForeach* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "Foreach statements should have been converted to while statements in V3Begin.cpp");
    }
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_insStmtp);
        m_insStmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstStmtExpr* nodep) override {
        VL_RESTORER(m_insStmtp);
        m_insStmtp = nodep;
        iterateChildren(nodep);
        if (!nodep->exprp()) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    void visit(AstSenItem* nodep) override {
        UASSERT_OBJ(!m_inSensesp, nodep, "Senitem under senitem?");
        VL_RESTORER(m_inSensesp);
        m_inSensesp = true;
        iterateChildren(nodep);
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    TaskVisitor(AstNetlist* nodep, TaskStateVisitor* statep)
        : m_statep{statep} {
        iterate(nodep);
    }
    ~TaskVisitor() {
        V3Stats::addStat("Optimizations, Functions inlined", m_statInlines);
        V3Stats::addStat("Optimizations, Function getters replaced with reads", m_statGetters);
        V3Stats::addStat("Optimizations, Hierarchical DPI wrappers with costs",
                         m_statHierDpisWithCosts);
    }
};

//######################################################################
// Mark interface members under timing controls of interface CFuncs as interface-sensed

class TaskIfaceSensVisitor final : public VNVisitorConst {
    // STATE
    bool m_underIfaceFunc = false;  // Under a CFunc owned by an interface scope
    bool m_underSenses = false;  // Under a sensitivity expression of such a CFunc

    // METHODS
    void markSensesAndIterate(AstNode* nodep) {
        if (!m_underIfaceFunc) return;
        VL_RESTORER(m_underSenses);
        m_underSenses = true;
        iterateAndNextConstNull(nodep);
    }
    // VISITORS
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_underIfaceFunc);
        m_underIfaceFunc = VN_IS(nodep->scopep()->modp(), Iface);
        iterateChildrenConst(nodep);
    }
    void visit(AstSenTree* nodep) override { markSensesAndIterate(nodep->sensesp()); }
    void visit(AstWait* nodep) override {
        markSensesAndIterate(nodep->condp());
        iterateAndNextConstNull(nodep->stmtsp());
    }
    void visit(AstVarRef* nodep) override {
        if (!m_underSenses) return;
        UASSERT_OBJ(nodep->varScopep(), nodep, "No var scope");
        // Keep temps: the clocking event var is a MODULETEMP
        if (nodep->varp()->isFuncLocal()) return;
        if (AstIface* const ifacep = VN_CAST(nodep->varScopep()->scopep()->modp(), Iface)) {
            nodep->varp()->sensIfacep(ifacep);
        }
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit TaskIfaceSensVisitor(AstNetlist* nodep) { iterateChildrenConst(nodep); }
    ~TaskIfaceSensVisitor() override = default;
};

//######################################################################
// Task class functions

const char* const V3Task::s_dpiTemporaryVarSuffix = "__Vcvt";

V3TaskConnects V3Task::taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp,
                                    V3TaskConnectState* statep, bool makeChanges) {
    // Output list will be in order of the port declaration variables (so
    // func calls are made right in C)
    // Missing pin/expr?  We return (pinvar, nullptr)
    // Extra   pin/expr?  We clean it up
    UINFO(9, "taskConnects " << nodep);
    std::map<const std::string, int> nameToIndex;
    V3TaskConnects tconnects;
    UASSERT_OBJ(nodep->taskp(), nodep, "unlinked");

    // Find ports
    int tpinnum = 0;
    AstVar* sformatp = nullptr;
    for (AstNode* stmtp = taskStmtsp; stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* const portp = VN_CAST(stmtp, Var)) {
            if (portp->isIO()) {
                tconnects.emplace_back(portp, static_cast<AstArg*>(nullptr));
                nameToIndex.emplace(portp->name(), tpinnum);  // For name based connections
                ++tpinnum;
                if (portp->attrSFormat()) {
                    sformatp = portp;
                } else if (sformatp) {
                    portp->v3error("/*verilator sformat*/ can only be applied to last argument of "
                                   "a function");
                }
            }
        }
    }

    // Find pins
    int ppinnum = 0;
    bool reorganize = false;
    for (AstArg* const argp : nodep->argspList()) {
        if (!argp->name().empty()) {
            // By name
            const auto it = nameToIndex.find(argp->name());
            if (it == nameToIndex.end()) {
                if (makeChanges) {
                    argp->v3error(
                        "No such argument "
                        << argp->prettyNameQ() << " in call to " << nodep->taskp()->verilogKwd()
                        << " " << nodep->taskp()->prettyNameQ() << '\n'
                        << nodep->warnContextPrimary() << '\n'
                        << nodep->warnMore() << "... Location of " << nodep->taskp()->verilogKwd()
                        << " " << nodep->taskp()->prettyNameQ() << " declaration\n"
                        << nodep->taskp()->warnContextSecondary());
                    // We'll just delete it; seems less error prone than making a false argument
                    VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);
                }
            } else {
                if (tconnects[it->second].second && makeChanges) {
                    argp->v3error("Duplicate argument " << argp->prettyNameQ()
                                                        << " in function call to "
                                                        << nodep->taskp()->prettyTypeName());
                    tconnects[it->second].second->unlinkFrBack()->deleteTree();
                }
                tconnects[it->second].second = argp;
                reorganize = true;
            }
        } else {  // By pin number
            if (nodep->taskp()->prettyName() == "randomize") {
                // Arguments to randomize() are special, will be handled in V3Randomize
            } else if (ppinnum >= tpinnum) {
                if (sformatp) {
                    tconnects.emplace_back(sformatp, static_cast<AstArg*>(nullptr));
                    tconnects[ppinnum].second = argp;
                    ++tpinnum;
                } else if (makeChanges) {
                    argp->v3error("Too many arguments in call to "
                                  << nodep->taskp()->verilogKwd() << " "
                                  << nodep->taskp()->prettyNameQ() << '\n'
                                  << nodep->warnContextPrimary() << '\n'
                                  << nodep->warnMore() << "... Location of "
                                  << nodep->taskp()->verilogKwd() << " "
                                  << nodep->taskp()->prettyNameQ() << " declaration:\n"
                                  << nodep->taskp()->warnContextSecondary());
                    // We'll just delete it; seems less error prone than making a false argument
                    VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);
                }
            } else {
                tconnects[ppinnum].second = argp;
            }
        }
        ++ppinnum;
    }

    if (!makeChanges) return tconnects;

    // Connect missing ones
    VInsertionSet<const AstVar*> argWrap;  // Which ports are defaulted; need arg wrapper creation
    for (int i = 0; i < tpinnum; ++i) {
        AstVar* const portp = tconnects[i].first;
        if (!tconnects[i].second || !tconnects[i].second->exprp()) {
            AstNodeExpr* newvaluep = nullptr;
            if (!portp->valuep()) {
                nodep->v3error("Missing argument on non-defaulted argument "
                               << portp->prettyNameQ() << " in function call to "
                               << nodep->taskp()->prettyTypeName());
                newvaluep = new AstConst{nodep->fileline(), AstConst::Unsized32{}, 0};
            } else if (AstFuncRef* const funcRefp = VN_CAST(portp->valuep(), FuncRef)) {
                const AstNodeFTask* const funcp = funcRefp->taskp();
                if (funcp->classMethod() && funcp->isStatic()) newvaluep = funcRefp;
            } else if (AstConst* const constp = VN_CAST(portp->valuep(), Const)) {
                newvaluep = constp;
            }

            if (!newvaluep) {
                // The default value for this port might be a constant
                // expression that hasn't been folded yet. Try folding it
                // now; we don't have much to lose if it fails.
                newvaluep = V3Const::constifyEdit(VN_AS(portp->valuep(), NodeExpr));
                if (!VN_IS(newvaluep, Const)) {
                    if (statep) {
                        portp->pinNum(i + 1);  // Make sure correct, will use to build name
                        UINFO(9, "taskConnects arg wrapper needed " << portp->valuep());
                        argWrap.insert(portp);
                    } else {  // statep = nullptr, called too late or otherwise to handle args
                        // Problem otherwise is we might have a varref, task
                        // call, or something else that only makes sense in the
                        // domain of the function (or class containing the method),
                        // versus that of the callee.
                        nodep->v3warn(
                            E_UNSUPPORTED,
                            "Unsupported: Non-constant default value in missing argument "
                                << portp->prettyNameQ() << " in function call to "
                                << nodep->taskp()->prettyTypeName());
                        newvaluep = new AstConst{nodep->fileline(), AstConst::Unsized32{}, 0};
                    }
                }
            }
            newvaluep = newvaluep->backp() ? newvaluep->cloneTree(true) : newvaluep;
            // To avoid problems with callee needing to know to deleteTree
            // or not, we make this into a pin
            UINFO(9, "Default pin for " << portp);
            AstArg* const newp = new AstArg{nodep->fileline(), portp->name(), newvaluep};
            if (tconnects[i].second) {  // Have a "nullptr" pin already defined for it
                VL_DO_CLEAR(tconnects[i].second->unlinkFrBack()->deleteTree(),
                            tconnects[i].second = nullptr);
            }
            tconnects[i].second = newp;
            reorganize = true;
        }
        if (tconnects[i].second) {
            UINFO(9, "Connect " << portp << "  ->  " << tconnects[i].second);
        } else {
            UINFO(9, "Connect " << portp << "  ->  NONE");
        }
    }

    for (const auto& tconnect : tconnects) {
        AstArg* const argp = tconnect.second;
        argp->name("");  // Can forget name as will add back in pin order
    }

    if (reorganize) {
        // To simplify downstream, put argument list back into pure pinnumber ordering
        while (nodep->argsp()) {
            // Must unlink each pin, not all pins linked together as one list
            nodep->argsp()->unlinkFrBack();
        }
        for (int i = 0; i < tpinnum; ++i) {
            AstArg* const argp = tconnects[i].second;
            UASSERT_OBJ(argp, nodep, "Lost argument in func conversion");
            nodep->addArgsp(argp);
        }
    }

    if (debug() >= 9) {  // LCOV_EXCL_START
        nodep->dumpTree("-  ftref-out: ");
        for (int i = 0; i < tpinnum; ++i) {
            UINFO(0, "   pin " << i << "  pin=" << cvtToHex(tconnects[i].first)
                               << "  conn=" << cvtToHex(tconnects[i].second));
        }
    }  // LCOV_EXCL_STOP

    if (!argWrap.empty()) {
        UINFO(9, "Arg wrapper generation " << nodep);
        // Create wrapper function with default argument settings.
        // Needed because the default needs symbol table of the called function.
        taskConnectWrap(nodep, tconnects, statep, argWrap);
        // Regenerate all connections, this time connecting to the wrapper
        return taskConnects(nodep, nodep->taskp()->stmtsp(),
                            // statep null, so can't recurse forever
                            nullptr);
    }
    return tconnects;
}

void V3Task::taskConnectWrap(AstNodeFTaskRef* nodep, const V3TaskConnects& tconnects,
                             V3TaskConnectState* statep,
                             const VInsertionSet<const AstVar*>& argWrap) {
    statep->setDidWrap();
    // Make wrapper name such that is same iff same args are defaulted
    std::string newname = nodep->name() + "__Vtcwrap";
    for (const AstVar* varp : argWrap) newname += "_" + cvtToStr(varp->pinNum());
    const auto pair = statep->wrapMap().emplace(std::piecewise_construct,
                                                std::forward_as_tuple(nodep->taskp(), newname),
                                                std::forward_as_tuple(nullptr));
    if (pair.second) {
        pair.first->second = taskConnectWrapNew(nodep->taskp(), newname, tconnects, argWrap);
    }
    AstNodeFTask* const newTaskp = pair.first->second;

    // Remove the defaulted arguments from original outside call
    for (const auto& tconnect : tconnects) {
        const AstVar* const portp = tconnect.first;
        AstArg* const argp = tconnect.second;
        if (argWrap.exists(portp)) {  // Removed arg
            statep->pushDeletep(argp->unlinkFrBack());
        }
    }
    // Change outside call to connect to new function
    nodep->taskp(newTaskp);
    nodep->name(newTaskp->name());
    // UINFOTREE(9, nodep, "", "taskConnectWrap-call");
}

AstNodeFTask* V3Task::taskConnectWrapNew(AstNodeFTask* taskp, const string& newname,
                                         const V3TaskConnects& tconnects,
                                         const VInsertionSet<const AstVar*>& argWrap) {
    std::map<const AstVar*, AstVar*> oldNewVars;  // Old -> new var mappings

    AstNodeFTask* const newTaskp = taskp->cloneType(newname);
    newTaskp->propagateAttrFrom(taskp);
    taskp->addNextHere(newTaskp);

    AstNodeFTaskRef* newCallp = nullptr;
    AstNode* newCallInsertp = nullptr;
    if (VN_IS(taskp, Func)) {
        AstVar* const fvarp = VN_AS(taskp->fvarp(), Var);
        UASSERT_OBJ(fvarp, taskp, "FuncRef without fvar");
        AstVar* const newFVarp = fvarp->cloneTree(true);
        oldNewVars.emplace(fvarp, newFVarp);
        newFVarp->name(newTaskp->name());
        newTaskp->fvarp(newFVarp);
        newTaskp->dtypeFrom(newFVarp);
        newCallp = new AstFuncRef{taskp->fileline(), VN_AS(taskp, Func)};
        newCallInsertp
            = new AstAssign{taskp->fileline(),
                            new AstVarRef{fvarp->fileline(), newFVarp, VAccess::WRITE}, newCallp};
        newCallInsertp->dtypeFrom(newFVarp);
    } else if (VN_IS(taskp, Task)) {
        newCallp = new AstTaskRef{taskp->fileline(), VN_AS(taskp, Task)};
        newCallInsertp = new AstStmtExpr{taskp->fileline(), newCallp};
    } else {
        taskp->v3fatalSrc("Unsupported: Non-constant default value in missing argument in a "
                          << taskp->prettyTypeName());
    }

    // Create wrapper's ports matching original's
    for (const auto& tconnect : tconnects) {
        AstVar* const portp = tconnect.first;
        AstVar* newPortp;
        if (!argWrap.exists(portp)) {  // Not removed arg
            newPortp = new AstVar{portp->fileline(), portp->varType(), portp->name(), portp};
            newPortp->propagateWrapAttrFrom(portp);
            newPortp->funcLocal(true);
            if (newPortp->valuep()) newPortp->valuep()->unlinkFrBack()->deleteTree();
            newTaskp->addStmtsp(newPortp);
        } else {  // Defaulting arg
            AstNodeExpr* const valuep = VN_AS(portp->valuep(), NodeExpr);
            if ((portp->isRef() || portp->isConstRef()) && VN_IS(valuep, VarRef)) {
                const VAccess refAccess = portp->direction().pinAccess();
                AstVarRef* const refp = VN_AS(valuep->cloneTree(false), VarRef);
                refp->access(refAccess);
                AstArg* const newArgp = new AstArg{portp->fileline(), portp->name(), refp};
                newCallp->addArgsp(newArgp);
                continue;
            }
            // Create local temporary
            newPortp = new AstVar{portp->fileline(), VVarType::BLOCKTEMP, portp->name(),
                                  portp->dtypep()};
            newPortp->propagateAttrFrom(portp);
            newPortp->funcLocal(true);
            newTaskp->addStmtsp(newPortp);
            // Runtime-assign it to the default
            if (!VN_IS(valuep, EmptyQueue)) {
                AstAssign* const newAssignp
                    = new AstAssign{valuep->fileline(),
                                    new AstVarRef{valuep->fileline(), newPortp, VAccess::WRITE},
                                    valuep->cloneTree(true)};
                newTaskp->addStmtsp(newAssignp);
            }
        }
        oldNewVars.emplace(portp, newPortp);
        AstArg* const newArgp = new AstArg{
            portp->fileline(), portp->name(),
            new AstVarRef{portp->fileline(), newPortp, portp->direction().pinAccess()}};
        newCallp->addArgsp(newArgp);
    }
    // Create wrapper call to original, passing arguments, adding setting of return value
    newTaskp->addStmtsp(newCallInsertp);
    // Replace any varref's to original to new ports (e.g. in argument equations)
    newTaskp->foreach([=](AstVarRef* refp) {
        const auto it = oldNewVars.find(refp->varp());
        if (it != oldNewVars.end()) refp->varp(it->second);
    });
    // UINFOTREE(9, newTaskp, "", "taskConnectWrap-new");
    return newTaskp;
}

string V3Task::assignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix,
                                   const string& toSuffix, const string& frPrefix) {
    // Create assignment from internal format into DPI temporary
    // Internal representation is scalar, 1D, or multi-dimensional array (similar to SV)
    // DPI temporary is scalar or 1D array (if unpacked array)
    string stmt;
    string ket;
    // Someday we'll have better type support, and this can make variables and casts.
    // But for now, we'll just text-bash it.
    const string frName = frPrefix + portp->name() + frSuffix;
    const string toName = portp->name() + toSuffix;
    const string idx = portp->name() + "__Vidx";
    size_t unpackSize = 1;  // non-unpacked array is treated as size 1
    int unpackDim = 0;
    if (AstUnpackArrayDType* const unpackp
        = VN_CAST(portp->dtypep()->skipRefp(), UnpackArrayDType)) {
        unpackSize = unpackp->arrayUnpackedElements();
        unpackDim = unpackp->dimensions(false).second;
        if (unpackDim > 0) UASSERT_OBJ(unpackSize > 0, portp, "size must be greater than 0");
    }
    if (!portp->dtypep()->isDpiPrimitive()) {
        const bool isBit = portp->dtypep()->isDpiBitVec();
        const bool needsFor = unpackSize > 1;
        if (needsFor) {
            stmt = "for (size_t " + idx + " = 0; " + idx + " < " + cvtToStr(unpackSize) + "; ++"
                   + idx + ") ";
        }

        stmt += (isBit ? "VL_SET_SVBV_"s : "VL_SET_SVLV_"s)
                + portp->dtypep()->skipRefp()->charIQWN() + "(" + cvtToStr(portp->width()) + ", ";
        stmt += toName;
        if (needsFor) {
            stmt += " + " + cvtToStr(portp->dtypep()->skipRefp()->widthWords()) + " * " + idx;
        }
        stmt += ", ";
        if (unpackDim > 0) {  // Access multi-dimensional array as a 1D array
            stmt += "(&" + frName;
            for (int i = 0; i < unpackDim; ++i) stmt += "[0]";
            stmt += ")[" + (needsFor ? idx : "0") + "])";
        } else {
            stmt += frName + ")";
        }
    } else {
        const bool isChandle
            = portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::CHANDLE;
        const bool isString
            = portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::STRING;
        const string unpackAt = unpackSize > 1 ? "[" + idx + "]" : "[0]";
        if (unpackDim > 0) {
            const string forStmt = unpackSize > 1
                                       ? "for (size_t " + idx + " = 0; " + idx + " < "
                                             + cvtToStr(unpackSize) + "; ++" + idx + ") "
                                       : "";
            stmt += forStmt + toName + unpackAt;
        } else {
            if (isPtr) stmt += "*";  // DPI outputs are pointers
            stmt += toName;
        }
        stmt += " = ";
        if (isChandle) {
            stmt += "VL_CVT_Q_VP(";
            ket += ")";
        }
        if (unpackDim > 0) {
            stmt += "(&" + frName;
            for (int i = 0; i < unpackDim; ++i) stmt += "[0]";
            stmt += ")" + unpackAt;
        } else {
            stmt += frName;
        }
        if (isString) stmt += ".c_str()";
    }
    stmt += ket + ";";
    return stmt;
}

// Create assignment from DPI temporary into internal format
// DPI temporary is scalar or 1D array (if unpacked array)
// Internal representation is scalar, 1D, or multi-dimensional array (similar to SV)
std::string V3Task::assignDpiToInternal(const std::string& lhsName, AstVar* varp) {
    std::string cvt;
    bool useSvVec;
    std::tie(cvt, useSvVec) = TaskDpiUtils::dpiToInternalCvtStmt(varp->dtypep());
    const std::vector<std::pair<int, int>> strides = TaskDpiUtils::unpackDimsAndStrides(varp);
    const int total = strides.empty() ? 1 : strides[0].first * strides[0].second;
    const int widthWords = varp->dtypep()->elemDTypep()->widthWords();
    string statements;
    for (int i = 0; i < total; ++i) {
        std::string lhs = lhsName;
        // extract a scalar from multi-dimensional array (internal format)
        for (const auto& stride : strides) {
            lhs += "[" + std::to_string((i / stride.second) % stride.first) + "]";
        }
        // extract a scalar from DPI temporary var that is scalar or 1D array
        if (useSvVec) {
            const std::string offset = std::to_string(i * widthWords);
            statements += cvt + " " + lhs + ", " + varp->name() + " + " + offset + ");\n";
        } else {
            const std::string elem = strides.empty() ? "" : "[" + std::to_string(i) + "]";
            statements += lhs + " = " + cvt + varp->name() + elem + ")" + ";\n";
        }
    }
    return statements;
}

void V3Task::taskAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        TaskStateVisitor visitors{nodep};
        const TaskVisitor visitor{nodep, &visitors};
    }  // Destruct before checking
    { TaskIfaceSensVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("task", 0, dumpTreeEitherLevel() >= 3);
}
