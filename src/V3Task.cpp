// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for task nodes
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
// V3Task's Transformations:
//
// Each module:
//      Look for TASKREF
//          Insert task's statements into the referrer
//      Look for TASKs
//          Remove them, they're inlined
//
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Task.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3LinkLValue.h"

#include <map>
#include <tuple>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Graph subclasses

class TaskBaseVertex VL_NOT_FINAL : public V3GraphVertex {
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
    // Every task gets a vertex, and we link tasks together based on funcrefs.
    AstNodeFTask* const m_nodep;
    AstCFunc* m_cFuncp = nullptr;

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
};

class TaskCodeVertex final : public TaskBaseVertex {
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
private:
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
    AstAssignW* m_assignwp = nullptr;  // Current assignment
    AstNodeFTask* m_ctorp = nullptr;  // Class constructor
    AstClass* m_classp = nullptr;  // Current class
    V3Graph m_callGraph;  // Task call graph
    TaskBaseVertex* m_curVxp;  // Current vertex we're adding to
    std::vector<AstInitialAutomatic*> m_initialps;  // Initial blocks to move

public:
    // METHODS
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
    AstCFunc* ftaskCFuncp(AstNodeFTask* nodep) { return getFTaskVertex(nodep)->cFuncp(); }
    void ftaskCFuncp(AstNodeFTask* nodep, AstCFunc* cfuncp) {
        getFTaskVertex(nodep)->cFuncp(cfuncp);
    }
    void checkPurity(AstNodeFTask* nodep) { checkPurity(nodep, getFTaskVertex(nodep)); }

private:
    void checkPurity(AstNodeFTask* nodep, TaskBaseVertex* vxp) {
        if (nodep->recursive()) return;  // Impure, but no warning
        if (!vxp->pure()) {
            nodep->v3warn(
                IMPURE, "Unsupported: External variable referenced by non-inlined function/task: "
                            << nodep->prettyNameQ() << '\n'
                            << nodep->warnContextPrimary() << '\n'
                            << vxp->impureNode()->warnOther()
                            << "... Location of the external reference: "
                            << vxp->impureNode()->prettyNameQ() << '\n'
                            << vxp->impureNode()->warnContextSecondary());
        }
        // And, we need to check all tasks this task calls
        for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            checkPurity(nodep, static_cast<TaskBaseVertex*>(edgep->top()));
        }
    }
    TaskFTaskVertex* getFTaskVertex(AstNodeFTask* nodep) {
        if (!nodep->user4p()) nodep->user4p(new TaskFTaskVertex{&m_callGraph, nodep});
        return static_cast<TaskFTaskVertex*>(nodep->user4u().toGraphVertex());
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        // Each FTask is unique per-scope, so AstNodeFTaskRefs do not need
        // pointers to what scope the FTask is to be invoked under.
        // However, to create variables, we need to track the scopes involved.
        // Find all var->varscope mappings, for later cleanup
        for (AstNode* stmtp = nodep->varsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVarScope* const vscp = VN_CAST(stmtp, VarScope)) {
                if (vscp->varp()->isFuncLocal() || vscp->varp()->isUsedLoopIdx()) {
                    UINFO(9, "   funcvsc " << vscp << endl);
                    m_varToScopeMap.insert(
                        std::make_pair(std::make_pair(nodep, vscp->varp()), vscp));
                }
            }
        }
        // Likewise, all FTask->scope mappings
        for (AstNode* stmtp = nodep->blocksp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstNodeFTask* const taskp = VN_CAST(stmtp, NodeFTask)) taskp->user3p(nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstAssignW* nodep) override {
        VL_RESTORER(m_assignwp);
        m_assignwp = nodep;
        VL_DO_DANGLING(iterateChildren(nodep), nodep);  // May delete nodep.
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // Includes handling AstMethodCall, AstNew
        if (m_assignwp) {
            // Wire assigns must become always statements to deal with insertion
            // of multiple statements.  Perhaps someday make all wassigns into always's?
            UINFO(5, "     IM_WireRep  " << m_assignwp << endl);
            m_assignwp->convertToAlways();
            VL_DO_CLEAR(pushDeletep(m_assignwp), m_assignwp = nullptr);
        }
        // We make multiple edges if a task is called multiple times from another task.
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked task");
        new TaskEdge{&m_callGraph, m_curVxp, getFTaskVertex(nodep->taskp())};
    }
    void visit(AstNodeFTask* nodep) override {
        UINFO(9, "  TASK " << nodep << endl);
        {
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
        iterateChildren(nodep);
        nodep->user4p(m_curVxp);  // Remember what task it's under
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (nodep->varp()->user4u().toGraphVertex() != m_curVxp) {
            if (m_curVxp->pure() && !nodep->varp()->isXTemp()) m_curVxp->impure(nodep);
        }
    }
    void visit(AstClass* nodep) override {
        // Move initial statements into the constructor
        m_initialps.clear();
        m_ctorp = nullptr;
        m_classp = nodep;
        {  // Find m_initialps, m_ctor
            iterateChildren(nodep);
        }
        UASSERT_OBJ(m_ctorp, nodep, "class constructor missing");  // LinkDot always makes it
        for (AstInitialAutomatic* initialp : m_initialps) {
            if (AstNode* const newp = initialp->stmtsp()) {
                newp->unlinkFrBackWithNext();
                if (!m_ctorp->stmtsp()) {
                    m_ctorp->addStmtsp(newp);
                } else {
                    m_ctorp->stmtsp()->addHereThisAsNext(newp);
                }
            }
            VL_DO_DANGLING(pushDeletep(initialp->unlinkFrBack()), initialp);
        }
        m_initialps.clear();
        m_ctorp = nullptr;
        m_classp = nullptr;
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
        AstNode::user3ClearTree();
        AstNode::user4ClearTree();
        //
        iterate(nodep);
        //
        m_callGraph.removeRedundantEdgesSum(&TaskEdge::followAlwaysTrue);
        if (dumpGraphLevel()) m_callGraph.dumpDotFilePrefixed("task_call");
    }
    ~TaskStateVisitor() override = default;
    VL_UNCOPYABLE(TaskStateVisitor);
};

//######################################################################
// DPI related utility functions

struct TaskDpiUtils {
    static std::vector<std::pair<AstUnpackArrayDType*, int>>
    unpackDimsAndStrides(AstNodeDType* dtypep) {
        std::vector<std::pair<AstUnpackArrayDType*, int>> dimStrides;
        if (AstUnpackArrayDType* const unpackp = VN_CAST(dtypep->skipRefp(), UnpackArrayDType)) {
            const std::vector<AstUnpackArrayDType*> dims = unpackp->unpackDimensions();
            dimStrides.resize(dims.size(), {nullptr, 0});
            dimStrides.back() = {dims.back(), 1};
            for (ssize_t i = dims.size() - 2; i >= 0; --i) {
                dimStrides[i].first = dims[i];
                dimStrides[i].second = dimStrides[i + 1].second * dims[i + 1]->elementsConst();
            }
        }
        return dimStrides;
    }
    static bool dpiToInternalFrStmt(AstVar* portp, const string& frName, string& frstmt,
                                    string& ket) {
        ket.clear();
        if (portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::CHANDLE) {
            frstmt = "VL_CVT_VP_Q(" + frName;
            ket = ")";
        } else if ((portp->basicp() && portp->basicp()->isDpiPrimitive())) {
            frstmt = frName;
        } else {
            const string frSvType = portp->basicp()->isDpiBitVec() ? "SVBV" : "SVLV";
            if (portp->isWide()) {
                // Need to convert to wide, using special function
                frstmt = "VL_SET_W_" + frSvType + "(" + cvtToStr(portp->width()) + ",";
                return true;
            } else {
                const AstNodeDType* const dtypep = portp->dtypep()->skipRefp();
                frstmt = "VL_SET_" + string{dtypep->charIQWN()} + "_" + frSvType + "(";
                if (VN_IS(dtypep, UnpackArrayDType)) frstmt += "&";
                frstmt += frName;
                ket = ")";
            }
        }
        return false;
    }
};

//######################################################################
// Task state, as a visitor of each AstNode

class TaskVisitor final : public VNVisitor {
private:
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
    int m_modNCalls = 0;  // Incrementing func # for making symbols
    DpiCFuncs m_dpiNames;  // Map of all created DPI functions

    // METHODS

    AstVarScope* createFuncVar(AstCFunc* funcp, const string& name, AstVar* examplep) {
        AstVar* const newvarp = new AstVar{funcp->fileline(), VVarType::BLOCKTEMP, name, examplep};
        newvarp->funcLocal(true);
        funcp->addInitsp(newvarp);
        AstVarScope* const newvscp = new AstVarScope{funcp->fileline(), m_scopep, newvarp};
        m_scopep->addVarsp(newvscp);
        return newvscp;
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
    AstVarScope* createVarScope(AstVar* invarp, const string& name) {
        if (invarp->isParam() && VN_IS(invarp->valuep(), InitArray)) {
            // Move array params in functions into constant pool
            return v3Global.rootp()->constPoolp()->findTable(VN_AS(invarp->valuep(), InitArray));
        } else {
            // We could create under either the ref's scope or the ftask's scope.
            // It shouldn't matter, as they are only local variables.
            // We choose to do it under whichever called this function, which results
            // in more cache locality.
            AstVar* const newvarp
                = new AstVar{invarp->fileline(), VVarType::BLOCKTEMP, name, invarp};
            newvarp->funcLocal(false);
            newvarp->propagateAttrFrom(invarp);
            m_modp->addStmtsp(newvarp);
            AstVarScope* const newvscp = new AstVarScope{newvarp->fileline(), m_scopep, newvarp};
            m_scopep->addVarsp(newvscp);
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
        AstNodeExpr* const inPinClonep
            = pureCheck ? inPinp->cloneTreePure(true) : inPinp->cloneTree(true);
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
            if (AstNodeUniop* soutPinp = VN_CAST(outPinp, Extend)) {
                outPinp = soutPinp->lhsp();
            } else if (AstNodeUniop* soutPinp = VN_CAST(outPinp, ExtendS)) {
                outPinp = soutPinp->lhsp();
            } else if (AstSel* soutPinp = VN_CAST(outPinp, Sel)) {
                outPinp = soutPinp->fromp();
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
            postRhsp->dtypeFrom(outPinp);
        }
        // Put output assignment AFTER function call
        AstNodeExpr* const outPinClonep
            = pureCheck ? outPinp->cloneTreePure(true) : outPinp->cloneTree(true);
        AstAssign* const assp = new AstAssign{pinp->fileline(), outPinClonep, postRhsp};
        assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
        return assp;
    }

    void connectPort(AstVar* portp, AstArg* argp, const string& namePrefix, AstNode* beginp,
                     bool inlineTask) {
        AstNodeExpr* const pinp = argp->exprp();
        if (inlineTask) {
            portp->unlinkFrBack();
            pushDeletep(portp);  // Remove it from the clone (not original)
        }
        if (!pinp) {
            // Too few arguments in function call
        } else {
            UINFO(9, "     Port " << portp << endl);
            UINFO(9, "      pin " << pinp << endl);
            if (inlineTask) {
                pinp->unlinkFrBack();  // Relinked to assignment below
                VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);  // Args no longer needed
            }
            if (portp->isWritable() && VN_IS(pinp, Const)) {
                pinp->v3error("Function/task " + portp->direction().prettyName()  // e.g. "output"
                              + " connected to constant instead of variable: "
                              + portp->prettyNameQ());
            } else if (portp->isRef() || portp->isConstRef()) {
                bool refArgOk = false;
                if (VN_IS(pinp, VarRef) || VN_IS(pinp, MemberSel) || VN_IS(pinp, StructSel)
                    || VN_IS(pinp, ArraySel)) {
                    refArgOk = true;
                } else if (const AstCMethodHard* const cMethodp = VN_CAST(pinp, CMethodHard)) {
                    refArgOk = cMethodp->name() == "at";
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
                        pushDeletep(pinp);
                    } else {
                        pinp->v3warn(E_TASKNSVAR, "Unsupported: ref argument of inlined "
                                                  "function/task is not a simple variable");
                        // Providing a var to avoid an internal error.
                        AstVarScope* const newvscp
                            = createVarScope(portp, namePrefix + "__" + portp->shortName());
                        portp->user2p(newvscp);
                    }
                }
            } else if (portp->isInoutish()) {
                // if (debug() >= 9) pinp->dumpTree("-pinrsize- ");
                V3LinkLValue::linkLValueSet(pinp);

                AstVarScope* const newvscp
                    = createVarScope(portp, namePrefix + "__" + portp->shortName());
                portp->user2p(newvscp);
                if (!inlineTask)
                    pinp->replaceWith(
                        new AstVarRef{newvscp->fileline(), newvscp, VAccess::READWRITE});

                // Put input assignment in FRONT of all other statements
                AstAssign* const preassp = connectPortMakeInAssign(pinp, newvscp, true);
                if (AstNode* const afterp = beginp->nextp()) {
                    afterp->unlinkFrBackWithNext();
                    AstNode::addNext<AstNode, AstNode>(preassp, afterp);
                }
                beginp->addNext(preassp);

                AstAssign* const postassp = connectPortMakeOutAssign(portp, pinp, newvscp, true);
                beginp->addNext(postassp);
                // if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-pinrsize-out- ");
            } else if (portp->isWritable()) {
                // Make output variables
                // Correct lvalue; we didn't know when we linked
                // This is slightly scary; are we sure no decisions were made
                // before here based on this not being a lvalue?
                // Doesn't seem so; V3Unknown uses it earlier, but works ok.
                V3LinkLValue::linkLValueSet(pinp);
                // Even if it's referencing a varref, we still make a temporary
                // Else task(x,x,x) might produce incorrect results
                AstVarScope* const newvscp
                    = createVarScope(portp, namePrefix + "__" + portp->shortName());
                portp->user2p(newvscp);
                if (!inlineTask)
                    pinp->replaceWith(new AstVarRef{newvscp->fileline(), newvscp, VAccess::WRITE});
                AstAssign* const postassp = connectPortMakeOutAssign(portp, pinp, newvscp, false);
                // Put assignment BEHIND of all other statements
                beginp->addNext(postassp);
            } else if (inlineTask && portp->isNonOutput()) {
                // Make input variable
                AstVarScope* const newvscp
                    = createVarScope(portp, namePrefix + "__" + portp->shortName());
                portp->user2p(newvscp);
                AstAssign* const preassp = connectPortMakeInAssign(pinp, newvscp, false);
                // Put assignment in FRONT of all other statements
                if (AstNode* const afterp = beginp->nextp()) {
                    afterp->unlinkFrBackWithNext();
                    AstNode::addNext<AstNode, AstNode>(preassp, afterp);
                }
                beginp->addNext(preassp);
            }
        }
    }

    AstNode* createInlinedFTask(AstNodeFTaskRef* refp, const string& namePrefix,
                                AstVarScope* outvscp) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstNode* const newbodysp
            = refp->taskp()->stmtsp() ? refp->taskp()->stmtsp()->cloneTree(true) : nullptr;
        AstNode* const beginp
            = new AstComment{refp->fileline(), string{"Function: "} + refp->name(), true};
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
                connectPort(portp, argp, namePrefix, beginp, true);
            }
        }
        UASSERT_OBJ(!refp->pinsp(), refp, "Pin wasn't removed by above loop");
        {
            AstNode* nextstmtp;
            for (AstNode* stmtp = beginp; stmtp; stmtp = nextstmtp) {
                nextstmtp = stmtp->nextp();
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    // Any I/O variables that fell out of above loop were already linked
                    if (!portp->user2p()) {
                        // Move it to a new localized variable
                        portp->unlinkFrBack();
                        pushDeletep(portp);  // Remove it from the clone (not original)
                        AstVarScope* const localVscp
                            = createVarScope(portp, namePrefix + "__" + portp->shortName());
                        portp->user2p(localVscp);
                    }
                }
            }
        }
        // Create function output variables
        if (outvscp) {
            // UINFO(0, "setflag on " << funcp->fvarp() << " to " << outvscp << endl);
            refp->taskp()->fvarp()->user2p(outvscp);
        }
        // Replace variable refs
        relink(beginp);
        //
        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-  iotask: ");
        return beginp;
    }

    AstNode* createNonInlinedFTask(AstNodeFTaskRef* refp, const string& namePrefix,
                                   AstVarScope* outvscp, AstCNew*& cnewpr) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstCFunc* const cfuncp = m_statep->ftaskCFuncp(refp->taskp());
        UASSERT_OBJ(cfuncp, refp, "No non-inline task associated with this task call?");
        //
        AstNode* const beginp
            = new AstComment{refp->fileline(), string{"Function: "} + refp->name(), true};
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

        // Convert complicated outputs to temp signals
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(refp, refp->taskp()->stmtsp());
            for (const auto& itr : tconnects) {
                AstVar* const portp = itr.first;
                AstArg* const argp = itr.second;
                connectPort(portp, argp, namePrefix, beginp, false);
            }
        }
        // First argument is symbol table, then output if a function
        const bool needSyms = !refp->taskp()->dpiImport();
        if (needSyms) ccallp->argTypes("vlSymsp");

        if (refp->taskp()->dpiContext()) {
            // __Vscopep
            AstScopeName* const snp = refp->scopeNamep()->unlinkFrBack();
            UASSERT_OBJ(snp, refp, "Missing scoping context");
            ccallp->addArgsp(snp);
            // __Vfilenamep
            ccallp->addArgsp(new AstCExpr{refp->fileline(),
                                          "\"" + refp->fileline()->filename() + "\"", 64, true});
            // __Vlineno
            ccallp->addArgsp(new AstConst(refp->fileline(), refp->fileline()->lineno()));
        }

        // Create connections
        AstNode* nextpinp;
        for (AstNode* pinp = refp->pinsp(); pinp; pinp = nextpinp) {
            nextpinp = pinp->nextp();
            // Move pin to the CCall, removing all Arg's
            AstNodeExpr* const exprp = VN_AS(pinp, Arg)->exprp();
            exprp->unlinkFrBack();
            ccallp->addArgsp(exprp);
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
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
                    if (args != "") {
                        args += ", ";
                        dpiproto += ", ";
                    }
                    // Include both the Verilator and C type names, as if either
                    // differ we may get C compilation problems later
                    const std::string dpiType = portp->dpiArgType(false, false);
                    dpiproto += dpiType;
                    const std::string vType = portp->dtypep()->prettyDTypeName();
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

    static AstNode* createDpiTemp(AstVar* portp, const string& suffix) {
        const string stmt = portp->dpiTmpVarType(portp->name() + suffix) + ";\n";
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

    AstNode* createAssignDpiToInternal(AstVarScope* portvscp, const string& frName) {
        // Create assignment from DPI temporary into internal format
        // DPI temporary is scalar or 1D array (if unpacked array)
        // Internal representation is scalar, 1D, or multi-dimensional array (similar to SV)
        AstVar* const portp = portvscp->varp();
        string frstmt;
        string ket;
        const bool useSetWSvlv = TaskDpiUtils::dpiToInternalFrStmt(portp, frName, frstmt, ket);
        // Use a AstCExpr, as we want V3Clean to mask off bits that don't make sense.
        int cwidth = VL_IDATASIZE;
        if (!useSetWSvlv && portp->basicp()) {
            if (portp->basicp()->keyword().isBitLogic()) {
                cwidth = VL_EDATASIZE * portp->widthWords();
            } else {
                cwidth = portp->basicp()->keyword().width();
            }
        }

        const std::vector<std::pair<AstUnpackArrayDType*, int>> dimStrides
            = TaskDpiUtils::unpackDimsAndStrides(portp->dtypep());
        const int total = dimStrides.empty() ? 1
                                             : dimStrides.front().first->elementsConst()
                                                   * dimStrides.front().second;
        AstNode* newp = nullptr;
        const int widthWords = portp->basicp()->widthWords();
        for (int i = 0; i < total; ++i) {
            AstNodeExpr* srcp = new AstVarRef{portvscp->fileline(), portvscp, VAccess::WRITE};
            // extract a scalar from multi-dimensional array (internal format)
            for (auto&& dimStride : dimStrides) {
                const size_t dimIdx = (i / dimStride.second) % dimStride.first->elementsConst();
                srcp = new AstArraySel(portvscp->fileline(), srcp, dimIdx);
            }
            AstNode* stmtp = nullptr;
            // extract a scalar from DPI temporary var that is scalar or 1D array
            if (useSetWSvlv) {
                AstNode* const linesp = new AstText{portvscp->fileline(), frstmt + ket};
                linesp->addNext(srcp);
                linesp->addNext(
                    new AstText{portvscp->fileline(),
                                "," + frName + " + " + cvtToStr(i * widthWords) + ");\n"});
                stmtp = new AstCStmt{portvscp->fileline(), linesp};
            } else {
                string from = frstmt;
                if (!dimStrides.empty()) {
                    // e.g. time is 64bit svLogicVector
                    const int coef = portp->basicp()->isDpiLogicVec() ? widthWords : 1;
                    from += "[" + cvtToStr(i * coef) + "]";
                }
                from += ket;
                AstNodeExpr* const rhsp = new AstSel{
                    portp->fileline(), new AstCExpr{portp->fileline(), from, cwidth, false}, 0,
                    portp->width()};
                stmtp = new AstAssign{portp->fileline(), srcp, rhsp};
            }
            if (i > 0) {
                newp->addNext(stmtp);
            } else {
                newp = stmtp;
            }
        }
        return newp;
    }

    AstCFunc* makeDpiExportDispatcher(AstNodeFTask* nodep, AstVar* rtnvarp) {
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();
        AstCFunc* const funcp = new AstCFunc{nodep->fileline(), nodep->cname(), m_scopep,
                                             (rtnvarp ? rtnvarp->dpiArgType(true, true) : "")};
        funcp->dpiExportDispatcher(true);
        funcp->dpiContext(nodep->dpiContext());
        funcp->dontCombine(true);
        funcp->entryPoint(true);
        funcp->isStatic(true);
        funcp->protect(false);
        funcp->cname(nodep->cname());
        // Add DPI Export to top, since it's a global function
        m_topScopep->scopep()->addBlocksp(funcp);

        {  // Create dispatch wrapper
            // Note this function may dispatch to myfunc on a different class.
            // Thus we need to be careful not to assume a particular function layout.
            //
            // Func numbers must be the same for each function, even when there are
            // completely different models with the same function name.
            // Thus we can't just use a constant computed at Verilation time.
            // We could use 64-bits of a MD5/SHA hash rather than a string here,
            // but the compare is only done on first call then memoized, so
            // it's not worth optimizing.
            string stmt;
            // Static doesn't need save-restore as if below will re-fill proper value
            stmt += "static int __Vfuncnum = -1;\n";
            // First time init (faster than what the compiler does if we did a singleton
            stmt += "if (VL_UNLIKELY(__Vfuncnum == -1)) __Vfuncnum = Verilated::exportFuncNum(\""
                    + nodep->cname() + "\");\n";
            // If the find fails, it will throw an error
            stmt += "const VerilatedScope* __Vscopep = Verilated::dpiScope();\n";
            // If dpiScope is fails and is null; the exportFind function throws and error
            const string cbtype
                = VIdProtect::protect(v3Global.opt.prefix() + "__Vcb_" + nodep->cname() + "_t");
            stmt += cbtype + " __Vcb = (" + cbtype
                    + ")(VerilatedScope::exportFind(__Vscopep, __Vfuncnum));\n";  // Can't use
                                                                                  // static_cast
            // If __Vcb is null the exportFind function throws and error
            funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
        }

        // Convert input/inout DPI arguments to Internal types
        string args;
        args += ("(" + EmitCBase::symClassName()
                 + "*)(__Vscopep->symsp())");  // Upcast w/o overhead
        AstNode* argnodesp = nullptr;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
                    // No createDpiTemp; we make a real internal variable instead
                    // SAME CODE BELOW
                    args += ", ";
                    if (args != "") {
                        argnodesp = argnodesp->addNext(new AstText{portp->fileline(), args, true});
                        args = "";
                    }
                    AstVarScope* const outvscp
                        = createFuncVar(funcp, portp->name() + tmpSuffixp, portp);
                    // No information exposure; is already visible in import/export func template
                    outvscp->varp()->protect(false);
                    portp->protect(false);
                    AstVarRef* const refp
                        = new AstVarRef{portp->fileline(), outvscp,
                                        portp->isWritable() ? VAccess::WRITE : VAccess::READ};
                    argnodesp = argnodesp->addNext(refp);

                    if (portp->isNonOutput()) {
                        std::string frName
                            = portp->isInoutish() && portp->basicp()->isDpiPrimitive()
                                      && portp->dtypep()->skipRefp()->arrayUnpackedElements() == 1
                                  ? "*"
                                  : "";
                        frName += portp->name();
                        funcp->addStmtsp(createAssignDpiToInternal(outvscp, frName));
                    }
                }
            }
        }

        if (rtnvarp) {
            AstVar* const portp = rtnvarp;
            // SAME CODE ABOVE
            args += ", ";
            if (args != "") {
                argnodesp = argnodesp->addNext(new AstText{portp->fileline(), args, true});
                args = "";
            }
            AstVarScope* const outvscp = createFuncVar(funcp, portp->name() + tmpSuffixp, portp);
            // No information exposure; is already visible in import/export func template
            outvscp->varp()->protect(false);
            AstVarRef* const refp = new AstVarRef{
                portp->fileline(), outvscp, portp->isWritable() ? VAccess::WRITE : VAccess::READ};
            argnodesp = argnodesp->addNext(refp);
        }

        {  // Call the user function
            // Add the variables referenced as VarRef's so that lifetime analysis
            // doesn't rip up the variables on us
            args += ");\n";
            AstCStmt* const newp = new AstCStmt{nodep->fileline(), "(*__Vcb)("};
            newp->addExprsp(argnodesp);
            VL_DANGLING(argnodesp);
            newp->addExprsp(new AstText{nodep->fileline(), args, true});
            funcp->addStmtsp(newp);
        }

        // Convert output/inout arguments back to internal type
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && portp->isWritable() && !portp->isFuncReturn()) {
                    funcp->addStmtsp(createAssignInternalToDpi(portp, true, tmpSuffixp, ""));
                }
            }
        }

        if (rtnvarp) {
            funcp->addStmtsp(createDpiTemp(rtnvarp, ""));
            funcp->addStmtsp(createAssignInternalToDpi(rtnvarp, false, tmpSuffixp, ""));
            string stmt = "return " + rtnvarp->name();
            stmt += rtnvarp->basicp()->isDpiPrimitive() ? ";\n" : "[0];\n";
            funcp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
        }
        makePortList(nodep, funcp);
        return funcp;
    }

    AstCFunc* makeDpiImportPrototype(AstNodeFTask* nodep, AstVar* rtnvarp) {
        if (nodep->cname() != AstNode::prettyName(nodep->cname())) {
            nodep->v3error("DPI function has illegal characters in C identifier name: "
                           << AstNode::prettyNameQ(nodep->cname()));
        }
        // Tasks (but not void functions) return a boolean 'int' indicating disabled
        const string rtnType = rtnvarp            ? rtnvarp->dpiArgType(true, true)
                               : nodep->dpiTask() ? "int"
                                                  : "";
        AstCFunc* const funcp = new AstCFunc{nodep->fileline(), nodep->cname(), m_scopep, rtnType};
        funcp->dpiContext(nodep->dpiContext());
        funcp->dpiImportPrototype(true);
        funcp->dontCombine(true);
        funcp->entryPoint(false);
        funcp->isMethod(false);
        funcp->protect(false);
        funcp->dpiPure(nodep->dpiPure());
        // Add DPI Import to top, since it's a global function
        m_topScopep->scopep()->addBlocksp(funcp);
        makePortList(nodep, funcp);
        return funcp;
    }

    AstCFunc* getDpiFunc(AstNodeFTask* nodep, AstVar* rtnvarp) {
        UASSERT_OBJ(nodep->dpiImport() || nodep->dpiExport(), nodep, "Not a DPI function");
        // Compute unique signature of this DPI function
        const string signature = dpiSignature(nodep, rtnvarp);
        // Only create one DPI Import prototype or DPI Export entry point for each unique cname as
        // it is illegal for the user to attach multiple tasks with different signatures to one DPI
        // cname.
        const auto it = m_dpiNames.find(nodep->cname());
        if (it == m_dpiNames.end()) {
            // First time encountering this cname. Create Import prototype / Export entry point
            AstCFunc* const funcp = nodep->dpiExport() ? makeDpiExportDispatcher(nodep, rtnvarp)
                                                       : makeDpiImportPrototype(nodep, rtnvarp);
            m_dpiNames.emplace(nodep->cname(), std::make_tuple(nodep, signature, funcp));
            return funcp;
        } else {
            // Seen this cname import before. Check if it's the same prototype.
            const AstNodeFTask* firstNodep;
            string firstSignature;
            AstCFunc* firstFuncp;
            std::tie(firstNodep, firstSignature, firstFuncp) = it->second;
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

    static void makePortList(AstNodeFTask* nodep, AstCFunc* dpip) {
        // Copy nodep's list of function I/O to the new dpip c function
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    // Move it to new function
                    AstVar* const newPortp = portp->cloneTree(false);
                    newPortp->funcLocal(true);
                    dpip->addArgsp(newPortp);
                    if (!portp->basicp()) {
                        portp->v3warn(
                            E_UNSUPPORTED,
                            "Unsupported: DPI argument of type "
                                << portp->basicp()->prettyTypeName() << '\n'
                                << portp->warnMore()
                                << "... For best portability, use bit, byte, int, or longint");
                        // We don't warn on logic either, although the 4-stateness is lost.
                        // That's what other simulators do.
                    }
                }
            }
        }
    }

    void bodyDpiImportFunc(AstNodeFTask* nodep, AstVarScope* rtnvscp, AstCFunc* cfuncp,
                           AstCFunc* dpiFuncp) {
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();
        // Convert input/inout arguments to DPI types
        string args;
        for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                AstVarScope* const portvscp
                    = VN_AS(portp->user2p(), VarScope);  // Remembered when we created it earlier
                if (portp->isIO() && !portp->isFuncReturn() && portvscp != rtnvscp
                    && portp->name() != "__Vscopep"  // Passed to dpiContext, not callee
                    && portp->name() != "__Vfilenamep" && portp->name() != "__Vlineno") {

                    if (args != "") args += ", ";

                    if (portp->isDpiOpenArray()) {
                        AstNodeDType* const dtypep = portp->dtypep()->skipRefp();
                        if (VN_IS(dtypep, DynArrayDType) || VN_IS(dtypep, QueueDType)) {
                            v3fatalSrc("Passing dynamic array or queue as actual argument to DPI "
                                       "open array is not yet supported");
                        }

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
                        if (portp->isWritable() && portp->basicp()->isDpiPrimitive()) {
                            if (!VN_IS(portp->dtypep()->skipRefp(), UnpackArrayDType)) args += "&";
                        }

                        args += portp->name() + tmpSuffixp;

                        cfuncp->addStmtsp(createDpiTemp(portp, tmpSuffixp));
                        if (portp->isNonOutput()) {
                            cfuncp->addStmtsp(
                                createAssignInternalToDpi(portp, false, "", tmpSuffixp));
                        }
                    }
                }
            }
        }

        // Store context, if needed
        if (nodep->dpiContext()) {
            const string stmt = "Verilated::dpiContext(__Vscopep, __Vfilenamep, __Vlineno);\n";
            cfuncp->addStmtsp(new AstCStmt{nodep->fileline(), stmt});
        }

        {  // Call the imported function
            if (rtnvscp) {  // isFunction will no longer work as we unlinked the return var
                cfuncp->addStmtsp(createDpiTemp(rtnvscp->varp(), tmpSuffixp));
                string stmt = rtnvscp->varp()->name();
                stmt += tmpSuffixp;
                stmt += rtnvscp->varp()->basicp()->isDpiPrimitive() ? " = " : "[0] = ";
                cfuncp->addStmtsp(new AstText{nodep->fileline(), stmt, /* tracking: */ true});
            }
            AstCCall* const callp = new AstCCall{nodep->fileline(), dpiFuncp};
            callp->dtypeSetVoid();
            callp->argTypes(args);
            cfuncp->addStmtsp(callp->makeStmt());
        }

        // Convert output/inout arguments back to internal type
        for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                portp->protect(false);  // No additional exposure - already part of shown proto
                if (portp->isIO() && (portp->isWritable() || portp->isFuncReturn())
                    && !portp->isDpiOpenArray()) {
                    AstVarScope* const portvscp = VN_AS(
                        portp->user2p(), VarScope);  // Remembered when we created it earlier
                    cfuncp->addStmtsp(
                        createAssignDpiToInternal(portvscp, portp->name() + tmpSuffixp));
                }
            }
        }
    }

    AstVarScope* getDpiExporTrigger() {
        AstNetlist* const netlistp = v3Global.rootp();
        AstVarScope* dpiExportTriggerp = netlistp->dpiExportTriggerp();
        if (!dpiExportTriggerp) {
            // Create the global DPI export trigger flag the first time we encounter a DPI export.
            // This flag is set any time a DPI export is invoked, and cleared at the end of eval.
            FileLine* const fl = m_topScopep->fileline();
            const string name{"__Vdpi_export_trigger"};
            AstVar* const varp = new AstVar{fl, VVarType::VAR, name, VFlagBitPacked{}, 1};
            m_topScopep->scopep()->modp()->addStmtsp(varp);
            dpiExportTriggerp = new AstVarScope{fl, m_topScopep->scopep(), varp};
            m_topScopep->scopep()->addVarsp(dpiExportTriggerp);
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
                if (!bdtypep->isDpiPrimitive()) {
                    if (bdtypep->isDpiBitVec() && portp->width() > 32) {
                        portp->v3error("DPI function may not return a > 32 bits wide type "
                                       "other than basic types.\n"
                                       + portp->warnMore()
                                       + "... Suggest make it an output argument instead?");
                    }
                    if (bdtypep->isDpiLogicVec()) {
                        portp->v3error("DPI function may not return a 4-state type "
                                       "other than a single 'logic' (IEEE 1800-2017 35.5.5)");
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
            rtnvarp->name(rtnvarp->name()
                          + "__Vfuncrtn");  // Avoid conflict with DPI function name
            if (nodep->dpiImport() || nodep->dpiExport()) rtnvarp->protect(false);
        }

        // Create/pick up the DPI CFunc for DPI Import/ DPI Export.
        AstCFunc* dpiFuncp = nullptr;
        if (nodep->dpiImport() || nodep->dpiExport()) {
            UASSERT_OBJ(!(nodep->dpiOpenParent() && nodep->dpiOpenChild()), nodep,
                        "DPI task should not be both parent and child");
            dpiFuncp = getDpiFunc(nodep, rtnvarp);
            if (!dpiFuncp) return nullptr;  // There was an error, so bail
            if (nodep->dpiImport() && nodep->dpiOpenParent()) {
                // No need to make more than just the DPI Import prototype, the children will
                // create the wrapper implementations.
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
        cfuncp->dpiTraceInit(nodep->dpiTraceInit());
        if (nodep->dpiImport() || nodep->dpiExport()) {
            cfuncp->isStatic(true);
            cfuncp->isLoose(true);
        } else {
            cfuncp->isStatic(false);
        }
        cfuncp->isVirtual(nodep->isVirtual());
        cfuncp->dpiPure(nodep->dpiPure());
        if (nodep->name() == "new") {
            cfuncp->isConstructor(true);
            AstClass* const classp = m_statep->getClassp(nodep);
            if (classp->extendsp()) {
                cfuncp->baseCtors(EmitCBase::prefixNameProtect(classp->extendsp()->classp()));
            }
        }
        if (cfuncp->dpiExportImpl()) cfuncp->cname(nodep->cname());

        if (!nodep->dpiImport() && !nodep->taskPublic()) {
            // Need symbol table
            cfuncp->argTypes(EmitCBase::symClassVar());
            if (cfuncp->name() == "new") {
                const string stmt = VIdProtect::protect("_ctor_var_reset") + "(vlSymsp);\n";
                cfuncp->addInitsp(new AstCStmt{nodep->fileline(), stmt});
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
            snp->dpiExport(
                true);  // The AstScopeName is really a statement(ish) for tracking, not a function
            snp->unlinkFrBack();
            cfuncp->addInitsp(snp);
        }

        // Create list of arguments and move to function
        for (AstNode *nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isParam() && VN_IS(portp->valuep(), InitArray)) {
                    // Move array parameters in functions into constant pool
                    portp->unlinkFrBack();
                    pushDeletep(portp);
                    AstNode* const tablep = v3Global.rootp()->constPoolp()->findTable(
                        VN_AS(portp->valuep(), InitArray));
                    portp->user2p(tablep);
                } else {
                    if (portp->isIO()) {
                        // Move it to new function
                        unlinkAndClone(nodep, portp, false);
                        portp->funcLocal(true);
                        cfuncp->addArgsp(portp);
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
            AstBegin* const tempp = new AstBegin{nodep->fileline(), "[EditWrapper]", bodysp};
            VL_DANGLING(bodysp);
            // If we cloned due to recursion, now need to rip out the ports
            // (that remained in place) then got cloned
            for (AstNode *nextp, *stmtp = tempp->stmtsp(); stmtp; stmtp = nextp) {
                nextp = stmtp->nextp();
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    if (portp->isIO()) portp->unlinkFrBack();
                }
            }
            if (tempp->stmtsp()) cfuncp->addStmtsp(tempp->stmtsp()->unlinkFrBackWithNext());
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        if (nodep->dpiImport()) bodyDpiImportFunc(nodep, rtnvscp, cfuncp, dpiFuncp);

        // Return statement
        if (rtnvscp && nodep->taskPublic()) {
            cfuncp->addFinalsp(new AstCReturn{
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
                if (refp->access().isReadOnly()) return;  // Ignore read reference
                AstVar* const varp = refp->varScopep()->varp();
                // We are ignoring function locals as they should not be referenced anywhere
                // outside the enclosing AstCFunc, hence they are irrelevant for code ordering.
                if (varp->isFuncLocal()) return;
                // Mark it as written by DPI export
                varp->setWrittenByDpi();
                // Remember we had some
                writesNonLocals = true;
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
                if (cfuncp->stmtsp()) {
                    cfuncp->stmtsp()->addHereThisAsNext(assignp);
                } else {
                    cfuncp->addStmtsp(assignp);
                }
            }
        }

        // Mark the fact that this function allocates std::process
        if (nodep->needProcess()) cfuncp->setNeedProcess();

        // Delete rest of cloned task and return new func
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        if (debug() >= 9) cfuncp->dumpTree("-  userFunc: ");
        return cfuncp;
    }

    void iterateIntoFTask(AstNodeFTask* nodep) {
        // Iterate into the FTask we are calling.  Note it may be under a different
        // scope then the caller, so we need to restore state.
        VL_RESTORER(m_scopep);
        VL_RESTORER(m_insStmtp);
        {
            m_scopep = m_statep->getScope(nodep);
            iterate(nodep);
        }
    }
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        if (debug() >= 9) nodep->dumpTree("-  newstmt: ");
        UASSERT_OBJ(m_insStmtp, nodep, "Function call not underneath a statement");
        if (debug() >= 9) newp->dumpTree("-  newfunc: ");
        m_insStmtp->addHereThisAsNext(newp);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modNCalls);
        {
            m_modp = nodep;
            m_insStmtp = nullptr;
            m_modNCalls = 0;
            iterateChildren(nodep);
        }
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
        m_scopep = nodep;
        m_insStmtp = nullptr;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (m_inSensesp) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: function calls in sensitivity lists");
            nodep->taskp(nullptr);  // So V3Broken doesn't complain
            return;
        }
        // Includes handling AstMethodCall, AstNew
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked?");
        iterateIntoFTask(nodep->taskp());  // First, do hierarchical funcs
        UINFO(4, " FTask REF   " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree("-  inlfunc: ");
        UASSERT_OBJ(m_scopep, nodep, "func ref not under scope");
        const string namePrefix = ((VN_IS(nodep, FuncRef) ? "__Vfunc_" : "__Vtask_")
                                   + nodep->taskp()->shortName() + "__" + cvtToStr(m_modNCalls++));
        // Create output variable
        AstVarScope* outvscp = nullptr;
        if (nodep->taskp()->isFunction()) {
            // Not that it's a FUNCREF, but that we're calling a function (perhaps as a task)
            outvscp
                = createVarScope(VN_AS(nodep->taskp()->fvarp(), Var), namePrefix + "__Vfuncout");
        }
        // Create cloned statements
        AstNode* beginp;
        AstCNew* cnewp = nullptr;
        if (m_statep->ftaskNoInline(nodep->taskp())) {
            // This may share VarScope's with a public task, if any.  Yuk.
            beginp = createNonInlinedFTask(nodep, namePrefix, outvscp, cnewp /*ref*/);
        } else {
            beginp = createInlinedFTask(nodep, namePrefix, outvscp);
        }

        if (VN_IS(nodep, New)) {
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
            beginp = new AstExprStmt{nodep->fileline(), beginp, outrefp};
            // AstExprStmt is currently treated as impure, so clear the cached purity of its
            // parents
            nodep->clearCachedPurity();
            nodep->replaceWith(beginp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            insertBeforeStmt(nodep, beginp);
            if (nodep->taskp()->isFunction()) {
                nodep->v3warn(
                    IGNOREDRETURN,
                    "Ignoring return value of non-void function (IEEE 1800-2017 13.4.1)");
            }
            nodep->unlinkFrBack();
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
        UINFO(4, "  FTask REF Done.\n");
    }
    void visit(AstNodeFTask* nodep) override {
        UINFO(4, " visitFTask   " << nodep << endl);
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

            if (nodep->dpiImport() || nodep->dpiExport() || nodep->taskPublic()
                || m_statep->ftaskNoInline(nodep)) {
                // Clone it first, because we may have later FTaskRef's that still need
                // the original version.
                if (m_statep->ftaskNoInline(nodep) && !nodep->classMethod()) {
                    m_statep->checkPurity(nodep);
                }
                AstNodeFTask* const clonedFuncp = nodep->cloneTree(false);
                if (nodep->isConstructor()) m_statep->remapFuncClassp(nodep, clonedFuncp);

                AstCFunc* const cfuncp = makeUserFunc(clonedFuncp, m_statep->ftaskNoInline(nodep));
                if (cfuncp) {
                    nodep->addNextHere(cfuncp);
                    if (nodep->dpiImport() || m_statep->ftaskNoInline(nodep)) {
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
                    UINFO(9, "   funcremovevsc " << vscp << endl);
                    VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
                }
            }
            for (AstNode *nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp = nextp) {
                nextp = stmtp->nextp();
                if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                    AstVarScope* const vscp = m_statep->findVarScope(m_scopep, portp);
                    UINFO(9, "   funcremovevsc " << vscp << endl);
                    VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
                }
            }
            // Just push for deletion, as other references to func may
            // remain until visitor exits
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstWhile* nodep) override {
        // Special, as statements need to be put in different places
        // Preconditions insert first just before themselves (the normal
        // rule for other statement types)
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->precondsp());
        // Conditions insert first at end of precondsp.
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->stmtsp());
        iterateAndNextNull(nodep->incsp());
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstNodeFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "For statements should have been converted to while statements in V3Begin.cpp");
    }
    void visit(AstNodeStmt* nodep) override {
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    void visit(AstStmtExpr* nodep) override {
        m_insStmtp = nodep;
        iterateChildren(nodep);
        if (!nodep->exprp()) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
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
    ~TaskVisitor() override = default;
};

//######################################################################
// Task class functions

const char* const V3Task::s_dpiTemporaryVarSuffix = "__Vcvt";

V3TaskConnects V3Task::taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp,
                                    V3TaskConnectState* statep) {
    // Output list will be in order of the port declaration variables (so
    // func calls are made right in C)
    // Missing pin/expr?  We return (pinvar, nullptr)
    // Extra   pin/expr?  We clean it up
    UINFO(9, "taskConnects " << nodep << endl);
    std::map<const std::string, int> nameToIndex;
    std::set<const AstVar*> argWrap;  // Which ports are defaulted, forcing arg wrapper creation
    V3TaskConnects tconnects;
    UASSERT_OBJ(nodep->taskp(), nodep, "unlinked");

    // Find ports
    int tpinnum = 0;
    AstVar* sformatp = nullptr;
    for (AstNode* stmtp = taskStmtsp; stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* const portp = VN_CAST(stmtp, Var)) {
            if (portp->isIO()) {
                tconnects.push_back(std::make_pair(portp, static_cast<AstArg*>(nullptr)));
                nameToIndex.insert(
                    std::make_pair(portp->name(), tpinnum));  // For name based connections
                tpinnum++;
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
    for (AstNode *nextp, *pinp = nodep->pinsp(); pinp; pinp = nextp) {
        nextp = pinp->nextp();
        AstArg* const argp = VN_AS(pinp, Arg);
        UASSERT_OBJ(argp, pinp, "Non-arg under ftask reference");
        if (argp->name() != "") {
            // By name
            const auto it = nameToIndex.find(argp->name());
            if (it == nameToIndex.end()) {
                pinp->v3error("No such argument " << argp->prettyNameQ() << " in function call to "
                                                  << nodep->taskp()->prettyTypeName());
                // We'll just delete it; seems less error prone than making a false argument
                VL_DO_DANGLING(pinp->unlinkFrBack()->deleteTree(), pinp);
            } else {
                if (tconnects[it->second].second) {
                    pinp->v3error("Duplicate argument " << argp->prettyNameQ()
                                                        << " in function call to "
                                                        << nodep->taskp()->prettyTypeName());
                }
                argp->name("");  // Can forget name as will add back in pin order
                tconnects[it->second].second = argp;
                reorganize = true;
            }
        } else {  // By pin number
            if (ppinnum >= tpinnum) {
                if (sformatp) {
                    tconnects.push_back(std::make_pair(sformatp, static_cast<AstArg*>(nullptr)));
                    tconnects[ppinnum].second = argp;
                    tpinnum++;
                } else {
                    pinp->v3error("Too many arguments in function call to "
                                  << nodep->taskp()->prettyTypeName());
                    // We'll just delete it; seems less error prone than making a false argument
                    VL_DO_DANGLING(pinp->unlinkFrBack()->deleteTree(), pinp);
                }
            } else {
                tconnects[ppinnum].second = argp;
            }
        }
        ppinnum++;
    }

    // Connect missing ones
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
                if (funcp->classMethod() && funcp->lifetime().isStatic()) newvaluep = funcRefp;
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
                        UINFO(9, "taskConnects arg wrapper needed " << portp->valuep() << endl);
                        argWrap.emplace(portp);
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
            newvaluep = newvaluep->cloneTree(true);
            // To avoid problems with callee needing to know to deleteTree
            // or not, we make this into a pin
            UINFO(9, "Default pin for " << portp << endl);
            AstArg* const newp = new AstArg{nodep->fileline(), portp->name(), newvaluep};
            if (tconnects[i].second) {  // Have a "nullptr" pin already defined for it
                VL_DO_CLEAR(tconnects[i].second->unlinkFrBack()->deleteTree(),
                            tconnects[i].second = nullptr);
            }
            tconnects[i].second = newp;
            reorganize = true;
        }
        if (tconnects[i].second) {
            UINFO(9, "Connect " << portp << "  ->  " << tconnects[i].second << endl);
        } else {
            UINFO(9, "Connect " << portp << "  ->  NONE" << endl);
        }
    }

    if (reorganize) {
        // To simplify downstream, put argument list back into pure pinnumber ordering
        while (nodep->pinsp()) {
            // Must unlink each pin, not all pins linked together as one list
            nodep->pinsp()->unlinkFrBack();
        }
        for (int i = 0; i < tpinnum; ++i) {
            AstArg* const argp = tconnects[i].second;
            UASSERT_OBJ(argp, nodep, "Lost argument in func conversion");
            nodep->addPinsp(argp);
        }
    }

    if (debug() >= 9) {  // LCOV_EXCL_START
        nodep->dumpTree("-  ftref-out: ");
        for (int i = 0; i < tpinnum; ++i) {
            UINFO(0, "   pin " << i << "  pin=" << cvtToHex(tconnects[i].first)
                               << "  conn=" << cvtToHex(tconnects[i].second) << endl);
        }
    }  // LCOV_EXCL_STOP

    if (!argWrap.empty()) {
        UINFO(9, "Arg wrapper generation " << nodep << endl);
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
                             V3TaskConnectState* statep, const std::set<const AstVar*>& argWrap) {
    statep->setDidWrap();
    // Make wrapper name such that is same iff same args are defaulted
    std::string newname = nodep->name() + "__Vtcwrap";
    for (const AstVar* varp : argWrap) newname += "_" + cvtToStr(varp->pinNum());
    const auto namekey = std::make_pair(nodep->taskp(), newname);
    auto& wrapMapr = statep->wrapMap();
    const auto it = wrapMapr.find(namekey);
    AstNodeFTask* newTaskp;
    if (it != wrapMapr.end()) {
        newTaskp = it->second;
    } else {
        newTaskp = taskConnectWrapNew(nodep->taskp(), newname, tconnects, argWrap);
        wrapMapr.emplace(namekey, newTaskp);
    }

    // Remove the defaulted arguments from original outside call
    for (const auto& tconnect : tconnects) {
        const AstVar* const portp = tconnect.first;
        AstArg* const argp = tconnect.second;
        if (argWrap.find(portp) != argWrap.end()) {  // Removed arg
            statep->pushDeletep(argp->unlinkFrBack());
        }
    }
    // Change outside call to connect to new function
    nodep->taskp(newTaskp);
    nodep->name(newTaskp->name());
    // if (debug() >= 9) nodep->dumpTree("-taskConnectWrap-call ");
}

AstNodeFTask* V3Task::taskConnectWrapNew(AstNodeFTask* taskp, const string& newname,
                                         const V3TaskConnects& tconnects,
                                         const std::set<const AstVar*>& argWrap) {
    std::map<const AstVar*, AstVar*> oldNewVars;  // Old -> new var mappings

    AstNodeFTask* const newTaskp = taskp->cloneType(newname);
    newTaskp->propagateAttrFrom(taskp);
    taskp->addNextHere(newTaskp);

    AstNodeFTaskRef* newCallp = nullptr;
    AstNode* newCallInsertp = nullptr;
    if (VN_IS(taskp, Func)) {
        AstVar* const fvarp = VN_AS(taskp->fvarp(), Var);
        UASSERT(fvarp, "FuncRef without fvar");
        AstVar* const newFVarp = fvarp->cloneTree(true);
        oldNewVars.emplace(fvarp, newFVarp);
        newFVarp->name(newTaskp->name());
        newTaskp->fvarp(newFVarp);
        newTaskp->dtypeFrom(newFVarp);
        newCallp = new AstFuncRef{taskp->fileline(), taskp->name(), nullptr};
        newCallp->taskp(taskp);
        newCallp->dtypeFrom(newFVarp);
        newCallInsertp
            = new AstAssign{taskp->fileline(),
                            new AstVarRef{fvarp->fileline(), newFVarp, VAccess::WRITE}, newCallp};
        newCallInsertp->dtypeFrom(newFVarp);
    } else if (VN_IS(taskp, Task)) {
        newCallp = new AstTaskRef{taskp->fileline(), taskp->name(), nullptr};
        newCallp->taskp(taskp);
        newCallInsertp = new AstStmtExpr{taskp->fileline(), newCallp};
    } else {
        taskp->v3fatalSrc("Unsupported: Non-constant default value in missing argument in a "
                          << taskp->prettyTypeName());
    }

    // Create wrapper's ports matching original's
    for (const auto& tconnect : tconnects) {
        AstVar* const portp = tconnect.first;
        AstVar* newPortp;
        if (argWrap.find(portp) == argWrap.end()) {  // Not removed arg
            newPortp = new AstVar{portp->fileline(), portp->varType(), portp->name(), portp};
            newPortp->propagateWrapAttrFrom(portp);
            newPortp->funcLocal(true);
            if (newPortp->valuep()) newPortp->valuep()->unlinkFrBack()->deleteTree();
            newTaskp->addStmtsp(newPortp);
        } else {  // Defaulting arg
            AstNodeExpr* const valuep = VN_AS(portp->valuep(), NodeExpr);
            // Create local temporary
            newPortp = new AstVar{portp->fileline(), VVarType::BLOCKTEMP, portp->name(),
                                  portp->dtypep()};
            newPortp->propagateAttrFrom(portp);
            newPortp->funcLocal(true);
            newTaskp->addStmtsp(newPortp);
            // Runtime-assign it to the default
            AstAssign* const newAssignp = new AstAssign{
                valuep->fileline(), new AstVarRef{valuep->fileline(), newPortp, VAccess::WRITE},
                valuep->cloneTree(true)};
            newTaskp->addStmtsp(newAssignp);
        }
        oldNewVars.emplace(portp, newPortp);
        AstArg* const newArgp
            = new AstArg{portp->fileline(), portp->name(),
                         new AstVarRef{portp->fileline(), newPortp, VAccess::READ}};
        newCallp->addPinsp(newArgp);
    }
    // Create wrapper call to original, passing arguments, adding setting of return value
    newTaskp->addStmtsp(newCallInsertp);
    // Replace any varref's to original to new ports (e.g. in argument equations)
    newTaskp->foreach([=](AstVarRef* refp) {
        const auto it = oldNewVars.find(refp->varp());
        if (it != oldNewVars.end()) refp->varp(it->second);
    });
    // if (debug() >= 9) newTaskp->dumpTree("-taskConnectWrap-new ");
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
    size_t unpackSize = 1;  // non-unpacked array is treated as size 1
    int unpackDim = 0;
    if (AstUnpackArrayDType* const unpackp
        = VN_CAST(portp->dtypep()->skipRefp(), UnpackArrayDType)) {
        unpackSize = unpackp->arrayUnpackedElements();
        unpackDim = unpackp->dimensions(false).second;
        if (unpackDim > 0) UASSERT_OBJ(unpackSize > 0, portp, "size must be greater than 0");
    }
    if (portp->basicp()->isDpiBitVec() || portp->basicp()->isDpiLogicVec()) {
        const bool isBit = portp->basicp()->isDpiBitVec();
        const string idx = portp->name() + "__Vidx";
        stmt = "for (size_t " + idx + " = 0; " + idx + " < " + cvtToStr(unpackSize) + "; ++" + idx
               + ") ";
        stmt += (isBit ? "VL_SET_SVBV_" : "VL_SET_SVLV_")
                + string{portp->dtypep()->skipRefp()->charIQWN()} + "(" + cvtToStr(portp->width())
                + ", ";
        stmt += toName + " + " + cvtToStr(portp->dtypep()->skipRefp()->widthWords()) + " * " + idx
                + ", ";
        if (unpackDim > 0) {  // Access multi-dimensional array as a 1D array
            stmt += "(&" + frName;
            for (int i = 0; i < unpackDim; ++i) stmt += "[0]";
            stmt += ")[" + idx + "])";
        } else {
            stmt += frName + ")";
        }
    } else {
        const bool isChandle
            = portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::CHANDLE;
        const bool isString
            = portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::STRING;
        const string idx = portp->name() + "__Vidx";
        stmt = "for (size_t " + idx + " = 0; " + idx + " < " + cvtToStr(unpackSize) + "; ++" + idx
               + ") ";
        if (unpackDim > 0) {
            stmt += toName + "[" + idx + "]";
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
            stmt += ")[" + idx + "]";
        } else {
            stmt += frName;
        }
        if (isString) stmt += ".c_str()";
    }
    stmt += ket + ";\n";
    return stmt;
}

string V3Task::assignDpiToInternal(const string& lhsName, AstVar* varp) {
    // Create assignment from DPI temporary into internal format
    // DPI temporary is scalar or 1D array (if unpacked array)
    // Internal representation is scalar, 1D, or multi-dimensional array (similar to SV)
    const string frName = varp->name();
    string frstmt;
    string ket;
    const bool useSetWSvlv = TaskDpiUtils::dpiToInternalFrStmt(varp, frName, frstmt, ket);

    const std::vector<std::pair<AstUnpackArrayDType*, int>> dimStrides
        = TaskDpiUtils::unpackDimsAndStrides(varp->dtypep());
    const int total = dimStrides.empty()
                          ? 1
                          : dimStrides.front().first->elementsConst() * dimStrides.front().second;
    const int widthWords = varp->basicp()->widthWords();
    string statements;
    for (int i = 0; i < total; ++i) {
        string lhs = lhsName;
        // extract a scalar from multi-dimensional array (internal format)
        for (auto&& dimStride : dimStrides) {
            const size_t dimIdx = (i / dimStride.second) % dimStride.first->elementsConst();
            lhs += "[" + cvtToStr(dimIdx) + "]";
        }
        // extract a scalar from DPI temporary var that is scalar or 1D array
        if (useSetWSvlv) {
            statements += frstmt + ket + " " + lhs + ", " + frName + " + "
                          + cvtToStr(i * widthWords) + ");\n";
        } else {
            string rhs = frstmt;
            if (!dimStrides.empty()) {
                // e.g. time is 64bit svLogicVector
                const int coef = varp->basicp()->isDpiLogicVec() ? widthWords : 1;
                rhs += "[" + cvtToStr(i * coef) + "]";
            }
            rhs += ket;
            statements += lhs + " = " + rhs + ";\n";
        }
    }
    return statements;
}

void V3Task::taskAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        TaskStateVisitor visitors{nodep};
        const TaskVisitor visitor{nodep, &visitors};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("task", 0, dumpTreeLevel() >= 3);
}
