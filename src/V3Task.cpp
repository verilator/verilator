// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for task nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Const.h"
#include "V3Task.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Graph.h"
#include "V3LinkLValue.h"

#include <map>

//######################################################################
// Graph subclasses

class TaskBaseVertex VL_NOT_FINAL : public V3GraphVertex {
    AstNode* m_impurep = nullptr;  // Node causing impure function w/ outside references
    bool m_noInline = false;  // Marked with pragma
public:
    explicit TaskBaseVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    virtual ~TaskBaseVertex() override = default;
    bool pure() const { return m_impurep == nullptr; }
    AstNode* impureNode() const { return m_impurep; }
    void impure(AstNode* nodep) { m_impurep = nodep; }
    bool noInline() const { return m_noInline; }
    void noInline(bool flag) { m_noInline = flag; }
};

class TaskFTaskVertex final : public TaskBaseVertex {
    // Every task gets a vertex, and we link tasks together based on funcrefs.
    AstNodeFTask* m_nodep;
    AstCFunc* m_cFuncp = nullptr;

public:
    TaskFTaskVertex(V3Graph* graphp, AstNodeFTask* nodep)
        : TaskBaseVertex{graphp}
        , m_nodep{nodep} {}
    virtual ~TaskFTaskVertex() override = default;
    AstNodeFTask* nodep() const { return m_nodep; }
    virtual string name() const override { return nodep()->name(); }
    virtual string dotColor() const override { return pure() ? "black" : "red"; }
    AstCFunc* cFuncp() const { return m_cFuncp; }
    void cFuncp(AstCFunc* nodep) { m_cFuncp = nodep; }
};

class TaskCodeVertex final : public TaskBaseVertex {
    // Top vertex for all calls not under another task
public:
    explicit TaskCodeVertex(V3Graph* graphp)
        : TaskBaseVertex{graphp} {}
    virtual ~TaskCodeVertex() override = default;
    virtual string name() const override { return "*CODE*"; }
    virtual string dotColor() const override { return "green"; }
};

class TaskEdge final : public V3GraphEdge {
public:
    TaskEdge(V3Graph* graphp, TaskBaseVertex* fromp, TaskBaseVertex* top)
        : V3GraphEdge{graphp, fromp, top, 1, false} {}
    virtual ~TaskEdge() override = default;
    virtual string dotLabel() const override { return "w" + cvtToStr(weight()); }
};

//######################################################################

class TaskStateVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  Output:
    //   AstNodeFTask::user3p   // AstScope* this FTask is under
    //   AstNodeFTask::user4p   // GraphFTaskVertex* this FTask is under
    //   AstVar::user4p         // GraphFTaskVertex* this variable is declared in

    AstUser3InUse m_inuser3;
    AstUser4InUse m_inuser4;

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
    std::vector<AstInitial*> m_initialps;  // Initial blocks to move

public:
    // METHODS
    AstScope* getScope(AstNodeFTask* nodep) {
        AstScope* scopep = VN_CAST(nodep->user3p(), Scope);
        UASSERT_OBJ(scopep, nodep, "No scope for function");
        return scopep;
    }
    AstVarScope* findVarScope(AstScope* scopep, AstVar* nodep) {
        const auto iter = m_varToScopeMap.find(std::make_pair(scopep, nodep));
        UASSERT_OBJ(iter != m_varToScopeMap.end(), nodep, "No scope for var");
        return iter->second;
    }
    AstClass* getClassp(AstNodeFTask* nodep) {
        AstClass* classp = m_funcToClassMap[nodep];
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
    void checkPurity(AstNodeFTask* nodep, TaskBaseVertex* vxp) {
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

private:
    TaskFTaskVertex* getFTaskVertex(AstNodeFTask* nodep) {
        if (!nodep->user4p()) nodep->user4p(new TaskFTaskVertex(&m_callGraph, nodep));
        return static_cast<TaskFTaskVertex*>(nodep->user4u().toGraphVertex());
    }

    // VISITORS
    virtual void visit(AstScope* nodep) override {
        // Each FTask is unique per-scope, so AstNodeFTaskRefs do not need
        // pointers to what scope the FTask is to be invoked under.
        // However, to create variables, we need to track the scopes involved.
        // Find all var->varscope mappings, for later cleanup
        for (AstNode* stmtp = nodep->varsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVarScope* vscp = VN_CAST(stmtp, VarScope)) {
                if (vscp->varp()->isFuncLocal()) {
                    UINFO(9, "   funcvsc " << vscp << endl);
                    m_varToScopeMap.insert(
                        std::make_pair(std::make_pair(nodep, vscp->varp()), vscp));
                }
            }
        }
        // Likewise, all FTask->scope mappings
        for (AstNode* stmtp = nodep->blocksp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstNodeFTask* taskp = VN_CAST(stmtp, NodeFTask)) taskp->user3p(nodep);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstAssignW* nodep) override {
        m_assignwp = nodep;
        VL_DO_DANGLING(iterateChildren(nodep), nodep);  // May delete nodep.
        m_assignwp = nullptr;
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
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
        new TaskEdge(&m_callGraph, m_curVxp, getFTaskVertex(nodep->taskp()));
    }
    virtual void visit(AstNodeFTask* nodep) override {
        UINFO(9, "  TASK " << nodep << endl);
        {
            VL_RESTORER(m_curVxp);
            m_curVxp = getFTaskVertex(nodep);
            if (nodep->dpiImport()) m_curVxp->noInline(true);
            if (nodep->classMethod()) m_curVxp->noInline(true);  // Until V3Task supports it
            if (nodep->isConstructor()) {
                m_curVxp->noInline(true);
                m_ctorp = nodep;
                UASSERT_OBJ(m_classp, nodep, "Ctor not under class");
                m_funcToClassMap[nodep] = m_classp;
            }
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstPragma* nodep) override {
        if (nodep->pragType() == AstPragmaType::NO_INLINE_TASK) {
            // Just mark for the next steps, and we're done with it.
            m_curVxp->noInline(true);
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        nodep->user4p(m_curVxp);  // Remember what task it's under
    }
    virtual void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (nodep->varp()->user4u().toGraphVertex() != m_curVxp) {
            if (m_curVxp->pure() && !nodep->varp()->isXTemp()) m_curVxp->impure(nodep);
        }
    }
    virtual void visit(AstClass* nodep) override {
        // Move initial statements into the constructor
        m_initialps.clear();
        m_ctorp = nullptr;
        m_classp = nodep;
        {  // Find m_initialps, m_ctor
            iterateChildren(nodep);
        }
        UASSERT_OBJ(m_ctorp, nodep, "class constructor missing");  // LinkDot always makes it
        for (AstInitial* initialp : m_initialps) {
            if (AstNode* newp = initialp->bodysp()) {
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
    virtual void visit(AstInitial* nodep) override {
        m_initialps.push_back(nodep);
        iterateChildren(nodep);
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TaskStateVisitor(AstNetlist* nodep) {
        m_curVxp = new TaskCodeVertex(&m_callGraph);
        AstNode::user3ClearTree();
        AstNode::user4ClearTree();
        //
        iterate(nodep);
        //
        m_callGraph.removeRedundantEdgesSum(&TaskEdge::followAlwaysTrue);
        m_callGraph.dumpDotFilePrefixed("task_call");
    }
    virtual ~TaskStateVisitor() override = default;
    VL_UNCOPYABLE(TaskStateVisitor);
};

//######################################################################

class TaskRelinkVisitor final : public AstNVisitor {
    // Replace varrefs with new var pointer
private:
    // NODE STATE
    //  Input:
    //   AstVar::user2p         // AstVarScope* to replace varref with

    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        // Similar code in V3Inline
        if (nodep->varp()->user2p()) {  // It's being converted to an alias.
            UINFO(9,
                  "    relinkVar " << cvtToHex(nodep->varp()->user2p()) << " " << nodep << endl);
            AstVarScope* newvscp = VN_CAST(nodep->varp()->user2p(), VarScope);
            UASSERT_OBJ(newvscp, nodep, "not linked");
            nodep->varScopep(newvscp);
            nodep->varp(nodep->varScopep()->varp());
            nodep->name(nodep->varp()->name());
        }
        iterateChildren(nodep);
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TaskRelinkVisitor(AstBegin* nodep) {  // Passed temporary tree
        iterate(nodep);
    }
    virtual ~TaskRelinkVisitor() override = default;
};

//######################################################################
// DPI related utility functions

struct TaskDpiUtils {
    static std::vector<std::pair<AstUnpackArrayDType*, int>>
    unpackDimsAndStrides(AstNodeDType* dtypep) {
        std::vector<std::pair<AstUnpackArrayDType*, int>> dimStrides;
        if (AstUnpackArrayDType* unpackp = VN_CAST(dtypep->skipRefp(), UnpackArrayDType)) {
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
        if (portp->basicp() && portp->basicp()->keyword() == AstBasicDTypeKwd::CHANDLE) {
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
                const AstNodeDType* dtypep = portp->dtypep()->skipRefp();
                frstmt = "VL_SET_" + string(dtypep->charIQWN()) + "_" + frSvType + "(";
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

class TaskVisitor final : public AstNVisitor {
private:
    // NODE STATE
    // Each module:
    //    AstNodeFTask::user1   // True if its been expanded
    // Each funccall
    //  to TaskRelinkVisitor:
    //    AstVar::user2p        // AstVarScope* to replace varref with

    AstUser1InUse m_inuser1;
    AstUser2InUse m_inuser2;

    // TYPES
    enum InsertMode : uint8_t {
        IM_BEFORE,  // Pointing at statement ref is in, insert before this
        IM_AFTER,  // Pointing at last inserted stmt, insert after
        IM_WHILE_PRECOND  // Pointing to for loop, add to body end
    };
    using DpiNames = std::map<const string, std::pair<AstNodeFTask*, std::string>>;

    // STATE
    TaskStateVisitor* m_statep;  // Common state between visitors
    AstNodeModule* m_modp = nullptr;  // Current module
    AstTopScope* m_topScopep = nullptr;  // Current top scope
    AstScope* m_scopep = nullptr;  // Current scope
    InsertMode m_insMode = IM_BEFORE;  // How to insert
    AstNode* m_insStmtp = nullptr;  // Where to insert statement
    int m_modNCalls = 0;  // Incrementing func # for making symbols
    DpiNames m_dpiNames;  // Map of all created DPI functions

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* createFuncVar(AstCFunc* funcp, const string& name, AstVar* examplep) {
        AstVar* newvarp = new AstVar(funcp->fileline(), AstVarType::BLOCKTEMP, name, examplep);
        newvarp->funcLocal(true);
        funcp->addInitsp(newvarp);
        AstVarScope* newvscp = new AstVarScope(funcp->fileline(), m_scopep, newvarp);
        m_scopep->addVarp(newvscp);
        return newvscp;
    }
    AstVarScope* createInputVar(AstCFunc* funcp, const string& name, AstBasicDTypeKwd kwd) {
        AstVar* newvarp = new AstVar(funcp->fileline(), AstVarType::BLOCKTEMP, name,
                                     funcp->findBasicDType(kwd));
        newvarp->funcLocal(true);
        newvarp->direction(VDirection::INPUT);
        funcp->addArgsp(newvarp);
        AstVarScope* newvscp = new AstVarScope(funcp->fileline(), m_scopep, newvarp);
        m_scopep->addVarp(newvscp);
        return newvscp;
    }
    AstVarScope* createVarScope(AstVar* invarp, const string& name) {
        // We could create under either the ref's scope or the ftask's scope.
        // It shouldn't matter, as they are only local variables.
        // We choose to do it under whichever called this function, which results
        // in more cache locality.
        AstVar* newvarp = new AstVar(invarp->fileline(), AstVarType::BLOCKTEMP, name, invarp);
        newvarp->funcLocal(false);
        newvarp->propagateAttrFrom(invarp);
        m_modp->addStmtp(newvarp);
        AstVarScope* newvscp = new AstVarScope(newvarp->fileline(), m_scopep, newvarp);
        m_scopep->addVarp(newvscp);
        return newvscp;
    }

    AstNode* createInlinedFTask(AstNodeFTaskRef* refp, const string& namePrefix,
                                AstVarScope* outvscp) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstNode* newbodysp
            = AstNode::cloneTreeNull(refp->taskp()->stmtsp(), true);  // Maybe nullptr
        AstNode* beginp
            = new AstComment(refp->fileline(), string("Function: ") + refp->name(), true);
        if (newbodysp) beginp->addNext(newbodysp);
        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-newbegi:");
        //
        // Create input variables
        AstNode::user2ClearTree();
        V3TaskConnects tconnects = V3Task::taskConnects(refp, beginp);
        for (const auto& itr : tconnects) {
            AstVar* portp = itr.first;
            AstArg* argp = itr.second;
            AstNode* pinp = argp->exprp();
            portp->unlinkFrBack();
            pushDeletep(portp);  // Remove it from the clone (not original)
            if (!pinp) {
                // Too few arguments in function call
            } else {
                UINFO(9, "     Port " << portp << endl);
                UINFO(9, "      pin " << pinp << endl);
                pinp->unlinkFrBack();  // Relinked to assignment below
                VL_DO_DANGLING(argp->unlinkFrBack()->deleteTree(), argp);  // Args no longer needed
                //
                if (portp->isWritable() && VN_IS(pinp, Const)) {
                    pinp->v3error(
                        "Function/task " + portp->direction().prettyName()  // e.g. "output"
                        + " connected to constant instead of variable: " + portp->prettyNameQ());
                } else if (portp->isInoutish()) {
                    // Correct lvalue; see comments below
                    V3LinkLValue::linkLValueSet(pinp);

                    if (AstVarRef* varrefp = VN_CAST(pinp, VarRef)) {
                        // Connect to this exact variable
                        AstVarScope* localVscp = varrefp->varScopep();
                        UASSERT_OBJ(localVscp, varrefp, "Null var scope");
                        portp->user2p(localVscp);
                        pushDeletep(pinp);
                    } else {
                        pinp->v3warn(
                            E_TASKNSVAR,
                            "Unsupported: Function/task input argument is not simple variable");
                    }
                } else if (portp->isWritable()) {
                    // Make output variables
                    // Correct lvalue; we didn't know when we linked
                    // This is slightly scary; are we sure no decisions were made
                    // before here based on this not being a lvalue?
                    // Doesn't seem so; V3Unknown uses it earlier, but works ok.
                    V3LinkLValue::linkLValueSet(pinp);

                    // Even if it's referencing a varref, we still make a temporary
                    // Else task(x,x,x) might produce incorrect results
                    AstVarScope* tempvscp
                        = createVarScope(portp, namePrefix + "__" + portp->shortName());
                    portp->user2p(tempvscp);
                    AstAssign* assp = new AstAssign(
                        pinp->fileline(), pinp,
                        new AstVarRef(tempvscp->fileline(), tempvscp, VAccess::READ));
                    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ,
                                                    true);  // Ok if in <= block
                    // Put assignment BEHIND of all other statements
                    beginp->addNext(assp);
                } else if (portp->isNonOutput()) {
                    // Make input variable
                    AstVarScope* inVscp
                        = createVarScope(portp, namePrefix + "__" + portp->shortName());
                    portp->user2p(inVscp);
                    AstAssign* assp = new AstAssign(
                        pinp->fileline(),
                        new AstVarRef(inVscp->fileline(), inVscp, VAccess::WRITE), pinp);
                    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ,
                                                    true);  // Ok if in <= block
                    // Put assignment in FRONT of all other statements
                    if (AstNode* afterp = beginp->nextp()) {
                        afterp->unlinkFrBackWithNext();
                        assp->addNext(afterp);
                    }
                    beginp->addNext(assp);
                }
            }
        }
        UASSERT_OBJ(!refp->pinsp(), refp, "Pin wasn't removed by above loop");
        {
            AstNode* nextstmtp;
            for (AstNode* stmtp = beginp; stmtp; stmtp = nextstmtp) {
                nextstmtp = stmtp->nextp();
                if (AstVar* portp = VN_CAST(stmtp, Var)) {
                    // Any I/O variables that fell out of above loop were already linked
                    if (!portp->user2p()) {
                        // Move it to a new localized variable
                        portp->unlinkFrBack();
                        pushDeletep(portp);  // Remove it from the clone (not original)
                        AstVarScope* localVscp
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
        // Iteration requires a back, so put under temporary node
        {
            AstBegin* tempp = new AstBegin(beginp->fileline(), "[EditWrapper]", beginp);
            TaskRelinkVisitor visitor(tempp);
            tempp->stmtsp()->unlinkFrBackWithNext();
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        //
        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-iotask: ");
        return beginp;
    }

    AstNode* createNonInlinedFTask(AstNodeFTaskRef* refp, const string& namePrefix,
                                   AstVarScope* outvscp, AstCNew*& cnewpr) {
        // outvscp is the variable for functions only, if nullptr, it's a task
        UASSERT_OBJ(refp->taskp(), refp, "Unlinked?");
        AstCFunc* cfuncp = m_statep->ftaskCFuncp(refp->taskp());
        UASSERT_OBJ(cfuncp, refp, "No non-inline task associated with this task call?");
        //
        AstNode* beginp
            = new AstComment(refp->fileline(), string("Function: ") + refp->name(), true);
        AstNodeCCall* ccallp;
        if (VN_IS(refp, New)) {
            AstCNew* cnewp = new AstCNew(refp->fileline(), cfuncp);
            cnewp->dtypep(refp->dtypep());
            ccallp = cnewp;
            // Parent AstNew will replace with this CNew
            cnewpr = cnewp;
        } else if (AstMethodCall* mrefp = VN_CAST(refp, MethodCall)) {
            ccallp = new AstCMethodCall(refp->fileline(), mrefp->fromp()->unlinkFrBack(), cfuncp);
            beginp->addNext(ccallp);
        } else {
            ccallp = new AstCCall(refp->fileline(), cfuncp);
            beginp->addNext(ccallp);
        }

        // Convert complicated outputs to temp signals
        V3TaskConnects tconnects = V3Task::taskConnects(refp, refp->taskp()->stmtsp());
        for (const auto& itr : tconnects) {
            AstVar* portp = itr.first;
            AstNode* pinp = itr.second->exprp();
            if (!pinp) {
                // Too few arguments in function call
            } else {
                UINFO(9, "     Port " << portp << endl);
                UINFO(9, "      pin " << pinp << endl);
                if (portp->isWritable() && VN_IS(pinp, Const)) {
                    pinp->v3error(
                        "Function/task " + portp->direction().prettyName()  // e.g. "output"
                        + " connected to constant instead of variable: " + portp->prettyNameQ());
                } else if (portp->isInoutish()) {
                    // Correct lvalue; see comments below
                    V3LinkLValue::linkLValueSet(pinp);

                    if (VN_IS(pinp, VarRef)) {
                        // Connect to this exact variable
                    } else {
                        pinp->v3warn(
                            E_TASKNSVAR,
                            "Unsupported: Function/task input argument is not simple variable");
                    }
                } else if (portp->isWritable()) {
                    // Make output variables
                    // Correct lvalue; we didn't know when we linked
                    // This is slightly scary; are we sure no decisions were made
                    // before here based on this not being a lvalue?
                    // Seems correct assumption; V3Unknown uses it earlier, but works ok.
                    V3LinkLValue::linkLValueSet(pinp);

                    // Even if it's referencing a varref, we still make a temporary
                    // Else task(x,x,x) might produce incorrect results
                    AstVarScope* newvscp
                        = createVarScope(portp, namePrefix + "__" + portp->shortName());
                    portp->user2p(newvscp);
                    pinp->replaceWith(new AstVarRef(newvscp->fileline(), newvscp, VAccess::WRITE));
                    AstAssign* assp = new AstAssign(
                        pinp->fileline(), pinp,
                        new AstVarRef(newvscp->fileline(), newvscp, VAccess::READ));
                    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ,
                                                    true);  // Ok if in <= block
                    // Put assignment BEHIND of all other statements
                    beginp->addNext(assp);
                }
            }
        }
        // First argument is symbol table, then output if a function
        bool needSyms = !refp->taskp()->dpiImport();
        if (needSyms) ccallp->argTypes("vlSymsp");

        if (refp->taskp()->dpiContext()) {
            // __Vscopep
            AstNode* snp = refp->scopeNamep()->unlinkFrBack();
            UASSERT_OBJ(snp, refp, "Missing scoping context");
            ccallp->addArgsp(snp);
            // __Vfilenamep
            ccallp->addArgsp(new AstCMath(refp->fileline(),
                                          "\"" + refp->fileline()->filename() + "\"", 64, true));
            // __Vlineno
            ccallp->addArgsp(new AstConst(refp->fileline(), refp->fileline()->lineno()));
        }

        // Create connections
        AstNode* nextpinp;
        for (AstNode* pinp = refp->pinsp(); pinp; pinp = nextpinp) {
            nextpinp = pinp->nextp();
            // Move pin to the CCall, removing all Arg's
            AstNode* exprp = VN_CAST(pinp, Arg)->exprp();
            exprp->unlinkFrBack();
            ccallp->addArgsp(exprp);
        }

        if (outvscp) ccallp->addArgsp(new AstVarRef(refp->fileline(), outvscp, VAccess::WRITE));

        if (debug() >= 9) beginp->dumpTreeAndNext(cout, "-nitask: ");
        return beginp;
    }

    string dpiprotoName(AstNodeFTask* nodep, AstVar* rtnvarp) const {
        // Return fancy export-ish name for DPI function
        // Variable names are NOT included so differences in only IO names won't matter
        string dpiproto;
        if (nodep->pure()) dpiproto += "pure ";
        if (nodep->dpiContext()) dpiproto += "context ";
        dpiproto += rtnvarp ? rtnvarp->dpiArgType(true, true) : "void";
        dpiproto += " " + nodep->cname() + " (";
        string args;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
                    if (args != "") {
                        args += ", ";
                        dpiproto += ", ";
                    }
                    args += portp->name();  // Leftover so ,'s look nice
                    if (nodep->dpiImport()) dpiproto += portp->dpiArgType(false, false);
                }
            }
        }
        dpiproto += ")";
        return dpiproto;
    }

    AstNode* createDpiTemp(AstVar* portp, const string& suffix) {
        const string stmt = portp->dpiTmpVarType(portp->name() + suffix) + ";\n";
        return new AstCStmt(portp->fileline(), stmt);
    }

    AstNode* createAssignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix,
                                       const string& toSuffix) {
        string stmt = V3Task::assignInternalToDpi(portp, isPtr, frSuffix, toSuffix);
        return new AstCStmt(portp->fileline(), stmt);
    }

    AstNode* createAssignDpiToInternal(AstVarScope* portvscp, const string& frName) {
        // Create assignment from DPI temporary into internal format
        // DPI temporary is scalar or 1D array (if unpacked array)
        // Internal representation is scalar, 1D, or multi-dimensional array (similar to SV)
        AstVar* portp = portvscp->varp();
        string frstmt;
        string ket;
        const bool useSetWSvlv = TaskDpiUtils::dpiToInternalFrStmt(portp, frName, frstmt, ket);
        // Use a AstCMath, as we want V3Clean to mask off bits that don't make sense.
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
            AstNode* srcp = new AstVarRef(portvscp->fileline(), portvscp, VAccess::WRITE);
            // extract a scalar from multi-dimensional array (internal format)
            for (auto&& dimStride : dimStrides) {
                const size_t dimIdx = (i / dimStride.second) % dimStride.first->elementsConst();
                srcp = new AstArraySel(portvscp->fileline(), srcp, dimIdx);
            }
            AstNode* stmtp = nullptr;
            // extract a scalar from DPI temporary var that is scalar or 1D array
            if (useSetWSvlv) {
                AstNode* linesp = new AstText(portvscp->fileline(), frstmt + ket);
                linesp->addNext(srcp);
                linesp->addNext(
                    new AstText(portvscp->fileline(),
                                "," + frName + " + " + cvtToStr(i * widthWords) + ");\n"));
                stmtp = new AstCStmt(portvscp->fileline(), linesp);
            } else {
                string from = frstmt;
                if (!dimStrides.empty()) {
                    // e.g. time is 64bit svLogicVector
                    const int coef = portp->basicp()->isDpiLogicVec() ? widthWords : 1;
                    from += "[" + cvtToStr(i * coef) + "]";
                }
                from += ket;
                AstNode* rhsp = new AstSel(portp->fileline(),
                                           new AstCMath(portp->fileline(), from, cwidth, false), 0,
                                           portp->width());
                stmtp = new AstAssign(portp->fileline(), srcp, rhsp);
            }
            if (i > 0) {
                newp->addNext(stmtp);
            } else {
                newp = stmtp;
            }
        }
        return newp;
    }

    void makeDpiExportWrapper(AstNodeFTask* nodep, AstVar* rtnvarp) {
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();
        AstCFunc* dpip = new AstCFunc(nodep->fileline(), nodep->cname(), m_scopep,
                                      (rtnvarp ? rtnvarp->dpiArgType(true, true) : ""));
        dpip->dontCombine(true);
        dpip->entryPoint(true);
        dpip->isStatic(true);
        dpip->dpiExportWrapper(true);
        dpip->protect(false);
        dpip->cname(nodep->cname());
        // Add DPI reference to top, since it's a global function
        m_topScopep->scopep()->addActivep(dpip);

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
            string cbtype
                = VIdProtect::protect(v3Global.opt.prefix() + "__Vcb_" + nodep->cname() + "_t");
            stmt += cbtype + " __Vcb = (" + cbtype
                    + ")(VerilatedScope::exportFind(__Vscopep, __Vfuncnum));\n";  // Can't use
                                                                                  // static_cast
            // If __Vcb is null the exportFind function throws and error
            dpip->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }

        // Convert input/inout DPI arguments to Internal types
        string args;
        args += ("(" + EmitCBaseVisitor::symClassName()
                 + "*)(__Vscopep->symsp())");  // Upcast w/o overhead
        AstNode* argnodesp = nullptr;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
                    // No createDpiTemp; we make a real internal variable instead
                    // SAME CODE BELOW
                    args += ", ";
                    if (args != "") {
                        argnodesp = argnodesp->addNext(new AstText(portp->fileline(), args, true));
                        args = "";
                    }
                    AstVarScope* outvscp = createFuncVar(dpip, portp->name() + tmpSuffixp, portp);
                    // No information exposure; is already visible in import/export func template
                    outvscp->varp()->protect(false);
                    portp->protect(false);
                    AstVarRef* refp
                        = new AstVarRef(portp->fileline(), outvscp,
                                        portp->isWritable() ? VAccess::WRITE : VAccess::READ);
                    argnodesp = argnodesp->addNextNull(refp);

                    if (portp->isNonOutput()) {
                        std::string frName
                            = portp->isInoutish() && portp->basicp()->isDpiPrimitive()
                                      && portp->dtypep()->skipRefp()->arrayUnpackedElements() == 1
                                  ? "*"
                                  : "";
                        frName += portp->name();
                        dpip->addStmtsp(createAssignDpiToInternal(outvscp, frName));
                    }
                }
            }
        }

        if (rtnvarp) {
            AstVar* portp = rtnvarp;
            // SAME CODE ABOVE
            args += ", ";
            if (args != "") {
                argnodesp = argnodesp->addNext(new AstText(portp->fileline(), args, true));
                args = "";
            }
            AstVarScope* outvscp = createFuncVar(dpip, portp->name() + tmpSuffixp, portp);
            // No information exposure; is already visible in import/export func template
            outvscp->varp()->protect(false);
            AstVarRef* refp = new AstVarRef(portp->fileline(), outvscp,
                                            portp->isWritable() ? VAccess::WRITE : VAccess::READ);
            argnodesp = argnodesp->addNextNull(refp);
        }

        {  // Call the user function
            // Add the variables referenced as VarRef's so that lifetime analysis
            // doesn't rip up the variables on us
            string stmt;
            stmt += "(*__Vcb)(";
            args += ");\n";
            AstCStmt* newp = new AstCStmt(nodep->fileline(), stmt);
            newp->addBodysp(argnodesp);
            VL_DANGLING(argnodesp);
            newp->addBodysp(new AstText(nodep->fileline(), args, true));
            dpip->addStmtsp(newp);
        }

        // Convert output/inout arguments back to internal type
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO() && portp->isWritable() && !portp->isFuncReturn()) {
                    dpip->addStmtsp(createAssignInternalToDpi(portp, true, tmpSuffixp, ""));
                }
            }
        }

        if (rtnvarp) {
            dpip->addStmtsp(createDpiTemp(rtnvarp, ""));
            dpip->addStmtsp(createAssignInternalToDpi(rtnvarp, false, tmpSuffixp, ""));
            string stmt = "return " + rtnvarp->name();
            stmt += rtnvarp->basicp()->isDpiPrimitive() ? ";\n" : "[0];\n";
            dpip->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }
        makePortList(nodep, dpip);
    }

    void makeDpiImportProto(AstNodeFTask* nodep, AstVar* rtnvarp) {
        if (nodep->cname() != AstNode::prettyName(nodep->cname())) {
            nodep->v3error("DPI function has illegal characters in C identifier name: "
                           << AstNode::prettyNameQ(nodep->cname()));
        }
        AstCFunc* dpip = new AstCFunc(nodep->fileline(), nodep->cname(), m_scopep,
                                      (rtnvarp ? rtnvarp->dpiArgType(true, true)
                                               // Tasks (but not void functions)
                                               // return bool indicating disabled
                                               : nodep->dpiTask() ? "int" : ""));
        dpip->dontCombine(true);
        dpip->entryPoint(false);
        dpip->funcPublic(true);
        dpip->isStatic(false);
        dpip->protect(false);
        dpip->pure(nodep->pure());
        dpip->dpiImport(true);
        // Add DPI reference to top, since it's a global function
        m_topScopep->scopep()->addActivep(dpip);
        makePortList(nodep, dpip);
    }

    bool duplicatedDpiProto(AstNodeFTask* nodep, const string& dpiproto) {
        // Only create one DPI extern prototype for each specified cname
        // as it's legal for the user to attach multiple tasks to one dpi cname
        const auto iter = m_dpiNames.find(nodep->cname());
        if (iter == m_dpiNames.end()) {
            m_dpiNames.emplace(nodep->cname(), std::make_pair(nodep, dpiproto));
            return false;
        } else if (iter->second.second != dpiproto) {
            nodep->v3error(
                "Duplicate declaration of DPI function with different formal arguments: "
                << nodep->prettyNameQ() << '\n'
                << nodep->warnContextPrimary() << '\n'
                << nodep->warnMore() << "... New prototype:      " << dpiproto << '\n'
                << iter->second.first->warnOther()
                << "... Original prototype: " << iter->second.second << '\n'
                << iter->second.first->warnContextSecondary());
            return true;
        } else {
            return true;
        }
    }

    void makePortList(AstNodeFTask* nodep, AstCFunc* dpip) {
        // Copy nodep's list of function I/O to the new dpip c function
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    // Move it to new function
                    AstVar* newPortp = portp->cloneTree(false);
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

    void bodyDpiImportFunc(AstNodeFTask* nodep, AstVarScope* rtnvscp, AstCFunc* cfuncp) {
        const char* const tmpSuffixp = V3Task::dpiTemporaryVarSuffix();
        // Convert input/inout arguments to DPI types
        string args;
        for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                AstVarScope* portvscp
                    = VN_CAST(portp->user2p(), VarScope);  // Remembered when we created it earlier
                if (portp->isIO() && !portp->isFuncReturn() && portvscp != rtnvscp
                    && portp->name() != "__Vscopep"  // Passed to dpiContext, not callee
                    && portp->name() != "__Vfilenamep" && portp->name() != "__Vlineno") {

                    if (args != "") args += ", ";

                    if (portp->isDpiOpenArray()) {
                        AstNodeDType* dtypep = portp->dtypep()->skipRefp();
                        if (VN_IS(dtypep, DynArrayDType) || VN_IS(dtypep, QueueDType)) {
                            v3fatalSrc("Passing dynamic array or queue as actual argument to DPI "
                                       "open array is not yet supported");
                        }

                        // Ideally we'd make a table of variable
                        // characteristics, and reuse it wherever we can
                        // At least put them into the module's CTOR as static?
                        string propName = portp->name() + "__Vopenprops";
                        string propCode = portp->vlPropDecl(propName);
                        cfuncp->addStmtsp(new AstCStmt(portp->fileline(), propCode));
                        //
                        // At runtime we need the svOpenArrayHandle to
                        // point to this task & thread's data, in addition
                        // to static info about the variable
                        string name = portp->name() + "__Vopenarray";
                        string varCode
                            = ("VerilatedDpiOpenVar "
                               // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                               + name + " (&" + propName + ", &" + portp->name() + ");\n");
                        cfuncp->addStmtsp(new AstCStmt(portp->fileline(), varCode));
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
            string stmt = "Verilated::dpiContext(__Vscopep, __Vfilenamep, __Vlineno);\n";
            cfuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }

        {  // Call the user function
            string stmt;
            if (rtnvscp) {  // isFunction will no longer work as we unlinked the return var
                cfuncp->addStmtsp(createDpiTemp(rtnvscp->varp(), tmpSuffixp));
                stmt = rtnvscp->varp()->name() + tmpSuffixp;
                stmt += rtnvscp->varp()->basicp()->isDpiPrimitive() ? " = " : "[0] = ";
            }
            stmt += nodep->cname() + "(" + args + ");\n";
            cfuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
        }

        // Convert output/inout arguments back to internal type
        for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                portp->protect(false);  // No additional exposure - already part of shown proto
                if (portp->isIO() && (portp->isWritable() || portp->isFuncReturn())
                    && !portp->isDpiOpenArray()) {
                    AstVarScope* portvscp = VN_CAST(
                        portp->user2p(), VarScope);  // Remembered when we created it earlier
                    cfuncp->addStmtsp(
                        createAssignDpiToInternal(portvscp, portp->name() + tmpSuffixp));
                }
            }
        }
    }

    AstCFunc* makeUserFunc(AstNodeFTask* nodep, bool ftaskNoInline) {
        // Given a already cloned node, make a public C function, or a non-inline C function
        // Probably some of this work should be done later, but...
        // should the type of the function be bool/uint32/64 etc (based on lookup) or IData?
        AstNode::user2ClearTree();
        AstVar* rtnvarp = nullptr;
        if (nodep->isFunction()) {
            AstVar* portp = VN_CAST(nodep->fvarp(), Var);
            UASSERT_OBJ(portp, nodep, "function without function output variable");
            if (!portp->isFuncReturn()) nodep->v3error("Not marked as function return var");
            if (nodep->dpiImport() || nodep->dpiExport()) {
                AstBasicDType* bdtypep = portp->dtypep()->basicp();
                if (!bdtypep->isDpiPrimitive()) {
                    if (bdtypep->isDpiBitVec() && portp->width() > 32) {
                        portp->v3error("DPI function may not return a > 32 bits wide type "
                                       "other than basic types.\n"
                                       + V3Error::warnMore()
                                       + "... Suggest make it an output argument instead?");
                    }
                    if (bdtypep->isDpiLogicVec()) {
                        portp->v3error("DPI function may not return a 4-state type "
                                       "other than a single 'logic' (IEEE 1800-2017 35.5.5)");
                    }
                }
            } else {
                if (portp->isWide()) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Public functions with return > 64 bits wide.\n"
                                      + V3Error::warnMore()
                                      + "... Suggest make it an output argument instead?");
                }
            }

            if (ftaskNoInline || nodep->dpiExport()) {
                portp->funcReturn(false);  // Converting return to 'outputs'
            }
            portp->unlinkFrBack();
            rtnvarp = portp;
            rtnvarp->funcLocal(true);
            rtnvarp->name(rtnvarp->name()
                          + "__Vfuncrtn");  // Avoid conflict with DPI function name
            if (nodep->dpiImport() || nodep->dpiExport()) rtnvarp->protect(false);
        }

        if (nodep->dpiImport()) {
            if (nodep->dpiOpenChild()) {  // The parent will make the dpi proto
                UASSERT_OBJ(!nodep->dpiOpenParent(), nodep,
                            "DPI task should be parent or wrapper, not both");
            } else {  // Parent or not open child, make wrapper
                string dpiproto = dpiprotoName(nodep, rtnvarp);
                if (!duplicatedDpiProto(nodep, dpiproto)) makeDpiImportProto(nodep, rtnvarp);
                if (nodep->dpiOpenParent()) {
                    // No need to make more than just the c prototype, children will
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return nullptr;
                }
            }

        } else if (nodep->dpiExport()) {
            string dpiproto = dpiprotoName(nodep, rtnvarp);
            if (!duplicatedDpiProto(nodep, dpiproto)) makeDpiExportWrapper(nodep, rtnvarp);
        }

        AstVarScope* rtnvscp = nullptr;
        if (rtnvarp) {
            rtnvscp = new AstVarScope(rtnvarp->fileline(), m_scopep, rtnvarp);
            m_scopep->addVarp(rtnvscp);
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
        string name = ((nodep->name() == "new") ? "new" : prefix + nodep->name() + suffix);
        AstCFunc* cfuncp = new AstCFunc(
            nodep->fileline(), name, m_scopep,
            ((nodep->taskPublic() && rtnvarp) ? rtnvarp->cPubArgType(true, true) : ""));
        // It's ok to combine imports because this is just a wrapper;
        // duplicate wrappers can get merged.
        cfuncp->dontCombine(!nodep->dpiImport());
        cfuncp->entryPoint(!nodep->dpiImport());
        cfuncp->funcPublic(nodep->taskPublic());
        cfuncp->dpiExport(nodep->dpiExport());
        cfuncp->dpiImportWrapper(nodep->dpiImport());
        cfuncp->isStatic(!(nodep->dpiImport() || nodep->taskPublic() || nodep->classMethod()));
        cfuncp->isVirtual(nodep->isVirtual());
        cfuncp->pure(nodep->pure());
        if (nodep->name() == "new") {
            cfuncp->isConstructor(true);
            AstClass* classp = m_statep->getClassp(nodep);
            if (classp->extendsp()) {
                cfuncp->ctorInits(EmitCBaseVisitor::prefixNameProtect(classp->extendsp()->classp())
                                  + "(vlSymsp)");
            }
        }
        // cfuncp->dpiImport   // Not set in the wrapper - the called function has it set
        if (cfuncp->dpiExport()) cfuncp->cname(nodep->cname());

        bool needSyms = !nodep->dpiImport();
        if (needSyms) {
            if (nodep->taskPublic()) {
                // We need to get a pointer to all of our variables (may
                // have eval'ed something else earlier)
                cfuncp->addInitsp(new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symClassVar()
                                                                      + " = this->__VlSymsp;\n"));
            } else {
                // Need symbol table
                cfuncp->argTypes(EmitCBaseVisitor::symClassVar());
                if (cfuncp->name() == "new") {
                    cfuncp->addInitsp(
                        new AstCStmt(nodep->fileline(),
                                     VIdProtect::protect("_ctor_var_reset") + "(vlSymsp);\n"));
                }
            }
        }
        if (nodep->dpiContext()) {
            // First three args go to dpiContext call
            createInputVar(cfuncp, "__Vscopep", AstBasicDTypeKwd::SCOPEPTR);
            createInputVar(cfuncp, "__Vfilenamep", AstBasicDTypeKwd::CHARPTR);
            createInputVar(cfuncp, "__Vlineno", AstBasicDTypeKwd::INT);
        }

        if (!nodep->dpiImport()) {
            cfuncp->addInitsp(
                new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign() + "\n"));
        }

        if (nodep->dpiExport()) {
            AstScopeName* snp = nodep->scopeNamep();
            UASSERT_OBJ(snp, nodep, "Missing scoping context");
            snp->dpiExport(
                true);  // The AstScopeName is really a statement(ish) for tracking, not a function
            snp->unlinkFrBack();
            cfuncp->addInitsp(snp);
        }

        // Create list of arguments and move to function
        for (AstNode *nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
                if (portp->isIO()) {
                    // Move it to new function
                    portp->unlinkFrBack();
                    portp->funcLocal(true);
                    cfuncp->addArgsp(portp);
                } else {
                    // "Normal" variable, mark inside function
                    portp->funcLocal(true);
                }
                AstVarScope* newvscp = new AstVarScope(portp->fileline(), m_scopep, portp);
                m_scopep->addVarp(newvscp);
                portp->user2p(newvscp);
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
            bodysp->unlinkFrBackWithNext();
            cfuncp->addStmtsp(bodysp);
        }
        if (nodep->dpiImport()) bodyDpiImportFunc(nodep, rtnvscp, cfuncp);

        // Return statement
        if (rtnvscp && nodep->taskPublic()) {
            cfuncp->addFinalsp(new AstCReturn(
                rtnvscp->fileline(), new AstVarRef(rtnvscp->fileline(), rtnvscp, VAccess::READ)));
        }
        // Replace variable refs
        // Iteration requires a back, so put under temporary node
        {
            AstBegin* tempp = new AstBegin(cfuncp->fileline(), "[EditWrapper]", cfuncp);
            TaskRelinkVisitor visitor(tempp);
            tempp->stmtsp()->unlinkFrBackWithNext();
            VL_DO_DANGLING(tempp->deleteTree(), tempp);
        }
        // Delete rest of cloned task and return new func
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        if (debug() >= 9) cfuncp->dumpTree(cout, "-userFunc: ");
        return cfuncp;
    }

    void iterateIntoFTask(AstNodeFTask* nodep) {
        // Iterate into the FTask we are calling.  Note it may be under a different
        // scope then the caller, so we need to restore state.
        VL_RESTORER(m_scopep);
        VL_RESTORER(m_insMode);
        VL_RESTORER(m_insStmtp);
        {
            m_scopep = m_statep->getScope(nodep);
            iterate(nodep);
        }
    }
    AstNode* insertBeforeStmt(AstNode* nodep, AstNode* newp) {
        // Return node that must be visited, if any
        // See also AstNode::addBeforeStmt; this predates that function
        if (debug() >= 9) nodep->dumpTree(cout, "-newstmt:");
        UASSERT_OBJ(m_insStmtp, nodep, "Function not underneath a statement");
        AstNode* visitp = nullptr;
        if (m_insMode == IM_BEFORE) {
            // Add the whole thing before insertAt
            UINFO(5, "     IM_Before  " << m_insStmtp << endl);
            if (debug() >= 9) newp->dumpTree(cout, "-newfunc:");
            m_insStmtp->addHereThisAsNext(newp);
        } else if (m_insMode == IM_AFTER) {
            UINFO(5, "     IM_After   " << m_insStmtp << endl);
            m_insStmtp->addNextHere(newp);
        } else if (m_insMode == IM_WHILE_PRECOND) {
            UINFO(5, "     IM_While_Precond " << m_insStmtp << endl);
            AstWhile* whilep = VN_CAST(m_insStmtp, While);
            UASSERT_OBJ(whilep, nodep, "Insert should be under WHILE");
            whilep->addPrecondsp(newp);
            visitp = newp;
        } else {
            nodep->v3fatalSrc("Unknown InsertMode");
        }
        m_insMode = IM_AFTER;
        m_insStmtp = newp;
        return visitp;
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modNCalls);
        {
            m_modp = nodep;
            m_insStmtp = nullptr;
            m_modNCalls = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstTopScope* nodep) override {
        m_topScopep = nodep;
        iterateChildren(nodep);
    }
    virtual void visit(AstScope* nodep) override {
        m_scopep = nodep;
        m_insStmtp = nullptr;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        // Includes handling AstMethodCall, AstNew
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked?");
        iterateIntoFTask(nodep->taskp());  // First, do hierarchical funcs
        UINFO(4, " FTask REF   " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree(cout, "-inlfunc:");
        UASSERT_OBJ(m_scopep, nodep, "func ref not under scope");
        string namePrefix = ((VN_IS(nodep, FuncRef) ? "__Vfunc_" : "__Vtask_")
                             + nodep->taskp()->shortName() + "__" + cvtToStr(m_modNCalls++));
        // Create output variable
        AstVarScope* outvscp = nullptr;
        if (nodep->taskp()->isFunction()) {
            // Not that it's a FUNCREF, but that we're calling a function (perhaps as a task)
            outvscp
                = createVarScope(VN_CAST(nodep->taskp()->fvarp(), Var), namePrefix + "__Vfuncout");
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
        // Replace the ref
        AstNode* visitp = nullptr;
        if (VN_IS(nodep, New)) {
            UASSERT_OBJ(!nodep->isStatement(), nodep, "new is non-stmt");
            UASSERT_OBJ(cnewp, nodep, "didn't create cnew for new");
            nodep->replaceWith(cnewp);
            visitp = insertBeforeStmt(nodep, beginp);
        } else if (!nodep->isStatement()) {
            UASSERT_OBJ(nodep->taskp()->isFunction(), nodep, "func reference to non-function");
            AstVarRef* outrefp = new AstVarRef(nodep->fileline(), outvscp, VAccess::READ);
            nodep->replaceWith(outrefp);
            // Insert new statements
            visitp = insertBeforeStmt(nodep, beginp);
        } else {
            if (nodep->taskp()->isFunction()) {
                nodep->v3warn(
                    IGNOREDRETURN,
                    "Ignoring return value of non-void function (IEEE 1800-2017 13.4.1)");
            }
            // outvscp maybe non-nullptr if calling a function in a taskref,
            // but if so we want to simply ignore the function result
            nodep->replaceWith(beginp);
        }
        // Cleanup
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        UINFO(4, "  FTask REF Done.\n");
        // Visit nodes that normal iteration won't find
        if (visitp) iterateAndNextNull(visitp);
    }
    virtual void visit(AstNodeFTask* nodep) override {
        UINFO(4, " Inline   " << nodep << endl);
        VL_RESTORER(m_insMode);
        VL_RESTORER(m_insStmtp);
        m_insMode = IM_BEFORE;
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
                AstNodeFTask* clonedFuncp = nodep->cloneTree(false);
                if (nodep->isConstructor()) m_statep->remapFuncClassp(nodep, clonedFuncp);

                AstCFunc* cfuncp = makeUserFunc(clonedFuncp, m_statep->ftaskNoInline(nodep));
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
                if (AstVar* portp = VN_CAST(nodep->fvarp(), Var)) {
                    AstVarScope* vscp = m_statep->findVarScope(m_scopep, portp);
                    UINFO(9, "   funcremovevsc " << vscp << endl);
                    VL_DO_DANGLING(pushDeletep(vscp->unlinkFrBack()), vscp);
                }
            }
            for (AstNode *nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp = nextp) {
                nextp = stmtp->nextp();
                if (AstVar* portp = VN_CAST(stmtp, Var)) {
                    AstVarScope* vscp = m_statep->findVarScope(m_scopep, portp);
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
    virtual void visit(AstWhile* nodep) override {
        // Special, as statements need to be put in different places
        // Preconditions insert first just before themselves (the normal
        // rule for other statement types)
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->precondsp());
        // Conditions insert first at end of precondsp.
        m_insMode = IM_WHILE_PRECOND;
        m_insStmtp = nodep;
        iterateAndNextNull(nodep->condp());
        // Body insert just before themselves
        m_insStmtp = nullptr;  // First thing should be new statement
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        // Done the loop
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    virtual void visit(AstNodeFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "For statements should have been converted to while statements in V3Begin.cpp");
    }
    virtual void visit(AstNodeStmt* nodep) override {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        m_insMode = IM_BEFORE;
        m_insStmtp = nodep;
        iterateChildren(nodep);
        m_insStmtp = nullptr;  // Next thing should be new statement
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    TaskVisitor(AstNetlist* nodep, TaskStateVisitor* statep)
        : m_statep{statep} {
        iterate(nodep);
    }
    virtual ~TaskVisitor() override = default;
};

//######################################################################
// Task class functions

V3TaskConnects V3Task::taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp) {
    // Output list will be in order of the port declaration variables (so
    // func calls are made right in C)
    // Missing pin/expr?  We return (pinvar, nullptr)
    // Extra   pin/expr?  We clean it up

    std::map<const std::string, int> nameToIndex;
    V3TaskConnects tconnects;
    UASSERT_OBJ(nodep->taskp(), nodep, "unlinked");

    // Find ports
    int tpinnum = 0;
    AstVar* sformatp = nullptr;
    for (AstNode* stmtp = taskStmtsp; stmtp; stmtp = stmtp->nextp()) {
        if (AstVar* portp = VN_CAST(stmtp, Var)) {
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
        AstArg* argp = VN_CAST(pinp, Arg);
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
        AstVar* portp = tconnects[i].first;
        if (!tconnects[i].second || !tconnects[i].second->exprp()) {
            AstNode* newvaluep = nullptr;
            if (!portp->valuep()) {
                nodep->v3error("Missing argument on non-defaulted argument "
                               << portp->prettyNameQ() << " in function call to "
                               << nodep->taskp()->prettyTypeName());
                newvaluep = new AstConst(nodep->fileline(), AstConst::Unsized32(), 0);
            } else if (!VN_IS(portp->valuep(), Const)) {
                // The default value for this port might be a constant
                // expression that hasn't been folded yet. Try folding it
                // now; we don't have much to lose if it fails.
                newvaluep = V3Const::constifyParamsEdit(portp->valuep());
                if (!VN_IS(newvaluep, Const)) {
                    // Problem otherwise is we might have a varref, task
                    // call, or something else that only makes sense in the
                    // domain of the function, not the callee.
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Non-constant default value in missing argument "
                                      << portp->prettyNameQ() << " in function call to "
                                      << nodep->taskp()->prettyTypeName());
                    newvaluep = new AstConst(nodep->fileline(), AstConst::Unsized32(), 0);
                } else {
                    newvaluep = newvaluep->cloneTree(true);
                }
            } else {
                newvaluep = portp->valuep()->cloneTree(true);
            }
            // To avoid problems with callee needing to know to deleteTree
            // or not, we make this into a pin
            UINFO(9, "Default pin for " << portp << endl);
            AstArg* newp = new AstArg(nodep->fileline(), portp->name(), newvaluep);
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
            AstArg* argp = tconnects[i].second;
            UASSERT_OBJ(argp, nodep, "Lost argument in func conversion");
            nodep->addPinsp(argp);
        }
    }

    if (debug() >= 9) {  // LCOV_EXCL_START
        nodep->dumpTree(cout, "-ftref-out: ");
        for (int i = 0; i < tpinnum; ++i) {
            UINFO(0, "   pin " << i << "  conn=" << cvtToHex(tconnects[i].second) << endl);
        }
    }  // LCOV_EXCL_STOP
    return tconnects;
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
    string frName = frPrefix + portp->name() + frSuffix;
    string toName = portp->name() + toSuffix;
    size_t unpackSize = 1;  // non-unpacked array is treated as size 1
    int unpackDim = 0;
    if (AstUnpackArrayDType* unpackp = VN_CAST(portp->dtypep()->skipRefp(), UnpackArrayDType)) {
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
                + string(portp->dtypep()->skipRefp()->charIQWN()) + "(" + cvtToStr(portp->width())
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
            = portp->basicp() && portp->basicp()->keyword() == AstBasicDTypeKwd::CHANDLE;
        const bool isString
            = portp->basicp() && portp->basicp()->keyword() == AstBasicDTypeKwd::STRING;
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

const char* V3Task::dpiTemporaryVarSuffix() {
    static const char* const suffix = "__Vcvt";
    return suffix;
}

void V3Task::taskAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        TaskStateVisitor visitors(nodep);
        TaskVisitor visitor(nodep, &visitors);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("task", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
