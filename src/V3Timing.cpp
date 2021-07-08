// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace return/continue with jumps
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
// Methods for handing process preemption.
//   1. Process maps to C++ coroutines/quickthreads (or likewise).
//      Save and restore it.
//        Upside: IEEE spec's intent, supports tasks
//        Downside: Slow, complicated to optimize
//   2. Split code around each delay point into separate processes.
//      Each DELAY schedules the new event, then does JUMPGO to end of block
//      New event for each delay point, with JUMPGO into where (last) delay was
//      New process triggering on each new event.
//        Upside: Fast after optimization for small blocks
//        Upside: Easy to split statements
//        Downside: Huge code explosion for e.g. "if () #1; test(1); if () #1; test(2); ...."
//   3. Convert into a FSM, with a state value (for a given always)
//      and state (for a given delay point) and event (to process state)
//        Upside: Minimal storage
//        Downside: Harder to split statements for separate optimization
//   For now we use approach 3 and hope optimizations do well
//*************************************************************************
// V3Timing's Transformations:
//
//    Each procedure
//      If has any delayed statement:
//      Assign FSM state# to each delay
//      Existing procedure edited to handle initial activation of the block
//        ALWAYS/INITIAL
//          IF(EQ(fsm, 0))
//            JUMPBLOCK
//               statements up to first delay
//               DELAY here replaced with:
//                  ASSIGN(fsm, <state#>)
//                  TIMEDEVENT(d, newevent)
//                  JUMPGO(endlabel)
//               statements here removed
//             JUMPLABEL(endlabel)
//
//      Procedure duplicated to activate on timed event
//        ALWAYS SENSETREE(newevent)
//          JUMPBLOCK ...
//            IF(EQ(fsm, 1))
//               JUMPGO(fsm, labelstate1)
//            else IF(EQ(fsm, 2))
//               JUMPGO(fsm, labelstate2)
//            ...
//            stmts_pre
//            DELAY here replaced with:
//              ASSIGN(fsm, <state#>)
//              TIMEDEVENT(delaytime, newevent)
//              JUMPGO(endlabel)
//              JUMPLABEL(labelstate2)
//            // code here entered when state 2 resumes
//            stmts_post
//
//    Through optimizations unnecessary JUMPGO/JUMPLABELs are removed
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Timing.h"
#include "V3Ast.h"
#include "V3Stats.h"

#include <map>

//######################################################################

// FIXME needed?
class TimingState final {
    // NODE STATE
    // AstDelay::user1  -> int, state assignment
    AstUser1InUse m_inuser1;

    // MEMBERS
    AstVarScope* m_eventVarScp = nullptr;  // FSM event variable for procedure
    AstVarScope* m_fsmVarScp = nullptr;  // FSM state variable for procedure
public:
    int m_procNum = 0;  // Procedure number
    AstNodeModule* m_modp = nullptr;  // Current module
    AstScope* m_scopep = nullptr;  // Current scope

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* getCreateEventVarScp(FileLine* fileline) {
        if (!m_eventVarScp) {
            string name = "__vProc" + cvtToStr(m_procNum) + "Event";
            AstVar* varp = new AstVar(fileline, AstVarType::MODULETEMP, name,
                                      m_modp->findBasicDType(AstBasicDTypeKwd::EVENTVALUE));
            m_modp->addStmtp(varp);
            m_eventVarScp = new AstVarScope(fileline, m_scopep, varp);
            m_scopep->addVarp(m_eventVarScp);
        }
        return m_eventVarScp;
    }
    AstVarScope* getCreateFsmVarScp(FileLine* fl) {
        if (!m_fsmVarScp) {
            // TODO change width to CData at end-of-time for small FSMs
            // (Also makes more likely would land next to Event var)
            AstVar* varp = new AstVar(fl, AstVarType::MODULETEMP, fsmName(), VFlagBitPacked(), 32);
            m_modp->addStmtp(varp);
            m_fsmVarScp = new AstVarScope(fl, m_scopep, varp);
            m_fsmVarScp->fileline()->modifyWarnOff(V3ErrorCode::UNOPTFLAT,
                                                   true);  // FIXME remove, teach optimizer
            m_scopep->addVarp(m_fsmVarScp);
        }
        return m_fsmVarScp;
    }
    AstNode* newFsmEqConst(FileLine* fl, int state) {
        return new AstEq(fl, new AstConst(fl, state),
                         new AstVarRef(fl, getCreateFsmVarScp(fl), VAccess::READ));
    }
    string fsmName() const { return "__vProc" + cvtToStr(m_procNum) + "Fsm"; }

    // CONSTRUCTORS
    TimingState() = default;
    ~TimingState() = default;
    void initProcedure() {
        m_eventVarScp = nullptr;
        m_fsmVarScp = nullptr;
    }
};

//######################################################################
// Visit a procedure being rebuilt

class TimingProcedureVisitor final : public AstNVisitor {
    // MEMBERS
    TimingState& m_state;  // State
    bool m_newProc;  // Creating always from an initial block
    AstJumpLabel* m_exitLabelp;  // Label to exit procedure
    using JumpTableMap = std::map<int, AstJumpLabel*>;
    JumpTableMap m_jumpTable;  // Map of states to jump locations

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstJumpLabel* newLabelp(AstNode* nodep) {
        // Create new JumpBlock/JumpLabel, return label for later insertion at appropriate point
        AstJumpBlock* blockp = new AstJumpBlock(nodep->fileline(), nullptr);
        AstJumpLabel* labelp = new AstJumpLabel(nodep->fileline(), blockp);
        blockp->labelp(labelp);
        // Returned labelp must be tree inserted
        // block will be inserted by buildTable
        return labelp;
    }
    AstJumpBlock* buildJumpBlocks(AstJumpBlock* upblockp) {
        for (JumpTableMap::iterator it = m_jumpTable.begin(); it != m_jumpTable.end(); ++it) {
            AstJumpLabel* labelp = it->second;
            if (labelp != m_exitLabelp) {
                AstJumpBlock* newblockp = labelp->blockp();
                AstNode* stmtsp = upblockp->stmtsp();
                if (stmtsp) newblockp->addStmtsp(stmtsp->unlinkFrBackWithNext());
                upblockp->addStmtsp(newblockp);
                upblockp = newblockp;
            }
        }
        return upblockp;
    }
    void buildTable(AstJumpBlock* upblockp) {
        AstNode* newp = nullptr;
        AstNodeIf* lastIfp = nullptr;
        for (JumpTableMap::iterator it = m_jumpTable.begin(); it != m_jumpTable.end(); ++it) {
            AstJumpLabel* labelp = it->second;
            // Build  IF(EQ(CONST(state), fsmvar)) JUMPGO(label)
            //           ELSE ...
            // TODO support emitting case statements, so compiler may make a jump table
            // FIXME probably better location for this so can optimize if set later
            AstNode* stmtp = new AstAssign(
                labelp->fileline(),
                new AstVarRef(labelp->fileline(), m_state.getCreateFsmVarScp(labelp->fileline()),
                              VAccess::WRITE),
                new AstConst(labelp->fileline(), 0));
            stmtp->addNext(new AstJumpGo(labelp->fileline(), labelp));
            AstIf* ifp = new AstIf(labelp->fileline(),
                                   m_state.newFsmEqConst(labelp->fileline(), it->first), stmtp);
            if (!newp) {
                newp = ifp;
            } else {
                lastIfp->addElsesp(ifp);
            }
            lastIfp = ifp;
        }
        if (debug() >= 9) newp->dumpTree(cout, "-table: ");
        if (newp) {
            if (upblockp->stmtsp()) {
                upblockp->stmtsp()->addHereThisAsNext(newp);
            } else {
                upblockp->addStmtsp(newp);
            }
        }
    }
    // VISITORS
    virtual void visit(AstNodeProcedure* nodep) VL_OVERRIDE {
        AstNode* stmtsp = nodep->bodysp();
        // Keep any AstVars under the function not under the new JumpLabel/If
        while (VN_IS(stmtsp, Var)) stmtsp = stmtsp->nextp();
        // Move all other statements under end label, so can branch past it
        AstJumpBlock* blockp = new AstJumpBlock(nodep->fileline(), nullptr);
        m_exitLabelp = new AstJumpLabel(nodep->fileline(), blockp);
        blockp->labelp(m_exitLabelp);
        blockp->addEndStmtsp(m_exitLabelp);
        if (stmtsp) blockp->addStmtsp(stmtsp->unlinkFrBackWithNext());
        if (!m_newProc) {
            // For existing procedure, allow activate only if state == 0
            AstIf* ifp = new AstIf(nodep->fileline(), m_state.newFsmEqConst(nodep->fileline(), 0),
                                   blockp);
            nodep->addStmtp(ifp);
        } else {
            nodep->addStmtp(blockp);
        }
        // When FSM is inactive, we don't process any of the reactivate block
        // m_jumpTable[0 /*state*/] = m_exitLabelp;
        {  //
            iterateChildren(nodep);
        }
        if (m_newProc) {
            // Back-insert the jump blocks and state table
            buildTable(buildJumpBlocks(blockp));
        }
        m_exitLabelp = nullptr;
    }
    virtual void visit(AstDelay* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        int state = nodep->user1();
        UASSERT_OBJ(state, nodep, "delay state not assigned in TimingVisitor::AstDelay");
        AstNode* newp = new AstAssign(nodep->fileline(),
                                      new AstVarRef(nodep->fileline(),
                                                    m_state.getCreateFsmVarScp(nodep->fileline()),
                                                    VAccess::WRITE),
                                      new AstConst(nodep->fileline(), state));
        newp->addNext(new AstTimedEvent(
            nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
            new AstVarRef(nodep->fileline(), m_state.getCreateEventVarScp(nodep->fileline()),
                          VAccess::WRITE)));
        newp->addNext(new AstJumpGo(nodep->fileline(), m_exitLabelp));
        if (m_newProc) {
            AstJumpLabel* restoreLabelp = newLabelp(nodep);
            m_jumpTable[state] = restoreLabelp;
            newp->addNext(restoreLabelp);
            newp->addNext(
                new AstComment(nodep->fileline(),
                               string("From " + m_state.fsmName() + " state ") + cvtToStr(state)));
        } else {
            // Any statements (at this statement level) can never execute
            // We might as well get rid of them now (V3Const will also clean up)
            while (nodep->nextp() && !VN_IS(nodep->nextp(), JumpLabel)) {
                nodep->nextp()->unlinkFrBack()->deleteTree();
            }
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstNodeMath*) VL_OVERRIDE {}
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    TimingProcedureVisitor(TimingState& stater, AstNodeProcedure* procedurep, bool newProc)
        : m_state(stater)
        , m_newProc(newProc)
        , m_exitLabelp(nullptr) {
        iterate(procedurep);
    }
    ~TimingProcedureVisitor() {}
};

//######################################################################

class TimingVisitor final : public AstNVisitor {
private:
    // STATE
    TimingState m_state;  // State information
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNodeProcedure* m_procedurep = nullptr;  // Current initial/final/always
    int m_delays = 0;  // Delays within procedure
    VDouble0 m_statDelays;  // Statistic tracking
    VDouble0 m_statProcedures;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_state.m_modp;
        {
            m_state.m_modp = nodep;
            iterateChildren(nodep);
        }
        m_state.m_modp = origModp;
        if (!m_state.m_modp) m_state.m_procNum = 0;
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        AstScope* oldScopep = m_state.m_scopep;
        {
            m_state.m_scopep = nodep;
            iterateChildren(nodep);
        }
        m_state.m_scopep = oldScopep;
    }
    virtual void visit(AstNodeProcedure* nodep) VL_OVERRIDE {
        m_procedurep = nodep;
        m_delays = 0;
        m_state.initProcedure();
        iterateChildren(nodep);
        if (m_delays) {
            // Activation & FSM variables
            ++m_state.m_procNum;
            ++m_statProcedures;
            AstNodeProcedure* alwaysp = nullptr;
            {
                FileLine* fl = nodep->fileline();
                // For initial, create version with and without triggering statements
                AstSenTree* sensesp = new AstSenTree(
                    fl, new AstSenItem(
                            fl, VEdgeType::ET_HIGHEDGE,
                            new AstVarRef(fl, m_state.getCreateEventVarScp(nodep->fileline()),
                                          VAccess::READ)));
                alwaysp = new AstAlways(fl, VAlwaysKwd::ALWAYS, sensesp,
                                        nodep->bodysp()->cloneTree(true));
                nodep->addNext(alwaysp);
            }
            // Add Jumps
            { TimingProcedureVisitor visit(m_state /*ref*/, nodep, false); }
            { TimingProcedureVisitor visit(m_state /*ref*/, alwaysp, true); }
        }
        m_procedurep = nullptr;
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = nullptr;
    }
    virtual void visit(AstDelay* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (m_ftaskp) {
            nodep->v3error("Unsupported: Tasks with delays");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (!m_procedurep) {
            nodep->v3error("Unexpected location for delay");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        ++m_delays;
        ++m_statDelays;
        // Must assign FSM codes before we clone into initial and non-initial
        nodep->user1(m_delays);
    }

    virtual void visit(AstNodeMath*) VL_OVERRIDE {}
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TimingVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~TimingVisitor() {
        V3Stats::addStat("Timing, Delayed procedures", m_statProcedures);
        V3Stats::addStat("Timing, Delayed procedures states", m_statDelays);
    }
};

//######################################################################
// Task class functions

void V3Timing::timingAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TimingVisitor bvisitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("timing", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
