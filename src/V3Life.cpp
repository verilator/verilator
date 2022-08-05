// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lifelicate variable assignment elimination
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
// LIFE TRANSFORMATIONS:
//      Build control-flow graph with assignments and var usages
//      All modules:
//          ASSIGN(x,...), ASSIGN(x,...) => delete first one
//          We also track across if statements:
//          ASSIGN(X,...) IF( ..., ASSIGN(X,...), ASSIGN(X,...)) => deletes first
//          We don't do the opposite yet though (remove assigns in if followed by outside if)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Life.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <map>
#include <vector>

//######################################################################
// Structure for global state

class LifeState final {
    // NODE STATE
    //   See below
    const VNUser1InUse m_inuser1;

    // STATE
public:
    VDouble0 m_statAssnDel;  // Statistic tracking
    VDouble0 m_statAssnCon;  // Statistic tracking
    std::vector<AstNode*> m_unlinkps;

    // CONSTRUCTORS
    LifeState() = default;
    ~LifeState() {
        V3Stats::addStatSum("Optimizations, Lifetime assign deletions", m_statAssnDel);
        V3Stats::addStatSum("Optimizations, Lifetime constant prop", m_statAssnCon);
        for (AstNode* ip : m_unlinkps) {
            ip->unlinkFrBack();
            ip->deleteTree();
        }
    }
    // METHODS
    void pushUnlinkDeletep(AstNode* nodep) { m_unlinkps.push_back(nodep); }
};

//######################################################################
// Structure for each variable encountered

class LifeVarEntry final {
    // Last assignment to this varscope, nullptr if no longer relevant
    AstNodeAssign* m_assignp = nullptr;
    AstConst* m_constp = nullptr;  // Known constant value
    // First access was a set (and thus block above may have a set that can be deleted
    bool m_setBeforeUse;
    // Was ever assigned (and thus above block may not preserve constant propagation)
    bool m_everSet = false;

public:
    class SIMPLEASSIGN {};
    class COMPLEXASSIGN {};
    class CONSUMED {};

    LifeVarEntry(SIMPLEASSIGN, AstNodeAssign* assp)
        : m_setBeforeUse{true} {
        simpleAssign(assp);
    }
    explicit LifeVarEntry(COMPLEXASSIGN)
        : m_setBeforeUse{false} {
        complexAssign();
    }
    explicit LifeVarEntry(CONSUMED)
        : m_setBeforeUse{false} {
        consumed();
    }
    ~LifeVarEntry() = default;
    inline void simpleAssign(AstNodeAssign* assp) {  // New simple A=.... assignment
        m_assignp = assp;
        m_constp = nullptr;
        m_everSet = true;
        if (VN_IS(assp->rhsp(), Const)) m_constp = VN_AS(assp->rhsp(), Const);
    }
    inline void complexAssign() {  // A[x]=... or some complicated assignment
        m_assignp = nullptr;
        m_constp = nullptr;
        m_everSet = true;
    }
    inline void consumed() {  // Rvalue read of A
        m_assignp = nullptr;
    }
    AstNodeAssign* assignp() const { return m_assignp; }
    AstConst* constNodep() const { return m_constp; }
    bool setBeforeUse() const { return m_setBeforeUse; }
    bool everSet() const { return m_everSet; }
};

//######################################################################
// Structure for all variables under a given meta-basic block

class LifeBlock final {
    // NODE STATE
    // Cleared each AstIf:
    //   AstVarScope::user1()   -> int.       Used in combining to detect duplicates

    // LIFE MAP
    //  For each basic block, we'll make a new map of what variables that if/else is changing
    using LifeMap = std::unordered_map<AstVarScope*, LifeVarEntry>;
    LifeMap m_map;  // Current active lifetime map for current scope
    LifeBlock* const m_aboveLifep;  // Upper life, or nullptr
    LifeState* const m_statep;  // Current global state

    VL_DEBUG_FUNC;  // Declare debug()

public:
    LifeBlock(LifeBlock* aboveLifep, LifeState* statep)
        : m_aboveLifep{aboveLifep}  // Null if top
        , m_statep{statep} {}
    ~LifeBlock() = default;
    // METHODS
    void checkRemoveAssign(const LifeMap::iterator& it) {
        const AstVar* const varp = it->first->varp();
        LifeVarEntry* const entp = &(it->second);
        if (!varp->isSigPublic()) {
            // Rather than track what sigs AstUCFunc/AstUCStmt may change,
            // we just don't optimize any public sigs
            // Check the var entry, and remove if appropriate
            if (AstNode* const oldassp = entp->assignp()) {
                UINFO(7, "       PREV: " << oldassp << endl);
                // Redundant assignment, in same level block
                // Don't delete it now as it will confuse iteration since it maybe WAY
                // above our current iteration point.
                if (debug() > 4) oldassp->dumpTree(cout, "       REMOVE/SAMEBLK ");
                entp->complexAssign();
                VL_DO_DANGLING(m_statep->pushUnlinkDeletep(oldassp), oldassp);
                ++m_statep->m_statAssnDel;
            }
        }
    }
    void simpleAssign(AstVarScope* nodep, AstNodeAssign* assp) {
        // Do we have a old assignment we can nuke?
        UINFO(4, "     ASSIGNof: " << nodep << endl);
        UINFO(7, "       new: " << assp << endl);
        const auto it = m_map.find(nodep);
        if (it != m_map.end()) {
            checkRemoveAssign(it);
            it->second.simpleAssign(assp);
        } else {
            m_map.emplace(nodep, LifeVarEntry(LifeVarEntry::SIMPLEASSIGN(), assp));
        }
        // lifeDump();
    }
    void complexAssign(AstVarScope* nodep) {
        UINFO(4, "     clearof: " << nodep << endl);
        const auto it = m_map.find(nodep);
        if (it != m_map.end()) {
            it->second.complexAssign();
        } else {
            m_map.emplace(nodep, LifeVarEntry(LifeVarEntry::COMPLEXASSIGN()));
        }
    }
    void varUsageReplace(AstVarScope* nodep, AstVarRef* varrefp) {
        // Variable rvalue.  If it references a constant, we can replace it
        const auto it = m_map.find(nodep);
        if (it != m_map.end()) {
            if (AstConst* const constp = it->second.constNodep()) {
                if (!varrefp->varp()->isSigPublic()) {
                    // Aha, variable is constant; substitute in.
                    // We'll later constant propagate
                    UINFO(4, "     replaceconst: " << varrefp << endl);
                    varrefp->replaceWith(constp->cloneTree(false));
                    VL_DO_DANGLING(varrefp->deleteTree(), varrefp);
                    ++m_statep->m_statAssnCon;
                    return;  // **DONE, no longer a var reference**
                }
            }
            UINFO(4, "     usage: " << nodep << endl);
            it->second.consumed();
        } else {
            m_map.emplace(nodep, LifeVarEntry(LifeVarEntry::CONSUMED()));
        }
    }
    void complexAssignFind(AstVarScope* nodep) {
        const auto it = m_map.find(nodep);
        if (it != m_map.end()) {
            UINFO(4, "     casfind: " << it->first << endl);
            it->second.complexAssign();
        } else {
            m_map.emplace(nodep, LifeVarEntry(LifeVarEntry::COMPLEXASSIGN()));
        }
    }
    void consumedFind(AstVarScope* nodep) {
        const auto it = m_map.find(nodep);
        if (it != m_map.end()) {
            it->second.consumed();
        } else {
            m_map.emplace(nodep, LifeVarEntry(LifeVarEntry::CONSUMED()));
        }
    }
    void lifeToAbove() {
        // Any varrefs under a if/else branch affect statements outside and after the if/else
        if (!m_aboveLifep) v3fatalSrc("Pushing life when already at the top level");
        for (auto& itr : m_map) {
            AstVarScope* const nodep = itr.first;
            m_aboveLifep->complexAssignFind(nodep);
            if (itr.second.everSet()) {
                // Record there may be an assignment, so we don't constant propagate across the if.
                complexAssignFind(nodep);
            } else {
                // Record consumption, so we don't eliminate earlier assignments
                consumedFind(nodep);
            }
        }
    }
    void dualBranch(LifeBlock* life1p, LifeBlock* life2p) {
        // Find any common sets on both branches of IF and propagate upwards
        // life1p->lifeDump();
        // life2p->lifeDump();
        AstNode::user1ClearTree();  // user1p() used on entire tree
        for (auto& itr : life1p->m_map) {
            // When the if branch sets a var before it's used, mark that variable
            if (itr.second.setBeforeUse()) itr.first->user1(1);
        }
        for (auto& itr : life2p->m_map) {
            // When the else branch sets a var before it's used
            AstVarScope* const nodep = itr.first;
            if (itr.second.setBeforeUse() && nodep->user1()) {
                // Both branches set the var, we can remove the assignment before the IF.
                UINFO(4, "DUALBRANCH " << nodep << endl);
                const auto itab = m_map.find(nodep);
                if (itab != m_map.end()) checkRemoveAssign(itab);
            }
        }
        // this->lifeDump();
    }
    void clear() { m_map.clear(); }
    // DEBUG
    void lifeDump() {
        UINFO(5, "  LifeMap:" << endl);
        for (const auto& itr : m_map) {
            UINFO(5, "     Ent:  " << (itr.second.setBeforeUse() ? "[F]  " : "     ") << itr.first
                                   << endl);
            if (itr.second.assignp()) {  //
                UINFO(5, "       Ass: " << itr.second.assignp() << endl);
            }
        }
    }
};

//######################################################################
// Life state, as a visitor of each AstNode

class LifeVisitor final : public VNVisitor {
private:
    // STATE
    LifeState* const m_statep;  // Current state
    bool m_sideEffect = false;  // Side effects discovered in assign RHS
    bool m_noopt = false;  // Disable optimization of variables in this block
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc

    // LIFE MAP
    //  For each basic block, we'll make a new map of what variables that if/else is changing
    using LifeMap = std::unordered_map<AstVarScope*, LifeVarEntry>;
    // cppcheck-suppress memleak  // cppcheck bug - it is deleted
    LifeBlock* m_lifep;  // Current active lifetime map for current scope

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
    void setNoopt() {
        m_noopt = true;
        m_lifep->clear();
    }

    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        // Consumption/generation of a variable,
        // it's used so can't elim assignment before this use.
        UASSERT_OBJ(nodep->varScopep(), nodep, "nullptr");
        //
        AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (nodep->access().isWriteOrRW()) {
            m_sideEffect = true;  // $sscanf etc may have RHS vars that are lvalues
            m_lifep->complexAssign(vscp);
        } else {
            VL_DO_DANGLING(m_lifep->varUsageReplace(vscp, nodep), nodep);
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        // Collect any used variables first, as lhs may also be on rhs
        // Similar code in V3Dead
        const uint64_t lastEdit = AstNode::editCountGbl();  // When it was last edited
        m_sideEffect = false;
        iterateAndNextNull(nodep->rhsp());
        if (lastEdit != AstNode::editCountGbl()) {
            // We changed something, try to constant propagate, but don't delete the
            // assignment as we still need nodep to remain.
            V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        }
        // Has to be direct assignment without any EXTRACTing.
        if (VN_IS(nodep->lhsp(), VarRef) && !m_sideEffect && !m_noopt) {
            AstVarScope* const vscp = VN_AS(nodep->lhsp(), VarRef)->varScopep();
            UASSERT_OBJ(vscp, nodep, "Scope lost on variable");
            m_lifep->simpleAssign(vscp, nodep);
        } else {
            iterateAndNextNull(nodep->lhsp());
        }
    }
    virtual void visit(AstAssignDly* nodep) override {
        // Don't treat as normal assign; V3Life doesn't understand time sense
        iterateChildren(nodep);
    }

    //---- Track control flow changes
    virtual void visit(AstNodeIf* nodep) override {
        UINFO(4, "   IF " << nodep << endl);
        // Condition is part of PREVIOUS block
        iterateAndNextNull(nodep->condp());
        LifeBlock* const prevLifep = m_lifep;
        LifeBlock* const ifLifep = new LifeBlock(prevLifep, m_statep);
        LifeBlock* const elseLifep = new LifeBlock(prevLifep, m_statep);
        {
            m_lifep = ifLifep;
            iterateAndNextNull(nodep->ifsp());
        }
        {
            m_lifep = elseLifep;
            iterateAndNextNull(nodep->elsesp());
        }
        m_lifep = prevLifep;
        UINFO(4, "   join " << endl);
        // Find sets on both flows
        m_lifep->dualBranch(ifLifep, elseLifep);
        // For the next assignments, clear any variables that were read or written in the block
        ifLifep->lifeToAbove();
        elseLifep->lifeToAbove();
        VL_DO_DANGLING(delete ifLifep, ifLifep);
        VL_DO_DANGLING(delete elseLifep, elseLifep);
    }

    virtual void visit(AstWhile* nodep) override {
        // While's are a problem, as we don't allow loops in the graph.  We
        // may go around the cond/body multiple times.  Thus a
        // lifelication just in the body is ok, but we can't delete an
        // assignment in the body that's used in the cond.  (And otherwise
        // would because it only appears used after-the-fact.  So, we model
        // it as a IF statement, and just don't allow elimination of
        // variables across the body.
        LifeBlock* const prevLifep = m_lifep;
        LifeBlock* const condLifep = new LifeBlock(prevLifep, m_statep);
        LifeBlock* const bodyLifep = new LifeBlock(prevLifep, m_statep);
        {
            m_lifep = condLifep;
            iterateAndNextNull(nodep->precondsp());
            iterateAndNextNull(nodep->condp());
        }
        {
            m_lifep = bodyLifep;
            iterateAndNextNull(nodep->bodysp());
            iterateAndNextNull(nodep->incsp());
        }
        m_lifep = prevLifep;
        UINFO(4, "   joinfor" << endl);
        // For the next assignments, clear any variables that were read or written in the block
        condLifep->lifeToAbove();
        bodyLifep->lifeToAbove();
        VL_DO_DANGLING(delete condLifep, condLifep);
        VL_DO_DANGLING(delete bodyLifep, bodyLifep);
    }
    virtual void visit(AstJumpBlock* nodep) override {
        // As with While's we can't predict if a JumpGo will kill us or not
        // It's worse though as an IF(..., JUMPGO) may change the control flow.
        // Just don't optimize blocks with labels; they're rare - so far.
        LifeBlock* const prevLifep = m_lifep;
        LifeBlock* const bodyLifep = new LifeBlock(prevLifep, m_statep);
        {
            VL_RESTORER(m_noopt);
            m_lifep = bodyLifep;
            setNoopt();
            iterateAndNextNull(nodep->stmtsp());
            m_lifep = prevLifep;
        }
        UINFO(4, "   joinjump" << endl);
        // For the next assignments, clear any variables that were read or written in the block
        bodyLifep->lifeToAbove();
        VL_DO_DANGLING(delete bodyLifep, bodyLifep);
    }
    virtual void visit(AstNodeCCall* nodep) override {
        // UINFO(4, "  CCALL " << nodep << endl);
        iterateChildren(nodep);
        // Enter the function and trace it
        // else is non-inline or public function we optimize separately
        if (!nodep->funcp()->entryPoint()) {
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        // UINFO(4, "  CFUNC " << nodep << endl);
        if (!m_tracingCall && !nodep->entryPoint()) return;
        m_tracingCall = false;
        if (nodep->dpiImportPrototype() && !nodep->pure()) {
            m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstUCFunc* nodep) override {
        m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        iterateChildren(nodep);
    }
    virtual void visit(AstCMath* nodep) override {
        m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        iterateChildren(nodep);
    }

    virtual void visit(AstVar*) override {}  // Don't want varrefs under it
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LifeVisitor(AstNode* nodep, LifeState* statep)
        : m_statep{statep} {
        UINFO(4, "  LifeVisitor on " << nodep << endl);
        {
            m_lifep = new LifeBlock(nullptr, m_statep);
            iterate(nodep);
            if (m_lifep) VL_DO_CLEAR(delete m_lifep, m_lifep = nullptr);
        }
    }
    virtual ~LifeVisitor() override {
        if (m_lifep) VL_DO_CLEAR(delete m_lifep, m_lifep = nullptr);
    }
    VL_UNCOPYABLE(LifeVisitor);
};

//######################################################################

class LifeTopVisitor final : public VNVisitor {
    // Visit all top nodes searching for functions that are entry points we want to start
    // finding code within.
private:
    // STATE
    LifeState* const m_statep;  // Current state

    // VISITORS
    virtual void visit(AstCFunc* nodep) override {
        if (nodep->entryPoint()) {
            // Usage model 1: Simulate all C code, doing lifetime analysis
            LifeVisitor{nodep, m_statep};
        }
    }
    virtual void visit(AstNodeProcedure* nodep) override {
        // Usage model 2: Cleanup basic blocks
        LifeVisitor{nodep, m_statep};
    }
    virtual void visit(AstVar*) override {}  // Accelerate
    virtual void visit(AstNodeStmt*) override {}  // Accelerate
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LifeTopVisitor(AstNetlist* nodep, LifeState* statep)
        : m_statep{statep} {
        iterate(nodep);
    }
    virtual ~LifeTopVisitor() override = default;
};

//######################################################################
// Life class functions

void V3Life::lifeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        LifeState state;
        LifeTopVisitor{nodep, &state};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("life", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
