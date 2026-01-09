// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lifelicate variable assignment elimination
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
// LIFE TRANSFORMATIONS:
//      Build control-flow graph with assignments and var usages
//      All modules:
//          ASSIGN(x,...), ASSIGN(x,...) => delete first one
//          We also track across if statements:
//          ASSIGN(X,...) IF( ..., ASSIGN(X,...), ASSIGN(X,...)) => deletes first
//          We don't do the opposite yet though (remove assigns in if followed by outside if)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Life.h"

#include "V3Const.h"
#include "V3Stats.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

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
    VDouble0 m_statCResetDel;  // Statistic tracking

    // CONSTRUCTORS
    LifeState() = default;
    ~LifeState() {
        V3Stats::addStatSum("Optimizations, Lifetime assign deletions", m_statAssnDel);
        V3Stats::addStatSum("Optimizations, Lifetime creset deletions", m_statCResetDel);
        V3Stats::addStatSum("Optimizations, Lifetime constant prop", m_statAssnCon);
    }
};

//######################################################################
// Structure for each variable encountered

class LifeVarEntry final {
    // Last assignment to this varscope, nullptr if no longer relevant
    AstNodeStmt* m_assignp = nullptr;
    AstConst* m_constp = nullptr;  // Known constant value
    bool m_isNew = true;  // Is just created
    // First access was a set (and thus block above may have a set that can be deleted
    bool m_setBeforeUse = false;
    // Was ever assigned (and thus above block may not preserve constant propagation)
    bool m_everSet = false;

public:
    LifeVarEntry() = default;
    ~LifeVarEntry() = default;

    void init(bool setBeforeUse) {
        UASSERT(m_isNew, "Not a new entry");
        m_isNew = false;
        m_setBeforeUse = setBeforeUse;
    }

    void simpleAssign(AstNodeAssign* nodep) {  // New simple A=.... assignment
        UASSERT_OBJ(!m_isNew, nodep, "Uninitialized new entry");
        m_assignp = nodep;
        m_constp = nullptr;
        m_everSet = true;
        if (VN_IS(nodep->rhsp(), Const)) m_constp = VN_AS(nodep->rhsp(), Const);
    }
    void resetStatement(AstCReset* nodep) {  // New CReset(A) assignment
        UASSERT_OBJ(!m_isNew, nodep, "Uninitialized new entry");
        m_assignp = nodep;
        m_constp = nullptr;
        m_everSet = true;
    }
    void complexAssign() {  // A[x]=... or some complicated assignment
        UASSERT(!m_isNew, "Uninitialized new entry");
        m_assignp = nullptr;
        m_constp = nullptr;
        m_everSet = true;
    }
    void consumed() {  // Rvalue read of A
        UASSERT(!m_isNew, "Uninitialized new entry");
        m_assignp = nullptr;
    }
    AstNodeStmt* assignp() const { return m_assignp; }
    AstConst* constNodep() const { return m_constp; }
    bool isNew() const { return m_isNew; }
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
    // For each basic block, we'll make a new map of what variables that if/else is changing
    // Current active lifetime map for current scope
    std::unordered_map<AstVarScope*, LifeVarEntry> m_map;
    LifeBlock* const m_aboveLifep;  // Upper life, or nullptr
    LifeState* const m_statep;  // Current global state
    bool m_replacedVref = false;  // Replaced a variable reference since last clearing
    VNDeleter m_deleter;  // Used to delay deletion of nodes

public:
    LifeBlock(LifeBlock* aboveLifep, LifeState* statep)
        : m_aboveLifep{aboveLifep}  // Null if top
        , m_statep{statep} {}
    ~LifeBlock() = default;
    // METHODS
    void checkRemoveAssign(const AstVarScope* vscp, LifeVarEntry& entr) {
        const AstVar* const varp = vscp->varp();
        // We don't optimize any public sigs
        if (varp->isSigPublic()) return;
        if (varp->sensIfacep()) return;
        // Check the var entry, and remove if appropriate
        AstNodeStmt* const oldassp = entr.assignp();
        if (!oldassp) return;
        UINFO(7, "       PREV: " << oldassp);
        // Redundant assignment, in same level block
        // Don't delete it now as it will confuse iteration since it maybe WAY
        // above our current iteration point.
        UINFOTREE(7, oldassp, "", "REMOVE/SAMEBLK");
        entr.complexAssign();
        oldassp->unlinkFrBack();
        if (VN_IS(oldassp, CReset)) {
            ++m_statep->m_statCResetDel;
        } else {
            ++m_statep->m_statAssnDel;
        }
        VL_DO_DANGLING(m_deleter.pushDeletep(oldassp), oldassp);
    }
    void resetStatement(AstVarScope* nodep, AstCReset* rstp) {
        // Do we have a old assignment we can nuke?
        UINFO(4, "     CRESETof: " << nodep);
        UINFO(7, "       new: " << rstp);
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) {
            entr.init(true);
        } else {
            checkRemoveAssign(nodep, entr);
        }
        entr.resetStatement(rstp);
        // lifeDump();
    }
    void simpleAssign(AstVarScope* nodep, AstNodeAssign* assp) {
        // Do we have a old assignment we can nuke?
        UINFO(4, "     ASSIGNof: " << nodep);
        UINFO(7, "       new: " << assp);
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) {
            entr.init(true);
        } else {
            checkRemoveAssign(nodep, entr);
        }
        entr.simpleAssign(assp);
        // lifeDump();
    }
    void complexAssign(AstVarScope* nodep) {
        UINFO(4, "     clearof: " << nodep);
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) entr.init(false);
        entr.complexAssign();
    }
    void clearReplaced() { m_replacedVref = false; }
    bool replaced() const { return m_replacedVref; }
    void varUsageReplace(AstVarScope* nodep, AstVarRef* varrefp) {
        // Variable rvalue.  If it references a constant, we can replace it
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) {
            entr.init(false);
        } else {
            if (AstConst* const constp = entr.constNodep()) {
                if (!varrefp->varp()->isSigPublic() && !varrefp->varp()->sensIfacep()) {
                    // Aha, variable is constant; substitute in.
                    // We'll later constant propagate
                    UINFO(4, "     replaceconst: " << varrefp);
                    varrefp->replaceWith(constp->cloneTree(false));
                    m_replacedVref = true;
                    VL_DO_DANGLING(varrefp->deleteTree(), varrefp);
                    ++m_statep->m_statAssnCon;
                    return;  // **DONE, no longer a var reference**
                }
            }
            UINFO(4, "     usage: " << nodep);
        }
        entr.consumed();
    }
    void complexAssignFind(AstVarScope* nodep) {
        UINFO(4, "     casfind: " << nodep);
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) entr.init(false);
        entr.complexAssign();
    }
    void consumedFind(AstVarScope* nodep) {
        LifeVarEntry& entr = m_map[nodep];
        if (entr.isNew()) entr.init(false);
        entr.consumed();
    }
    void lifeToAbove() {
        // Any varrefs under a if/else branch affect statements outside and after the if/else
        UASSERT(m_aboveLifep, "Pushing life when already at the top level");
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
                UINFO(4, "DUALBRANCH " << nodep);
                const auto itab = m_map.find(nodep);
                if (itab != m_map.end()) checkRemoveAssign(nodep, itab->second);
            }
        }
        // this->lifeDump();
    }
    void clear() { m_map.clear(); }
    // DEBUG
    void lifeDump() {
        UINFO(5, "  LifeMap:");
        for (const auto& itr : m_map) {
            UINFO(5,
                  "     Ent:  " << (itr.second.setBeforeUse() ? "[F]  " : "     ") << itr.first);
            if (itr.second.assignp()) {  //
                UINFO(5, "       Ass: " << itr.second.assignp());
            }
        }
    }
};

//######################################################################
// Life state, as a visitor of each AstNode

class LifeVisitor final : public VNVisitor {
    // STATE
    LifeState* const m_statep;  // Current state
    bool m_containsTiming = false;  // Statement contains timing control
    bool m_sideEffect = false;  // Side effects discovered in assign RHS
    bool m_noopt = false;  // Disable optimization of variables in this block
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    LifeBlock* m_lifep = nullptr;  // Current active lifetime map for current scope

    // METHODS
    void setNoopt() {
        m_noopt = true;
        m_lifep->clear();
    }

    // VISITORS
    void visit(AstVarRef* nodep) override {
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
    void visit(AstNodeAssign* nodep) override {
        if (nodep->isTimingControl() || VN_IS(nodep, AssignForce)) {
            // V3Life doesn't understand time sense nor force assigns - don't optimize
            setNoopt();
            if (nodep->isTimingControl()) m_containsTiming = true;
            iterateChildren(nodep);
            return;
        }
        // Collect any used variables first, as lhs may also be on rhs
        // Similar code in V3Dead
        VL_RESTORER(m_sideEffect);
        m_sideEffect = false;
        m_lifep->clearReplaced();
        iterateAndNextNull(nodep->rhsp());
        if (m_lifep->replaced()) {
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
    void visit(AstCReset* nodep) override {
        if (!m_noopt) {
            AstVarScope* const vscp = nodep->varrefp()->varScopep();
            UASSERT_OBJ(vscp, nodep, "Scope lost on variable");
            m_lifep->resetStatement(vscp, nodep);
        } else {
            iterateAndNextNull(nodep->varrefp());
        }
    }
    void visit(AstAssignDly* nodep) override {
        // V3Life doesn't understand time sense
        if (nodep->isTimingControl()) {
            // Don't optimize
            setNoopt();
            m_containsTiming = true;
        }
        // Don't treat as normal assign
        iterateChildren(nodep);
    }

    //---- Track control flow changes
    void visit(AstNodeIf* nodep) override {
        UINFO(4, "   IF " << nodep);
        // Condition is part of PREVIOUS block
        iterateAndNextNull(nodep->condp());
        LifeBlock* const prevLifep = m_lifep;
        LifeBlock* const ifLifep = new LifeBlock{prevLifep, m_statep};
        LifeBlock* const elseLifep = new LifeBlock{prevLifep, m_statep};
        {
            m_lifep = ifLifep;
            iterateAndNextNull(nodep->thensp());
        }
        {
            m_lifep = elseLifep;
            iterateAndNextNull(nodep->elsesp());
        }
        m_lifep = prevLifep;
        UINFO(4, "   join ");
        // Find sets on both flows
        m_lifep->dualBranch(ifLifep, elseLifep);
        // For the next assignments, clear any variables that were read or written in the block
        ifLifep->lifeToAbove();
        elseLifep->lifeToAbove();
        VL_DO_DANGLING(delete ifLifep, ifLifep);
        VL_DO_DANGLING(delete elseLifep, elseLifep);
    }
    void visit(AstLoop* nodep) override {
        // Similar problem to AstJumpBlock, don't optimize loop bodies - most are unrolled
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        VL_RESTORER(m_containsTiming);
        {
            VL_RESTORER(m_noopt);
            VL_RESTORER(m_lifep);
            m_lifep = new LifeBlock{m_lifep, m_statep};
            setNoopt();
            iterateAndNextNull(nodep->stmtsp());
            UINFO(4, "   joinloop");
            // For the next assignments, clear any variables that were read or written in the block
            m_lifep->lifeToAbove();
            VL_DO_DANGLING(delete m_lifep, m_lifep);
        }
        if (m_containsTiming) setNoopt();
    }
    void visit(AstJumpBlock* nodep) override {
        // As with Loop's we can't predict if a JumpGo will kill us or not
        // It's worse though as an IF(..., JUMPGO) may change the control flow.
        // Just don't optimize blocks with labels; they're rare - so far.
        VL_RESTORER(m_containsTiming);
        {
            VL_RESTORER(m_noopt);
            VL_RESTORER(m_lifep);
            m_lifep = new LifeBlock{m_lifep, m_statep};
            setNoopt();
            iterateAndNextNull(nodep->stmtsp());
            UINFO(4, "   joinjump");
            // For the next assignments, clear any variables that were read or written in the block
            m_lifep->lifeToAbove();
            VL_DO_DANGLING(delete m_lifep, m_lifep);
        }
        if (m_containsTiming) setNoopt();
    }
    void visit(AstNodeCCall* nodep) override {
        // UINFO(4, "  CCALL " << nodep);
        iterateChildren(nodep);
        // Enter the function and trace it
        // else is non-inline or public function we optimize separately
        if (nodep->funcp()->entryPoint()) {
            setNoopt();
        } else {
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    void visit(AstCFunc* nodep) override {
        // UINFO(4, "  CFUNC " << nodep);
        if (!m_tracingCall && !nodep->entryPoint()) return;
        m_tracingCall = false;
        if (nodep->recursive()) setNoopt();
        if (nodep->dpiImportPrototype() && !nodep->dpiPure()) {
            m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        }
        iterateChildren(nodep);
    }
    void visit(AstCExprUser* nodep) override {
        m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        iterateChildren(nodep);
    }
    void visit(AstCExpr* nodep) override {
        m_sideEffect = true;  // If appears on assign RHS, don't ever delete the assignment
        iterateChildren(nodep);
    }

    void visit(AstVar*) override {}  // Don't want varrefs under it
    void visit(AstNode* nodep) override {
        if (nodep->isTimingControl()) {
            // V3Life doesn't understand time sense - don't optimize
            setNoopt();
            m_containsTiming = true;
        }
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    LifeVisitor(AstNode* nodep, LifeState* statep)
        : m_statep{statep} {
        UINFO(4, "  LifeVisitor on " << nodep);
        {
            m_lifep = new LifeBlock{nullptr, m_statep};
            iterate(nodep);
            if (m_lifep) VL_DO_CLEAR(delete m_lifep, m_lifep = nullptr);
        }
    }
    ~LifeVisitor() override {
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
    void visit(AstCFunc* nodep) override {
        if (nodep->entryPoint()) {
            // Usage model 1: Simulate all C code, doing lifetime analysis
            LifeVisitor{nodep, m_statep};
        }
    }
    void visit(AstNodeProcedure* nodep) override {
        // Usage model 2: Cleanup basic blocks
        LifeVisitor{nodep, m_statep};
    }
    void visit(AstVar*) override {}  // Accelerate
    void visit(AstNodeStmt*) override {}  // Accelerate
    void visit(AstNodeExpr*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LifeTopVisitor(AstNetlist* nodep, LifeState* statep)
        : m_statep{statep} {
        iterate(nodep);
    }
    ~LifeTopVisitor() override = default;
};

//######################################################################
// Life class functions

void V3Life::lifeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        LifeState state;
        LifeTopVisitor{nodep, &state};
    }  // Destruct before checking
    VIsCached::clearCacheTree();  // Removing assignments may affect isPure
    V3Global::dumpCheckGlobalTree("life", 0, dumpTreeEitherLevel() >= 3);
}
