// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Create a IACTIVE(initial), SACTIVE(combo)
//      ALWAYS: Remove any-edges from sense list
//          If no POS/NEG in senselist, Fold into SACTIVE(combo)
//          Else fold into SACTIVE(sequent).
//          OPTIMIZE: When support async clocks, fold into that active if possible
//      INITIAL: Move into IACTIVE
//      WIRE: Move into SACTIVE(combo)
//
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Active.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Graph.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//***** See below for main transformation engine

//######################################################################

// Extend V3GraphVertex class for use in latch detection graph

class LatchDetectGraphVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(LatchDetectGraphVertex, V3GraphVertex)
public:
    enum VertexType : uint8_t { VT_BLOCK, VT_BRANCH, VT_OUTPUT };

private:
    const string m_name;  // Only used for .dot file generation
    const VertexType m_type;  // Vertex type (BLOCK/BRANCH/OUTPUT)

    string typestr() const VL_MT_SAFE {  //   "
        switch (m_type) {
        case VT_BLOCK: return "(||)";  // basic block node
        case VT_BRANCH: return "(&&)";  // if/else branch mode
        case VT_OUTPUT: return "(out)";  // var assignment
        default: return "??";  // unknown
        }
    }

public:
    LatchDetectGraphVertex(V3Graph* graphp, const string& name, VertexType type = VT_BLOCK)
        : V3GraphVertex{graphp}
        , m_name{name}
        , m_type{type} {}
    string name() const override VL_MT_STABLE { return m_name + " " + typestr(); }
    string dotColor() const override { return user() ? "green" : "black"; }
    virtual int type() const { return m_type; }
};

//######################################################################
// Extend V3Graph class for use as a latch detection graph

class LatchDetectGraph final : public V3Graph {
protected:
    LatchDetectGraphVertex* m_curVertexp = nullptr;  // Current latch detection graph vertex
    std::vector<AstVarRef*> m_outputs;  // Vector of lvalues encountered on this pass

    static LatchDetectGraphVertex* castVertexp(void* vertexp) {
        return reinterpret_cast<LatchDetectGraphVertex*>(vertexp);
    }

    // Recursively traverse the graph to determine whether every control 'BLOCK' has an assignment
    // to the output we are currently analyzing (the output whose 'user() is set), if so return
    // true. Where a BLOCK contains a BRANCH, both the if and else sides of the branch must return
    // true for the BRANCH to evaluate to true. A BLOCK however needs only a single one of its
    // siblings to evaluate true in order to evaluate true itself. On output vertex only evaluates
    // true if it is the vertex we are analyzing on this check

    bool latchCheckInternal(LatchDetectGraphVertex* vertexp) {
        bool result = false;
        switch (vertexp->type()) {
        case LatchDetectGraphVertex::VT_OUTPUT:  // Base case
            result = vertexp->user();
            break;
        case LatchDetectGraphVertex::VT_BLOCK:  // (OR of potentially many siblings)
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                if (latchCheckInternal(castVertexp(edgep->top()))) {
                    result = true;
                    break;
                }
            }
            break;
        case LatchDetectGraphVertex::VT_BRANCH:  // (AND of both sibling)
                                                 // A BRANCH vertex always has exactly 2 siblings
            LatchDetectGraphVertex* const ifp = castVertexp(vertexp->outBeginp()->top());
            LatchDetectGraphVertex* const elsp
                = castVertexp(vertexp->outBeginp()->outNextp()->top());
            result = latchCheckInternal(ifp) && latchCheckInternal(elsp);
            break;
        }
        vertexp->user(result);
        return result;
    }

public:
    LatchDetectGraph() { clear(); }
    ~LatchDetectGraph() override { clear(); }
    // ACCESSORS
    LatchDetectGraphVertex* currentp() { return m_curVertexp; }
    void currentp(LatchDetectGraphVertex* vertex) { m_curVertexp = vertex; }
    // METHODS
    void begin() {
        // Start a new if/else tracking graph
        // See NODE STATE comment in ActiveLatchCheckVisitor
        AstNode::user1ClearTree();
        m_curVertexp = new LatchDetectGraphVertex{this, "ROOT"};
    }
    // Clear out userp field of referenced outputs on destruction
    // (occurs at the end of each combinational always block)
    void clear() {
        m_outputs.clear();
        // Calling base class clear will unlink & delete all edges & vertices
        V3Graph::clear();
        m_curVertexp = nullptr;
    }
    // Add a new control path and connect it to its parent
    LatchDetectGraphVertex* addPathVertex(LatchDetectGraphVertex* parent, const string& name,
                                          bool branch = false) {
        m_curVertexp = new LatchDetectGraphVertex{this, name,
                                                  branch ? LatchDetectGraphVertex::VT_BRANCH
                                                         : LatchDetectGraphVertex::VT_BLOCK};
        new V3GraphEdge{this, parent, m_curVertexp, 1};
        return m_curVertexp;
    }
    // Add a new output variable vertex and store a pointer to it in the user1 field of the
    // variables AstNode
    LatchDetectGraphVertex* addOutputVertex(AstVarRef* nodep) {
        LatchDetectGraphVertex* const outVertexp
            = new LatchDetectGraphVertex{this, nodep->name(), LatchDetectGraphVertex::VT_OUTPUT};
        nodep->varp()->user1p(outVertexp);
        m_outputs.push_back(nodep);
        return outVertexp;
    }
    // Connect an output assignment to its parent control block
    void addAssignment(AstVarRef* nodep) {
        LatchDetectGraphVertex* outVertexp;
        if (!nodep->varp()->user1p()) {  // Not seen this output before
            outVertexp = addOutputVertex(nodep);
        } else {
            outVertexp = castVertexp(nodep->varp()->user1p());
        }
        new V3GraphEdge{this, m_curVertexp, outVertexp, 1};
    }
    // Run latchCheckInternal on each variable assigned by the always block to see if all control
    // paths make an assignment. Detected latches are flagged in the variables AstVar
    void latchCheck(AstNode* nodep, bool latch_expected) {
        bool latch_detected = false;
        for (const auto& vrp : m_outputs) {
            LatchDetectGraphVertex* const vertp = castVertexp(vrp->varp()->user1p());
            vertp->user(true);  // Identify the output vertex we are checking paths _to_
            if (!latchCheckInternal(castVertexp(verticesBeginp()))) latch_detected = true;
            if (latch_detected && !latch_expected) {
                nodep->v3warn(
                    LATCH,
                    "Latch inferred for signal "
                        << vrp->prettyNameQ()
                        << " (not all control paths of combinational always assign a value)\n"
                        << nodep->warnMore()
                        << "... Suggest use of always_latch for intentional latches");
                if (dumpGraphLevel() >= 9) dumpDotFilePrefixed("latch_" + vrp->name());
            }
            vertp->user(false);  // Clear again (see above)
            vrp->varp()->isLatched(latch_detected);
        }
        // Should _all_ variables assigned in always_latch be latches? Probably, but this only
        // warns if none of them are
        if (latch_expected && !latch_detected)
            nodep->v3warn(NOLATCH, "No latches detected in always_latch block");
    }
};

//######################################################################
// Collect existing active names

class ActiveNamer final : public VNVisitor {
private:
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope to add statement to
    AstActive* m_sActivep = nullptr;  // For current scope, the Static active we're building
    AstActive* m_iActivep = nullptr;  // For current scope, the Initial active we're building
    AstActive* m_fActivep = nullptr;  // For current scope, the Final active we're building
    AstActive* m_cActivep = nullptr;  // For current scope, the Combo active we're building

    // Map from AstSenTree (equivalence) to the corresponding AstActive created.
    std::unordered_map<VNRef<AstSenTree>, AstActive*> m_activeMap;

    // METHODS
    void addActive(AstActive* nodep) {
        UASSERT_OBJ(m_scopep, nodep, "nullptr scope");
        m_scopep->addBlocksp(nodep);
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        m_scopep = nodep;
        m_sActivep = nullptr;
        m_iActivep = nullptr;
        m_fActivep = nullptr;
        m_cActivep = nullptr;
        m_activeMap.clear();
        iterateChildren(nodep);
        // Don't clear scopep, the namer persists beyond this visit
    }
    void visit(AstSenTree* nodep) override {
        // Simplify sensitivity list
        VL_DO_DANGLING(V3Const::constifyExpensiveEdit(nodep), nodep);
    }
    //--------------------
    void visit(AstNodeStmt*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // Specialized below for the special sensitivity classes
    template <typename SenItemKind>
    AstActive*& getSpecialActive();

public:
    // METHODS
    AstScope* scopep() { return m_scopep; }

    // Make a new AstActive sensitive to the given sentree and return it
    AstActive* makeActive(FileLine* const fl, AstSenTree* const senTreep) {
        auto* const activep = new AstActive{fl, "", senTreep};
        activep->sensesStorep(activep->sensesp());
        addActive(activep);
        return activep;
    }

    // Make a new AstActive sensitive to the given special sensitivity class and return it
    template <typename SenItemKind>
    AstActive* makeSpecialActive(FileLine* const fl) {
        AstSenTree* const senTreep = new AstSenTree{fl, new AstSenItem{fl, SenItemKind{}}};
        return makeActive(fl, senTreep);
    }

    // Return an AstActive sensitive to the given special sensitivity class (possibly pre-created)
    template <typename SenItemKind>
    AstActive* getSpecialActive(FileLine* fl) {
        AstActive*& cachep = getSpecialActive<SenItemKind>();
        if (!cachep) cachep = makeSpecialActive<SenItemKind>(fl);
        return cachep;
    }

    // Return an AstActive that is sensitive to a SenTree equivalent to the given sentreep.
    AstActive* getActive(FileLine* fl, AstSenTree* sensesp) {
        UASSERT(sensesp, "Must be non-null");

        auto it = m_activeMap.find(*sensesp);
        // If found matching AstActive, return it
        if (it != m_activeMap.end()) return it->second;

        // No such AstActive yet, creat it, and add to map.
        AstSenTree* const newsenp = sensesp->cloneTree(false);
        AstActive* const activep = new AstActive{fl, "sequent", newsenp};
        activep->sensesStorep(activep->sensesp());
        addActive(activep);
        m_activeMap.emplace(*newsenp, activep);
        return activep;
    }

    // CONSTRUCTORS
    ActiveNamer() = default;
    ~ActiveNamer() override = default;
    void main(AstScope* nodep) { iterate(nodep); }
};

template <>
AstActive*& ActiveNamer::getSpecialActive<AstSenItem::Static>() {
    return m_sActivep;
}
template <>
AstActive*& ActiveNamer::getSpecialActive<AstSenItem::Initial>() {
    return m_iActivep;
}
template <>
AstActive*& ActiveNamer::getSpecialActive<AstSenItem::Final>() {
    return m_fActivep;
}
template <>
AstActive*& ActiveNamer::getSpecialActive<AstSenItem::Combo>() {
    return m_cActivep;
}

//######################################################################
// Latch checking visitor

class ActiveLatchCheckVisitor final : public VNVisitorConst {
private:
    // NODE STATE
    // Input:
    //  AstVar::user1p // V2LatchGraphVertex* The vertex handling this node
    const VNUser1InUse m_inuser1;
    // STATE
    LatchDetectGraph m_graph;  // Graph used to detect latches in combo always
    // VISITORS
    void visit(AstVarRef* nodep) override {
        const AstVar* const varp = nodep->varp();
        if (nodep->access().isWriteOrRW() && varp->isSignal() && !varp->isUsedLoopIdx()
            && !varp->isFuncLocalSticky()) {
            m_graph.addAssignment(nodep);
        }
    }
    void visit(AstNodeIf* nodep) override {
        if (!nodep->isBoundsCheck()) {
            LatchDetectGraphVertex* const parentp = m_graph.currentp();
            LatchDetectGraphVertex* const branchp = m_graph.addPathVertex(parentp, "BRANCH", true);
            m_graph.addPathVertex(branchp, "IF");
            iterateAndNextConstNull(nodep->thensp());
            m_graph.addPathVertex(branchp, "ELSE");
            iterateAndNextConstNull(nodep->elsesp());
            m_graph.currentp(parentp);
        } else {
            iterateChildrenConst(nodep);
        }
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    ActiveLatchCheckVisitor(AstNode* nodep, bool expectLatch) {
        m_graph.begin();
        iterateConst(nodep);
        m_graph.latchCheck(nodep, expectLatch);
    }
    ~ActiveLatchCheckVisitor() override = default;
};

//######################################################################
// Replace unsupported non-blocking assignments with blocking assignments

class ActiveDlyVisitor final : public VNVisitor {
public:
    enum CheckType : uint8_t { CT_SEQ, CT_COMB, CT_INITIAL };

private:
    // MEMBERS
    const CheckType m_check;  // Process type we are checking

    // VISITORS
    void visit(AstAssignDly* nodep) override {
        // Non-blocking assignments are OK in sequential processes
        if (m_check == CT_SEQ) return;

        // Issue appropriate warning
        if (m_check == CT_INITIAL) {
            nodep->v3warn(INITIALDLY,
                          "Non-blocking assignment '<=' in initial/final block\n"
                              << nodep->warnMore()
                              << "... This will be executed as a blocking assignment '='!");
        } else {
            nodep->v3warn(COMBDLY,
                          "Non-blocking assignment '<=' in combinational logic process\n"
                              << nodep->warnMore()
                              << "... This will be executed as a blocking assignment '='!");
        }

        // Convert to blocking assignment
        nodep->replaceWith(new AstAssign{
            nodep->fileline(),  //
            nodep->lhsp()->unlinkFrBack(),  //
            nodep->rhsp()->unlinkFrBack(),  //
            nodep->timingControlp() ? nodep->timingControlp()->unlinkFrBack() : nullptr});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void visit(AstAssign* nodep) override {
        // Blocking assignments are always OK in combinational (and initial/final) processes
        if (m_check != CT_SEQ) return;

        const bool ignore = nodep->lhsp()->forall([&](const AstVarRef* refp) {
            // Ignore reads (e.g.: index expressions)
            if (refp->access().isReadOnly()) return true;
            const AstVar* const varp = refp->varp();
            // Ignore ...
            return varp->isUsedLoopIdx()  // ... loop indices
                   || varp->isTemp()  // ... temporaries
                   || varp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ);  // ... user said so
        });

        if (ignore) return;

        nodep->v3warn(BLKSEQ,
                      "Blocking assignment '=' in sequential logic process\n"
                          << nodep->warnMore()  //
                          << "... Suggest using delayed assignment '<='");
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    ActiveDlyVisitor(AstNode* nodep, CheckType check)
        : m_check{check} {
        iterate(nodep);
    }
    ~ActiveDlyVisitor() override = default;
};

//######################################################################
// Active class functions

class ActiveVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  Each call to V3Const::constify
    //   AstVarScope::user1()           bool: This VarScope is referenced in the sensitivity list
    //   AstVarScope::user2()           bool: This VarScope is written in the current process
    //   AstNode::user4()               Used by V3Const::constify, called below

    // STATE
    ActiveNamer m_namer;  // Tracking of active names
    bool m_clockedProcess = false;  // Whether current process is a clocked process
    bool m_allChanged = false;  // Whether all SenItem in the SenTree are ET_CHANGED
    bool m_walkingBody = false;  // Walking body of a process
    bool m_canBeComb = false;  // Whether current clocked process can be turned into a comb process

    // METHODS
    template <typename T>
    void moveUnderSpecial(AstNode* nodep) {
        AstActive* const wantactivep = m_namer.getSpecialActive<T>(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }

    void visitAlways(AstNode* nodep, AstSenTree* oldsensesp, VAlwaysKwd kwd) {
        // Move always to appropriate ACTIVE based on its sense list
        if (oldsensesp && oldsensesp->sensesp() && oldsensesp->sensesp()->isNever()) {
            // Never executing.  Kill it.
            UASSERT_OBJ(!oldsensesp->sensesp()->nextp(), nodep,
                        "Never senitem should be alone, else the never should be eliminated.");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }

        {
            const VNUser1InUse user1InUse;

            // Walk sensitivity list
            m_clockedProcess = false;
            m_allChanged = true;
            if (oldsensesp) {
                oldsensesp->unlinkFrBack();
                iterateChildrenConst(oldsensesp);
            }

            // If all SenItems are ET_CHANGE, then walk the body to determine if this process
            // could be turned into a combinational process instead.
            if (m_allChanged) {
                const VNUser2InUse user2InUse;
                m_walkingBody = true;
                m_canBeComb = true;
                iterateChildrenConst(nodep);
                m_walkingBody = false;
                if (m_canBeComb) m_clockedProcess = false;
            }
        }

        AstActive* const wantactivep
            = !m_clockedProcess ? m_namer.getSpecialActive<AstSenItem::Combo>(nodep->fileline())
              : oldsensesp      ? m_namer.getActive(nodep->fileline(), oldsensesp)
                                : m_namer.getSpecialActive<AstSenItem::Initial>(nodep->fileline());

        // Delete sensitivity list
        if (oldsensesp) VL_DO_DANGLING(oldsensesp->deleteTree(), oldsensesp);

        // Move node to new active
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);

        // Warn and convert any delayed assignments
        {
            ActiveDlyVisitor{nodep, m_clockedProcess ? ActiveDlyVisitor::CT_SEQ
                                                     : ActiveDlyVisitor::CT_COMB};
        }

        // check combinational processes for latches
        if (!m_clockedProcess || kwd == VAlwaysKwd::ALWAYS_LATCH) {
            const ActiveLatchCheckVisitor latchvisitor{nodep, kwd == VAlwaysKwd::ALWAYS_LATCH};
        }
    }

    void visitSenItems(AstNode* nodep) {
        if (v3Global.opt.timing().isSetTrue()) {
            nodep->foreach([this](AstSenItem* senItemp) { visit(senItemp); });
        }
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        m_namer.main(nodep);  // Clear last scope's names, and collect this scope's existing names
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
        // Actives are being formed, so we can ignore any already made
    }

    void visit(AstInitialStatic* nodep) override { moveUnderSpecial<AstSenItem::Static>(nodep); }
    void visit(AstInitial* nodep) override {
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_INITIAL};
        visitSenItems(nodep);
        moveUnderSpecial<AstSenItem::Initial>(nodep);
    }
    void visit(AstFinal* nodep) override {
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_INITIAL};
        moveUnderSpecial<AstSenItem::Final>(nodep);
    }
    void visit(AstAssignAlias* nodep) override { moveUnderSpecial<AstSenItem::Combo>(nodep); }
    void visit(AstCoverToggle* nodep) override { moveUnderSpecial<AstSenItem::Combo>(nodep); }
    void visit(AstAssignW* nodep) override { moveUnderSpecial<AstSenItem::Combo>(nodep); }
    void visit(AstAlways* nodep) override {
        if (!nodep->stmtsp()) {  // Empty always. Remove it now.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        visitSenItems(nodep);
        visitAlways(nodep, nodep->sensesp(), nodep->keyword());
    }
    void visit(AstAlwaysPostponed* nodep) override {
        // Might be empty with later optimizations, so this assertion can be removed,
        // but for now it is guaranteed to be not empty.
        UASSERT_OBJ(nodep->stmtsp(), nodep, "Should not be empty");
        // Make a new active for it, needs to be the only item under the active for V3Sched
        AstActive* const activep = m_namer.makeSpecialActive<AstSenItem::Combo>(nodep->fileline());
        activep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstAlwaysObserved* nodep) override {
        UASSERT_OBJ(nodep->sensesp(), nodep, "Should have a sentree");
        AstSenTree* const sensesp = nodep->sensesp();
        sensesp->unlinkFrBack();
        // Make a new active for it, needs to be the only item under the active for V3Sched
        AstActive* const activep = m_namer.makeActive(nodep->fileline(), sensesp);
        activep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstAlwaysReactive* nodep) override {
        UASSERT_OBJ(nodep->sensesp(), nodep, "Should have a sentree");
        AstSenTree* const sensesp = nodep->sensesp();
        sensesp->unlinkFrBack();
        // Make a new active for it, needs to be the only item under the active for V3Sched
        AstActive* const activep = m_namer.makeActive(nodep->fileline(), sensesp);
        activep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstAlwaysPublic* nodep) override {
        visitAlways(nodep, nodep->sensesp(), VAlwaysKwd::ALWAYS);
    }
    void visit(AstCFunc* nodep) override { visitSenItems(nodep); }
    void visit(AstSenItem* nodep) override {
        UASSERT_OBJ(!m_walkingBody, nodep,
                    "Should not reach here when walking body without --timing");
        if (!nodep->sensp()) return;  // Ignore sequential items (e.g.: initial, comb, etc.)

        m_clockedProcess = true;
        if (nodep->edgeType() != VEdgeType::ET_CHANGED) m_allChanged = false;

        if (const auto* const dtypep = nodep->sensp()->dtypep()) {
            if (const auto* const basicp = dtypep->basicp()) {
                if (basicp->isEvent()) nodep->edgeType(VEdgeType::ET_EVENT);
            }
        }

        nodep->sensp()->foreach([](const AstVarRef* refp) {
            refp->varp()->usedClock(true);
            refp->varScopep()->user1(true);
        });
    }

    void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        if (nodep->access().isWriteOnly()) {
            vscp->user2(true);
        } else {
            // If the variable is read before it is written (and is not a never-changing value),
            // and is not in the sensitivity list, then this cannot be optimized into a
            // combinational process
            // TODO: live variable analysis would be more precise
            if (!vscp->user2() && !vscp->varp()->valuep() && !vscp->user1()) m_canBeComb = false;
        }
    }
    void visit(AstAssignDly* nodep) override {
        m_canBeComb = false;
        if (nodep->isTimingControl()) m_clockedProcess = true;
        iterateChildrenConst(nodep);
    }
    void visit(AstFireEvent* nodep) override {
        m_canBeComb = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstAssignForce* nodep) override {
        m_canBeComb = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstRelease* nodep) override {
        m_canBeComb = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstFork* nodep) override {
        if (nodep->isTimingControl()) {
            m_canBeComb = false;
            m_clockedProcess = true;
        }
        // Do not iterate children, technically not part of this process
    }

    //--------------------
    void visit(AstVar*) override {}  // Accelerate
    void visit(AstVarScope*) override {}  // Accelerate
    void visit(AstNode* nodep) override {
        if (!v3Global.opt.timing().isSetTrue() && m_walkingBody && !m_canBeComb) {
            return;  // Accelerate
        }
        if (!nodep->isPure()) m_canBeComb = false;
        if (nodep->isTimingControl()) {
            m_canBeComb = false;
            m_clockedProcess = true;
            return;
        }
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit ActiveVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ActiveVisitor() override = default;
};

//######################################################################
// Active class functions

void V3Active::activeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ActiveVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("active", 0, dumpTreeLevel() >= 3);
}
