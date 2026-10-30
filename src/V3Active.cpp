// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Active.h"

#include "V3ClassGraph.h"
#include "V3Const.h"
#include "V3Graph.h"

#include <unordered_map>
#include <unordered_set>

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
            // cppcheck-suppress constVariableReference
            for (V3GraphEdge& edge : vertexp->outEdges()) {
                if (latchCheckInternal(castVertexp(edge.top()))) {
                    result = true;
                    break;
                }
            }
            break;
        case LatchDetectGraphVertex::VT_BRANCH:  // (AND of both sibling)
                                                 // A BRANCH vertex always has exactly 2 siblings
            LatchDetectGraphVertex* const ifp = castVertexp(vertexp->outEdges().frontp()->top());
            LatchDetectGraphVertex* const elsp = castVertexp(vertexp->outEdges().backp()->top());
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
        m_curVertexp = new LatchDetectGraphVertex{this, "ROOT"};
    }
    // Clear out userp field of referenced outputs on destruction
    // (occurs at the end of each combinational always block)
    // cppcheck-suppress duplInheritedMember
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
    // Add an infeasible control path (e.g. the absent else of a 'unique if' chain).  An output
    // vertex with user() set represents a path that assigns every output, which is what an
    // unreachable path must do.
    void addUnreachableVertex(LatchDetectGraphVertex* parent) {
        LatchDetectGraphVertex* const vertexp
            = new LatchDetectGraphVertex{this, "UNREACHABLE", LatchDetectGraphVertex::VT_OUTPUT};
        vertexp->user(true);
        new V3GraphEdge{this, parent, vertexp, 1};
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
        for (const AstVarRef* const vrp : m_outputs) {
            LatchDetectGraphVertex* const vertp = castVertexp(vrp->varp()->user1p());
            vertp->user(true);  // Identify the output vertex we are checking paths _to_
            if (!latchCheckInternal(castVertexp(vertices().frontp()))) latch_detected = true;
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
    template <typename T_SenItemKind>
    AstActive*& getSpecialActive();

public:
    // METHODS
    AstScope* scopep() { return m_scopep; }

    // Make a new AstActive sensitive to the given sentree and return it
    AstActive* makeActive(FileLine* const fl, AstSenTree* const senTreep) {
        AstActive* const activep = new AstActive{fl, "", senTreep};
        activep->senTreeStorep(activep->sentreep());
        addActive(activep);
        return activep;
    }

    // Make a new AstActive sensitive to the given special sensitivity class and return it
    template <typename T_SenItemKind>
    AstActive* makeSpecialActive(FileLine* const fl) {
        AstSenTree* const senTreep = new AstSenTree{fl, new AstSenItem{fl, T_SenItemKind{}}};
        return makeActive(fl, senTreep);
    }

    // Return an AstActive sensitive to the given special sensitivity class (possibly pre-created)
    template <typename T_SenItemKind>
    AstActive* getSpecialActive(FileLine* fl) {
        AstActive*& cachep = getSpecialActive<T_SenItemKind>();
        if (!cachep) cachep = makeSpecialActive<T_SenItemKind>(fl);
        return cachep;
    }

    // Return an AstActive that is sensitive to a SenTree equivalent to the given sentreep.
    AstActive* getActive(FileLine* fl, AstSenTree* sentreep) {
        UASSERT(sentreep, "Must be non-null");

        auto it = m_activeMap.find(*sentreep);
        // If found matching AstActive, return it
        if (it != m_activeMap.end()) return it->second;

        // No such AstActive yet, creat it, and add to map.
        AstSenTree* const newsenp = sentreep->cloneTree(false);
        AstActive* const activep = new AstActive{fl, "sequent", newsenp};
        activep->senTreeStorep(activep->sentreep());
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
    // NODE STATE
    // Input:
    //  AstVar::user1p // V2LatchGraphVertex* The vertex handling this node
    const VNUser1InUse m_inuser1;
    // STATE
    LatchDetectGraph m_graph;  // Graph used to detect latches in combo always
    bool m_uniqueIfChain = false;  // Traversing the else-if chain of a 'unique if'
    // VISITORS
    void visit(AstVarRef* nodep) override {
        const AstVar* const varp = nodep->varp();
        if (nodep->access().isWriteOrRW() && varp->isSignal() && !varp->isUsedLoopIdx()
            && !varp->isFuncLocalSticky() && !varp->lifetime().isAutomatic()) {
            m_graph.addAssignment(nodep);
        }
    }
    // This visitor only walks procedural always blocks, so AstNodeIf nodes here are always AstIf.
    void visit(AstIf* nodep) override {
        if (nodep->isBoundsCheck()) {
            iterateChildrenConst(nodep);
            return;
        }

        // IEEE 1800-2023 12.4.2 requires a violation report if a 'unique if' has no matching
        // condition and no explicit else.  Treat that missing else as unreachable for latch
        // detection, consistent with the V3Assert check; 'unique0 if' permits no match and
        // therefore still has a potentially latching path.
        // Note: 'priority if' is omitted because V3Assert does not currently lower it to a
        // runtime check, so suppressing LATCH would hide a latch without a diagnostic.
        const bool exhaustive = m_uniqueIfChain || nodep->uniquePragma();

        LatchDetectGraphVertex* const parentp = m_graph.currentp();
        LatchDetectGraphVertex* const branchp = m_graph.addPathVertex(parentp, "BRANCH", true);

        m_graph.addPathVertex(branchp, "IF");
        {
            VL_RESTORER(m_uniqueIfChain);
            m_uniqueIfChain = false;
            iterateAndNextConstNull(nodep->thensp());
        }

        if (exhaustive && !nodep->elsesp()) {
            m_graph.addUnreachableVertex(branchp);
        } else {
            m_graph.addPathVertex(branchp, "ELSE");
            VL_RESTORER(m_uniqueIfChain);
            m_uniqueIfChain = exhaustive && VN_IS(nodep->elsesp(), If);
            iterateAndNextConstNull(nodep->elsesp());
        }
        m_graph.currentp(parentp);
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
// Analyse the call graph to find functions that may execute a
// '<=' non-blocking assignment or '->>' non-blocking event trigger.
// Evaluated lazily and cached. Functions calling each other in a cycle
// are analysed together, as Tarjan's strongly connected components, so
// every function is visited at most once, and only if it is reachable
// from a call in combinational logic.

class ActiveNbaFuncs final : public VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user3p()      AstNodeStmt*: A '<=' NBA or '->>' the function may execute,
    //                                       or m_nonep sentinel if none. Unset until found or
    //                                       analysed, so also while analysed and none found yet.
    const VNUser3InUse m_user3InUse;

    // STATE
    // Sentinel for functions without NBAs
    AstNodeStmt* const m_nonep = new AstComment{v3Global.rootp()->fileline(), "none"};
    AstCFunc* m_funcp = nullptr;  // Current function being analysed
    std::vector<AstCFunc*> m_stack;  // Functions being analysed
    std::unordered_map<const AstCFunc*, size_t> m_stackIndex;  // Index of each in 'm_stack'
    size_t m_low = 0;  // Lowest index in 'm_stack' of a function current 'm_funcp' calls
    std::unique_ptr<V3ClassGraph> m_classGraphp;  // Virtual functions a call may resolve to

    // METHODS
    // Whether the function being analysed has an NBA already
    bool found() const {
        UASSERT_OBJ(m_funcp->user3p() != m_nonep, m_funcp, "None while being analysed");
        return m_funcp->user3p() != nullptr;
    }
    // Return the one 'funcp' may execute, m_nonep if none, or nullptr if none found yet in a
    // cycle still being analysed. A cycle is complete when the first of its functions to be
    // analysed finishes.
    AstNode* findNba(AstCFunc* funcp) {
        if (funcp->user3p()) return funcp->user3p();

        const auto pair = m_stackIndex.emplace(funcp, m_stack.size());
        if (!pair.second) {  // Being analysed, so in a cycle with 'm_funcp'
            m_low = std::min(m_low, pair.first->second);
            return nullptr;
        }
        const size_t index = m_stack.size();
        m_stack.push_back(funcp);
        size_t low;
        {
            VL_RESTORER(m_funcp);
            VL_RESTORER(m_low);
            m_funcp = funcp;
            m_low = index;
            iterateChildrenConst(funcp);
            low = m_low;
        }
        if (low < index) {  // In a cycle with a function still being analysed
            m_low = std::min(m_low, low);
            return funcp->user3p();
        }
        // Done with the cycle, its functions may execute any one found in them
        AstNode* nbap = m_nonep;
        for (size_t i = index; i < m_stack.size(); ++i) {
            if (m_stack[i]->user3p()) nbap = m_stack[i]->user3p();
        }
        for (size_t i = index; i < m_stack.size(); ++i) {
            if (!m_stack[i]->user3p()) m_stack[i]->user3p(nbap);
            m_stackIndex.erase(m_stack[i]);
        }
        m_stack.resize(index);
        return funcp->user3p();
    }
    // Return the one 'callp' may execute, or nullptr if none, or none found yet in a cycle
    // still being analysed
    AstNodeStmt* findNba(AstNodeCCall* callp) {
        if (callp->funcp()->dpiImportWrapper()) return nullptr;
        if (!m_classGraphp) m_classGraphp = V3ClassGraph::build(v3Global.rootp());
        const std::unordered_set<AstCFunc*>& funcps = m_classGraphp->getCallPossibleCFuncs(callp);
        if (funcps.empty()) {
            AstNode* const nbap = findNba(callp->funcp());
            if (nbap && nbap != m_nonep) return VN_AS(nbap, NodeStmt);
        }
        for (AstCFunc* const funcp : funcps) {
            AstNode* const nbap = findNba(funcp);
            if (nbap && nbap != m_nonep) return VN_AS(nbap, NodeStmt);
        }
        return nullptr;
    }

    // VISITORS
    void visit(AstAssignDly* nodep) override {
        if (found()) return;
        m_funcp->user3p(nodep);  // Found one now
    }
    void visit(AstFireEvent* nodep) override {
        if (found()) return;
        if (nodep->isDelayed()) {
            m_funcp->user3p(nodep);  // Found one now
        } else {
            iterateChildrenConst(nodep);
        }
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        if (AstNodeStmt* const nbap = findNba(nodep)) m_funcp->user3p(nbap);  // Found one now
    }
    void visit(AstNode* nodep) override {
        if (found()) return;
        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    ActiveNbaFuncs() = default;
    ~ActiveNbaFuncs() override { m_nonep->deleteTree(); }

    // METHODS
    // Return an AstAssignDly or non-blocking AstFireEvent the 'callp' may execute, if any
    const AstNodeStmt* containsNba(AstNodeCCall* callp) { return findNba(callp); }
};

//######################################################################
// Replace unsupported non-blocking assignments with blocking assignments

class ActiveDlyVisitor final : public VNVisitor {
public:
    enum CheckType : uint8_t { CT_COMB, CT_FINAL };

private:
    // MEMBERS
    const CheckType m_check;  // Process type we are checking
    ActiveNbaFuncs& m_nbaFuncs;  // Functions that may execute a non-blocking assignment

    // VISITORS
    void visit(AstNodeCCall* nodep) override {
        if (m_check == CT_COMB) {
            if (const AstNodeStmt* const nbap = m_nbaFuncs.containsNba(nodep)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Non-blocking assignment in a function "
                                             "called from combinational logic\n"
                                                 << nodep->warnContextPrimary() << '\n'
                                                 << nbap->warnOther()
                                                 << "... Location of the non-blocking assignment\n"
                                                 << nbap->warnContextSecondary());
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstAssignDly* nodep) override {
        // Issue appropriate warning
        if (m_check == CT_FINAL) {
            nodep->v3warn(FINALDLY, "Non-blocking assignment '<=' in final block");
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

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    ActiveDlyVisitor(AstNode* nodep, CheckType check, ActiveNbaFuncs& nbaFuncs)
        : m_check{check}
        , m_nbaFuncs{nbaFuncs} {
        iterate(nodep);
    }
    ~ActiveDlyVisitor() override = default;
};

//######################################################################
// Active class functions

class ActiveVisitor final : public VNVisitor {
    // NODE STATE
    //  Each call to V3Const::constify
    //   AstVarScope::user1()           bool: This VarScope is referenced in the sensitivity list
    //   AstVarScope::user2()           bool: This VarScope is written in the current process
    //   AstNode::user4()               Used by V3Const::constify, called below

    // STATE
    ActiveNamer m_namer;  // Tracking of active names
    ActiveNbaFuncs m_nbaFuncs;  // Functions that may execute a non-blocking assignment
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

    void visitAlways(AstNode* nodep, AstSenTree* oldsentreep, VAlwaysKwd kwd) {
        // Move always to appropriate ACTIVE based on its sense list
        if (oldsentreep && oldsentreep->sensesp() && oldsentreep->sensesp()->isNever()) {
            // Never executing.  Kill it.
            UASSERT_OBJ(!oldsentreep->sensesp()->nextp(), nodep,
                        "Never senitem should be alone, else the never should be eliminated.");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }

        {
            const VNUser1InUse user1InUse;

            // Walk sensitivity list
            m_clockedProcess = false;
            m_allChanged = true;
            if (oldsentreep) {
                oldsentreep->unlinkFrBack();
                iterateChildrenConst(oldsentreep);
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
              : oldsentreep     ? m_namer.getActive(nodep->fileline(), oldsentreep)
                            // Clocked, no sensitivity lists, it's a suspendable, put it in initial
                            : m_namer.getSpecialActive<AstSenItem::Initial>(nodep->fileline());

        // Move node to new active
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);

        // Warn and convert any delayed assignments
        if (!m_clockedProcess) ActiveDlyVisitor{nodep, ActiveDlyVisitor::CT_COMB, m_nbaFuncs};

        // Delete sensitivity list
        if (oldsentreep) VL_DO_DANGLING(oldsentreep->deleteTree(), oldsentreep);

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

    static void markEventEdges(AstSenTree* sentreep) {
        for (AstSenItem* const senip : sentreep->sensespList()) {
            if (!senip->sensp()) continue;
            if (const AstNodeDType* const dtypep = senip->sensp()->dtypep()) {
                if (const AstBasicDType* const basicp = dtypep->basicp()) {
                    if (basicp->isEvent()) senip->edgeType(VEdgeType::ET_EVENT);
                }
            }
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
        visitSenItems(nodep);
        moveUnderSpecial<AstSenItem::Initial>(nodep);
    }
    void visit(AstFinal* nodep) override {
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_FINAL, m_nbaFuncs};
        moveUnderSpecial<AstSenItem::Final>(nodep);
    }
    void visit(AstCoverToggle* nodep) override { moveUnderSpecial<AstSenItem::Combo>(nodep); }
    void visit(AstAlways* nodep) override {
        if (!nodep->stmtsp()) {  // Empty always. Remove it now.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        if (nodep->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_COMB, m_nbaFuncs};
            moveUnderSpecial<AstSenItem::Combo>(nodep);
            return;
        }
        visitSenItems(nodep);
        visitAlways(nodep, nodep->sentreep(), nodep->keyword());
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
        UASSERT_OBJ(nodep->sentreep(), nodep, "Should have a sentree");
        markEventEdges(nodep->sentreep());
        AstSenTree* const sentreep = nodep->sentreep();
        sentreep->unlinkFrBack();
        // Make a new active for it, needs to be the only item under the active for V3Sched
        AstActive* const activep = m_namer.makeActive(nodep->fileline(), sentreep);
        activep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstAlwaysReactive* nodep) override {
        UASSERT_OBJ(nodep->sentreep(), nodep, "Should have a sentree");
        markEventEdges(nodep->sentreep());
        AstSenTree* const sentreep = nodep->sentreep();
        sentreep->unlinkFrBack();
        // Make a new active for it, needs to be the only item under the active for V3Sched
        AstActive* const activep = m_namer.makeActive(nodep->fileline(), sentreep);
        activep->addStmtsp(nodep->unlinkFrBack());
    }
    void visit(AstCFunc* nodep) override { visitSenItems(nodep); }
    void visit(AstSenItem* nodep) override {
        UASSERT_OBJ(!m_walkingBody, nodep,
                    "Should not reach here when walking body without --timing");
        if (!nodep->sensp()) return;  // Ignore sequential items (e.g.: initial, comb, etc.)

        m_clockedProcess = true;
        if (nodep->edgeType() != VEdgeType::ET_CHANGED) m_allChanged = false;

        if (const AstNodeDType* const dtypep = nodep->sensp()->dtypep()) {
            if (const AstBasicDType* const basicp = dtypep->basicp()) {
                if (basicp->isEvent()) nodep->edgeType(VEdgeType::ET_EVENT);
            }
        }

        nodep->sensp()->foreach([](const AstVarRef* refp) { refp->varScopep()->user1(true); });
    }

    void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        if (nodep->access().isWriteOnly()) {
            vscp->user2(true);
        } else {
            // If the variable is read before it is written (and is not a never-changing value,
            // including an X randomization temporary set once at initialization), and is not
            // in the sensitivity list, then this cannot be optimized into a combinational process
            // TODO: live variable analysis would be more precise
            const AstVar* const varp = vscp->varp();
            if (!vscp->user2() && !varp->valuep() && !varp->isXTemp() && !vscp->user1()) {
                m_canBeComb = false;
            }
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
// Pass 1: collect sample CFuncs and sampling events from covergroup class scopes

class CovergroupCollectVisitor final : public VNVisitor {
    // NODE STATE
    // Netlist:
    //  AstClass::user1p()  -> AstCFunc*.    The sample() CFunc for this covergroup class
    //  AstClass::user2p()  -> AstSenTree*.  Owned sampling event template (if any)

    // STATE
    AstClass* m_classp = nullptr;  // Current covergroup class context, or nullptr

    // VISITORS
    void visit(AstClass* nodep) override {
        if (!nodep->isCovergroup()) return;
        VL_RESTORER(m_classp);
        m_classp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstScope* nodep) override { iterateChildren(nodep); }

    void visit(AstCFunc* nodep) override {
        if (!m_classp) return;
        if (nodep->isCovergroupSample()) m_classp->user1p(nodep);
    }

    void visit(AstCovergroup* nodep) override {
        // V3Covergroup guarantees: only supported-event covergroups survive to V3Active,
        // and they are always inside a covergroup class (so m_classp is set).
        // Unlink eventp from cgp so it survives cgp's deletion,
        // then store it in user2p for use during the second pass.
        m_classp->user2p(nodep->eventp()->unlinkFrBack());
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CovergroupCollectVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CovergroupCollectVisitor() override = default;
};

//######################################################################
// Pass 2: inject automatic sample() calls for covergroup instances

class CovergroupEventBindVisitor final : public VNVisitor {
    AstVarScope* const m_instancep;  // Variable scope for the covergroup instance being sampled
    std::unordered_set<const AstVar*> m_memberps;  // Non-static variables in the covergroup class

    void visit(AstVarRef* nodep) override {
        if (!m_memberps.count(nodep->varp())) return;
        FileLine* const fl = nodep->fileline();
        AstMemberSel* const selp
            = new AstMemberSel{fl, new AstVarRef{fl, m_instancep, VAccess::READ}, nodep->varp()};
        selp->access(nodep->access());
        nodep->replaceWith(selp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    CovergroupEventBindVisitor(AstSenTree* eventp, AstClass* classp, AstVarScope* instancep)
        : m_instancep{instancep} {
        classp->foreachMember([&](AstClass* const, AstVar* const varp) {  //
            m_memberps.emplace(varp);
        });
        iterate(eventp);
    }
    ~CovergroupEventBindVisitor() override = default;
};

class CovergroupInjectVisitor final : public VNVisitor {
    // NODE STATE  (set by CovergroupCollectVisitor, consumed here)
    //  AstClass::user1p()  -> AstCFunc*.    The sample() CFunc for this covergroup class
    //  AstClass::user2p()  -> AstSenTree*.  Owned sampling event template (if any)

    // STATE
    ActiveNamer m_namer;  // Reuse active naming infrastructure

    // VISITORS
    void visit(AstScope* nodep) override {
        m_namer.main(nodep);  // Initialize active naming for this scope
        iterateChildren(nodep);
    }

    void visit(AstVarScope* nodep) override {
        // Get the underlying var
        AstVar* const varp = nodep->varp();
        UASSERT_OBJ(varp, nodep, "AstVarScope must have non-null varp");

        // Check if the variable is of covergroup class type
        const AstNodeDType* const dtypep = varp->dtypep();
        UASSERT_OBJ(dtypep, nodep, "AstVar must have non-null dtypep after V3Width");

        const AstClassRefDType* const classRefp = VN_CAST(dtypep, ClassRefDType);
        if (!classRefp) return;

        AstClass* const classp = classRefp->classp();

        // Check if this covergroup has an automatic sampling event
        AstSenTree* const eventp = VN_CAST(classp->user2p(), SenTree);
        if (!eventp) return;  // No automatic sampling for this covergroup

        // V3Covergroup guarantees every supported-event covergroup has a registered sample CFunc
        AstCFunc* const sampleCFuncp = VN_AS(classp->user1p(), CFunc);
        UASSERT_OBJ(sampleCFuncp, nodep,
                    "No sample() CFunc found for covergroup " << classp->name());

        // Create a VarRef to the covergroup instance for the method call
        FileLine* const fl = nodep->fileline();
        AstVarRef* const varrefp = new AstVarRef{fl, nodep, VAccess::READ};

        // Create the CMethodCall to sample()
        // Note: We don't pass arguments in argsp since vlSymsp is passed via argTypes
        AstCMethodCall* const cmethodCallp
            = new AstCMethodCall{fl, varrefp, sampleCFuncp, nullptr};

        cmethodCallp->dtypeSetVoid();
        cmethodCallp->argTypes("vlSymsp");

        // Clone the sensitivity for this active block. References to covergroup members need
        // to select through this particular instance; all other VarRefs retain the VarScopes
        // resolved by V3Scope.
        AstSenTree* senTreep = eventp->cloneTree(false);
        CovergroupEventBindVisitor{senTreep, classp, nodep};

        // Get or create the AstActive node for this sensitivity
        // senTreep is a template used by getActive() which clones it into the AstActive;
        // delete it afterwards as it is not added to the AST directly.
        AstActive* const activep = m_namer.getActive(fl, senTreep);
        VL_DO_DANGLING(pushDeletep(senTreep), senTreep);

        // Wrap the sample() call in an AstAlways so SchedPartition handles it
        // via visit(AstNodeProcedure*) like any other clocked always block.
        activep->addStmtsp(
            new AstAlways{fl, VAlwaysKwd::ALWAYS_FF, nullptr, cmethodCallp->makeStmt()});
    }

    void visit(AstClass* nodep) override {
        iterateChildren(nodep);
        // Delete the owned sampling event template stored during collection
        if (AstSenTree* const eventp = VN_CAST(nodep->user2p(), SenTree)) {
            VL_DO_DANGLING(pushDeletep(eventp), eventp);
        }
    }

    void visit(AstActive*) override {}  // Don't iterate into actives
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CovergroupInjectVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CovergroupInjectVisitor() override = default;
};

//######################################################################
// Active class functions

void V3Active::activeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ActiveVisitor{nodep}; }  // Destruct before checking
    if (v3Global.useCovergroup()) {
        // Add automatic covergroup sampling in two focused passes.
        // user1p/user2p on AstClass span both passes; guards must outlive both visitors.
        const VNUser1InUse user1InUse;
        const VNUser2InUse user2InUse;
        CovergroupCollectVisitor{nodep};  // Pass 1: collect CFuncs and events into user#p
        CovergroupInjectVisitor{nodep};  // Pass 2: inject sample() calls, delete user2p events
    }
    V3Global::dumpCheckGlobalTree("active", 0, dumpTreeEitherLevel() >= 3);
}
