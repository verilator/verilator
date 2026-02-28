// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reorder statements within always blocks
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
// V3Reorder transformations:
//
//  reorderAll() reorders statements within individual blocks to avoid
//  shwdow variables use by non blocking assignments when possible.
//  For exmaple, the left side needs a shadow variable for 'b', the
//  right side does not:
//      Bad:            Good:
//          b <= a;         c <= b;
//          c <= b;         b <= a;
//
// The scoreboard tracks data deps as follows:
//
//      ALWAYS
//              ASSIGN ({var} <= {cons})
//              Record as generating var_DLY (independent of use of var), consumers
//              ASSIGN ({var} = {cons}
//              Record generator and consumer
//      Any var that is only consumed can be ignored.
//      Then we split into separate ALWAYS blocks.
//
// The scoreboard includes innards of if/else nodes also.  Splitting is no
// longer limited to top-level statements, we can split within if-else
// blocks. We want to be able to split this:
//
// The optional reorder routine can optimize this:
//      NODEASSIGN/NODEIF/WHILE
//              S1: ASSIGN {v1} <= 0.   // Duplicate of below
//              S2: ASSIGN {v1} <= {v0}
//              S3: IF (...,
//                      X1: ASSIGN {v2} <= {v1}
//                      X2: ASSIGN {v3} <= {v2}
//      We'd like to swap S2 and S3, and X1 and X2.
//
//  Create a graph in split assignment order.
//      v3 -breakable-> v3Dly --> X2 --> v2 -brk-> v2Dly -> X1 -> v1
//      Likewise on each "upper" statement vertex
//              v3Dly & v2Dly -> S3 -> v1 & v2
//              v1 -brk-> v1Dly -> S2 -> v0
//                        v1Dly -> S1 -> {empty}
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Reorder.h"

#include "V3EmitV.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <string>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

//######################################################################
// Support classes

class ReorderNodeVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(ReorderNodeVertex, V3GraphVertex)
    AstNode* const m_nodep;

protected:
    ReorderNodeVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    ~ReorderNodeVertex() override = default;
    // ACCESSORS
    // Do not make accessor for nodep(),  It may change due to
    // reordering a lower block, but we don't repair it
    std::string name() const override {
        std::string str = cvtToHex(m_nodep) + '\n';
        if (AstVarScope* const vscp = VN_CAST(m_nodep, VarScope)) {
            str += vscp->prettyName();
        } else {
            str += V3EmitV::debugVerilogForTree(m_nodep);
            str = VString::quoteBackslash(str);
            str = VString::quoteAny(str, '"', '\\');
            str = VString::replaceSubstr(str, "\n", "\\l");
        }
        return str;
    }
    FileLine* fileline() const override { return nodep()->fileline(); }
    std::string dotShape() const override { return VN_IS(m_nodep, VarScope) ? "ellipse" : "box"; }

public:
    virtual AstNode* nodep() const { return m_nodep; }
};

class ReorderImpureVertex final : public ReorderNodeVertex {
    VL_RTTI_IMPL(ReorderImpureVertex, ReorderNodeVertex)
public:
    explicit ReorderImpureVertex(V3Graph* graphp, AstNode* nodep)
        : ReorderNodeVertex{graphp, nodep} {}
    ~ReorderImpureVertex() override = default;
    string name() const override VL_MT_STABLE { return "*IMPURE*"; }
    string dotColor() const override { return "red"; }
};

class ReorderLogicVertex final : public ReorderNodeVertex {
    VL_RTTI_IMPL(ReorderLogicVertex, ReorderNodeVertex)
public:
    ReorderLogicVertex(V3Graph* graphp, AstNode* nodep)
        : ReorderNodeVertex{graphp, nodep} {}
    ~ReorderLogicVertex() override = default;
    string dotColor() const override { return "black"; }
};

class ReorderVarStdVertex final : public ReorderNodeVertex {
    VL_RTTI_IMPL(ReorderVarStdVertex, ReorderNodeVertex)
public:
    ReorderVarStdVertex(V3Graph* graphp, AstVarScope* nodep)
        : ReorderNodeVertex{graphp, nodep} {}
    ~ReorderVarStdVertex() override = default;
    string dotColor() const override { return "blue"; }
};

class ReorderVarPostVertex final : public ReorderNodeVertex {
    VL_RTTI_IMPL(ReorderVarPostVertex, ReorderNodeVertex)
public:
    ReorderVarPostVertex(V3Graph* graphp, AstVarScope* nodep)
        : ReorderNodeVertex{graphp, nodep} {}
    ~ReorderVarPostVertex() override = default;
    string name() const override { return "POST "s + ReorderNodeVertex::name(); }
    string dotColor() const override { return "green"; }
};

//######################################################################
// Edge types

class ReorderEdge VL_NOT_FINAL : public V3GraphEdge {
    VL_RTTI_IMPL(ReorderEdge, V3GraphEdge)
    uint32_t m_ignoreInStep = 0;  // Step number that if set to, causes this edge to be ignored
    static uint32_t s_stepNum;  // Global step number
protected:
    static constexpr int WEIGHT_NORMAL = 10;
    ReorderEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, bool cutable)
        : V3GraphEdge{graphp, fromp, top, WEIGHT_NORMAL, cutable} {}
    ~ReorderEdge() override = default;

    virtual bool followScoreboard() const = 0;

    std::string dotStyle() const override {
        return ignoreThisStep() ? "dotted" : V3GraphEdge::dotStyle();
    }

public:
    // Iterator for graph functions
    static void incrementStep() { ++s_stepNum; }
    bool ignoreThisStep() const { return m_ignoreInStep == s_stepNum; }
    void setIgnoreThisStep() { m_ignoreInStep = s_stepNum; }

    static bool followScoreboard(const V3GraphEdge* edgep) {
        const ReorderEdge& edge = *edgep->as<ReorderEdge>();
        return !edge.ignoreThisStep() && edge.followScoreboard();
    }
    static bool followCyclic(const V3GraphEdge* edgep) {
        const ReorderEdge& edge = *edgep->as<ReorderEdge>();
        return !edge.ignoreThisStep();
    }
};
uint32_t ReorderEdge::s_stepNum = 0;

class ReorderPostEdge final : public ReorderEdge {
    VL_RTTI_IMPL(ReorderPostEdge, ReorderEdge)
public:
    ReorderPostEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : ReorderEdge{graphp, fromp, top, CUTABLE} {}
    ~ReorderPostEdge() override = default;
    bool followScoreboard() const override { return false; }
    string dotColor() const override { return "khaki"; }
};

class ReorderLVEdge final : public ReorderEdge {
    VL_RTTI_IMPL(ReorderLVEdge, ReorderEdge)
public:
    ReorderLVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : ReorderEdge{graphp, fromp, top, CUTABLE} {}
    ~ReorderLVEdge() override = default;
    bool followScoreboard() const override { return true; }
    string dotColor() const override { return "yellowGreen"; }
};

class ReorderRVEdge final : public ReorderEdge {
    VL_RTTI_IMPL(ReorderRVEdge, ReorderEdge)
public:
    ReorderRVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : ReorderEdge{graphp, fromp, top, CUTABLE} {}
    ~ReorderRVEdge() override = default;
    bool followScoreboard() const override { return true; }
    string dotColor() const override { return "green"; }
};

class ReorderScorebdEdge final : public ReorderEdge {
    VL_RTTI_IMPL(ReorderScorebdEdge, ReorderEdge)
public:
    ReorderScorebdEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : ReorderEdge{graphp, fromp, top, CUTABLE} {}
    ~ReorderScorebdEdge() override = default;
    bool followScoreboard() const override { return true; }
    string dotColor() const override { return "blue"; }
};

class ReorderStrictEdge final : public ReorderEdge {
    VL_RTTI_IMPL(ReorderStrictEdge, ReorderEdge)
    // A strict order, based on the original statement order in the graph
    // The only non-cutable edge type
public:
    ReorderStrictEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : ReorderEdge{graphp, fromp, top, NOT_CUTABLE} {}
    ~ReorderStrictEdge() override = default;
    bool followScoreboard() const override { return true; }
    string dotColor() const override { return "blue"; }
};

//######################################################################
// Reorder class functions

class ReorderVisitor final : public VNVisitor {
    // NODE STATE - Only under AstAlways
    // AstVarScope::user1p  -> Var ReorderVarStdVertex* for usage var, 0=not set yet
    // AstVarScope::user2p  -> Var ReorderVarPostVertex* for delayed assignment var, 0=not set yet
    // Ast*::user3p         -> Statement ReorderLogicVertex* (temporary only)
    // Ast*::user4          -> Current ordering number (reorderBlock usage)

    // STATE
    V3Graph* m_graphp = nullptr;  // Scoreboard of var usages/dependencies
    ReorderImpureVertex* m_impureVtxp = nullptr;  // Element specifying PLI ordering
    bool m_inDly = false;  // Inside ASSIGNDLY
    const char* m_noReorderWhy = nullptr;  // Reason we can't reorder
    std::vector<ReorderLogicVertex*> m_stmtStackps;  // Current statements being tracked

    // METHODS
    void cleanupBlockGraph(AstNode* nodep) {
        // Transform the graph into what we need
        UINFO(5, "ReorderBlock " << nodep);

        // Simplify graph by removing redundant edges
        m_graphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("reorderg_nodup", false);

        // Mark all the logic for this step by setting Vertex::user() to true
        m_graphp->userClearVertices();
        for (AstNode* nextp = nodep; nextp; nextp = nextp->nextp()) {
            nextp->user3u().to<ReorderLogicVertex*>()->user(true);
        }

        // New step
        ReorderEdge::incrementStep();

        // If a var vertex has only inputs, it's a input-only node,
        // and can be ignored for coloring **this block only**
        for (V3GraphVertex& vtx : m_graphp->vertices()) {
            if (!vtx.outEmpty()) continue;
            if (!vtx.is<ReorderVarStdVertex>()) continue;
            for (V3GraphEdge& edge : vtx.inEdges()) edge.as<ReorderEdge>()->setIgnoreThisStep();
        }

        // For reordering this single block only, mark all logic
        // vertexes not involved with this step as unimportant
        for (V3GraphVertex& vertex : m_graphp->vertices()) {
            if (vertex.user()) continue;
            if (!vertex.is<ReorderLogicVertex>()) continue;
            for (V3GraphEdge& edge : vertex.inEdges()) edge.as<ReorderEdge>()->setIgnoreThisStep();
            for (V3GraphEdge& edge : vertex.outEdges())
                edge.as<ReorderEdge>()->setIgnoreThisStep();
        }

        // Weak coloring to determine what needs to remain in order
        // This follows all step-relevant edges excluding PostEdges, which are done later
        m_graphp->weaklyConnected(&ReorderEdge::followScoreboard);

        // Add hard orderings between all nodes of same color, in the order they appeared
        std::unordered_map<uint32_t, ReorderLogicVertex*> lastOfColor;
        for (AstNode* currp = nodep; currp; currp = currp->nextp()) {
            ReorderLogicVertex* const vtxp = currp->user3u().to<ReorderLogicVertex*>();
            const uint32_t color = vtxp->color();
            UASSERT_OBJ(color, currp, "No node color assigned");
            if (lastOfColor[color]) new ReorderStrictEdge{m_graphp, lastOfColor[color], vtxp};
            lastOfColor[color] = vtxp;
        }

        // And a real ordering to get the statements into something reasonable
        // We don't care if there's cutable violations here...
        // Non-cutable violations should be impossible; as those edges are program-order
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("reorderg_pre", false);
        m_graphp->acyclic(&ReorderEdge::followCyclic);
        m_graphp->rank(&ReorderEdge::followCyclic);  // Or order(), but that's more expensive
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("reorderg_opt", false);
    }

    void reorderBlock(AstNode* nodep) {
        // Reorder statements in the completed graph

        // Map the rank numbers into nodes they associate with
        std::multimap<uint32_t, AstNode*> rankMap;
        int currOrder = 0;  // Existing sequence number of assignment
        for (AstNode* currp = nodep; currp; currp = currp->nextp()) {
            const ReorderLogicVertex* const vtxp = currp->user3u().to<ReorderLogicVertex*>();
            rankMap.emplace(vtxp->rank(), currp);
            currp->user4(++currOrder);  // Record current ordering
        }

        // Is the current ordering OK?
        bool leaveAlone = true;
        int newOrder = 0;  // New sequence number of assignment
        for (const auto& item : rankMap) {
            const AstNode* const nextp = item.second;
            if (++newOrder != nextp->user4()) leaveAlone = false;
        }
        if (leaveAlone) {
            UINFO(6, "   No changes");
            return;
        }

        VNRelinker replaceHandle;  // Where to add the list
        AstNode* newListp = nullptr;
        for (const auto& item : rankMap) {
            AstNode* const nextp = item.second;
            UINFO(6, "   New order: " << nextp);
            nextp->unlinkFrBack(nextp == nodep ? &replaceHandle : nullptr);
            newListp = AstNode::addNext(newListp, nextp);
        }
        replaceHandle.relink(newListp);
    }

    void processBlock(AstNode* nodep) {
        if (m_noReorderWhy) return;

        // Empty lists are ignorable
        if (!nodep) return;
        UASSERT_OBJ(nodep->firstAbovep(), nodep, "Node passed is in not head of list");
        UASSERT_OBJ(!nodep->user3p(), nodep, "Should not have a logic vertex");

        // It nothing to reorder with, just iterate
        if (!nodep->nextp()) {
            iterate(nodep);
            return;
        }

        // Process it
        UINFO(9, "  processBlock " << nodep);

        // Iterate across current block, making the scoreboard
        for (AstNode* currp = nodep; currp; currp = currp->nextp()) {
            // Create the logic vertex for this statement
            UASSERT_OBJ(!currp->user3p(), currp, "user3p should not be set");
            ReorderLogicVertex* const vtxp = new ReorderLogicVertex{m_graphp, currp};
            currp->user3p(vtxp);

            // Visit the statement - this can recursively reorder sub statements
            m_stmtStackps.push_back(vtxp);
            iterate(currp);
            m_stmtStackps.pop_back();
        }

        if (m_noReorderWhy) {  // Jump or something nasty
            UINFO(9, "  NoReorderBlock because " << m_noReorderWhy);
            return;
        }

        // Reorder statements in this block
        cleanupBlockGraph(nodep);
        reorderBlock(nodep);

        // 'nodep' might no longer be the head of the list, rewind
        while (nodep->backp()->nextp() == nodep) nodep = nodep->backp();

        // Delete vertexes and edges only applying to this block
        for (AstNode* currp = nodep; currp; currp = currp->nextp()) {
            currp->user3u().to<ReorderLogicVertex*>()->unlinkDelete(m_graphp);
            currp->user3p(nullptr);
        }
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        UASSERT_OBJ(!m_graphp, nodep, "AstAlways should not nest");
        VL_RESTORER(m_graphp);
        VL_RESTORER(m_impureVtxp);
        VL_RESTORER(m_inDly);
        VL_RESTORER(m_noReorderWhy);

        V3Graph graph;
        m_graphp = &graph;
        m_impureVtxp = nullptr;
        m_inDly = false;
        m_noReorderWhy = nullptr;

        const VNUser1InUse user1InUse;
        const VNUser2InUse user2InUse;
        const VNUser3InUse user3InUse;
        const VNUser4InUse user4InUse;

        UINFOTREE(9, nodep, "", "alwIn:");
        processBlock(nodep->stmtsp());
        UINFOTREE(9, nodep, "", "alwOut");

        m_stmtStackps.clear();
    }

    void visit(AstNodeIf* nodep) override {
        if (!m_graphp || m_noReorderWhy) return;
        iterateAndNextNull(nodep->condp());
        processBlock(nodep->thensp());
        processBlock(nodep->elsesp());
    }

    void visit(AstJumpGo* nodep) override {
        if (!m_graphp || m_noReorderWhy) return;
        m_noReorderWhy = "JumpGo";
        iterateChildren(nodep);
    }

    void visit(AstExprStmt* nodep) override {
        if (!m_graphp || m_noReorderWhy) return;
        VL_RESTORER(m_inDly);
        m_inDly = false;
        iterateChildren(nodep);
    }

    void visit(AstAssignDly* nodep) override {
        if (!m_graphp || m_noReorderWhy) return;
        iterate(nodep->rhsp());
        VL_RESTORER(m_inDly);
        m_inDly = true;
        iterate(nodep->lhsp());
    }

    void visit(AstVarRef* nodep) override {
        if (!m_graphp || m_noReorderWhy) return;
        if (m_stmtStackps.empty()) return;

        // Reads of constants can be ignored - TODO: This should be "constexpr", not run-time const
        if (nodep->varp()->isConst()) return;

        // SPEEDUP: We add duplicate edges, that should be fixed

        AstVarScope* const vscp = nodep->varScopep();

        // Create vertexes for variable
        if (!vscp->user1p()) vscp->user1p(new ReorderVarStdVertex{m_graphp, vscp});
        ReorderVarStdVertex* const vstdp = vscp->user1u().to<ReorderVarStdVertex*>();

        // Variable is read
        if (nodep->access().isReadOnly()) {
            for (ReorderLogicVertex* const vtxp : m_stmtStackps) {
                new ReorderRVEdge{m_graphp, vtxp, vstdp};
            }
            return;
        }

        // Variable is written, not NBA
        if (!m_inDly) {
            for (ReorderLogicVertex* const vtxp : m_stmtStackps) {
                new ReorderLVEdge{m_graphp, vstdp, vtxp};
            }
            return;
        }

        // Variable is written by NBA
        if (!vscp->user2p()) {
            ReorderVarPostVertex* const vpostp = new ReorderVarPostVertex{m_graphp, vscp};
            vscp->user2p(vpostp);
            new ReorderPostEdge{m_graphp, vstdp, vpostp};
        }
        ReorderVarPostVertex* const vpostp = vscp->user2u().to<ReorderVarPostVertex*>();
        for (ReorderLogicVertex* const vtxp : m_stmtStackps) {
            new ReorderLVEdge{m_graphp, vpostp, vtxp};
        }
    }

    void visit(AstNode* nodep) override {
        // Outside AstAlways, just descend
        if (!m_graphp) {
            iterateChildren(nodep);
            return;
        }

        // Early exit if decided not to reorder
        if (m_noReorderWhy) return;

        // Timing control prevents reordering
        if (nodep->isTimingControl()) {
            m_noReorderWhy = "TimingControl";
            return;
        }

        // Order all impure statements with other impure statements
        if (!nodep->isPure()) {
            if (!m_impureVtxp) m_impureVtxp = new ReorderImpureVertex{m_graphp, nodep};
            // This edge is only used to find weakly connected components, so one edge is enough
            for (ReorderLogicVertex* const vtxp : m_stmtStackps) {
                new ReorderScorebdEdge{m_graphp, m_impureVtxp, vtxp};
            }
        }

        iterateChildren(nodep);
    }

    // CONSTRUCTORS
public:
    explicit ReorderVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ReorderVisitor() override = default;
};

}  // namespace

//######################################################################
// V3Reorder class functions

void V3Reorder::reorderAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ReorderVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("reorder", 0, dumpTreeEitherLevel() >= 3);
}
