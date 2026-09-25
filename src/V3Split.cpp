// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements
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
// V3Split transformation:
//
//  splitAll() splits large always blocks into smaller always blocks when
//  possible, without changing the order of dependent statements relative to
//  one another. Splitting is not limited to top-level statements, if-else
//  blocks can also be split, so that:
//
//    always @ (...) begin
//      if (reset) begin
//        a <= 0;
//        b <= 0;
//         // ... ten thousand more
//      end
//      else begin
//        a <= a_in;
//        b <= b_in;
//         // ... ten thousand more
//      end
//    end
//
// becomes a separate block for each of a, b, and so on.  Even though this
// requires duplicating the conditional many times, it's usually better as it
// reduces ordering constraints, and later optimizations can merge
// conditionals.
//
// To find what must stay together, a graph is built per always block, holding
// a vertex per 'leaf' and 'if' statement, and up to two vertices per variable.
// Statements in the same connected component must stay in one block, and each
// component then becomes a block of its own. The edges are:
//
//   - Blocking write: variable -> statement. Such a write is observable within
//     the block, so the readers of the variable stay with the writer.
//   - Non-blocking write: a separate 'post' vertex of the variable -> statement.
//     All writers of a variable stay together, but the readers, which see the
//     value from before the NBA commits, are not held together with them.
//   - Read: statement -> variable. For an 'if', only the reads in its own
//     condition count, not those in its branches.
//   - Impure statement: statement -> a vertex shared by all of them, so that
//     $display, DPI calls, etc stay in one block, in order.
//
// A variable with no blocking write is an input to the block, so its vertex is
// removed, and with it the dependencies on it, as two statements both reading
// an input need not stay together. An 'if' left with no dependencies of its
// own is removed likewise, so that the statements under it can separate, each
// taking a copy of the condition.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Split.h"

#include "V3Graph.h"
#include "V3Stats.h"

#include <string>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Support classes

class SplitNodeVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(SplitNodeVertex, V3GraphVertex)
    AstNode* const m_nodep;

protected:
    SplitNodeVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    // ACCESSORS
    std::string name() const override {
        return cvtToHex(m_nodep) + ' ' + m_nodep->prettyTypeName();
    }

public:
    AstNode* nodep() const { return m_nodep; }
};

class SplitImpureVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitImpureVertex, SplitNodeVertex)

    std::string name() const override { return "*IMPURE*"; }
    std::string dotColor() const override { return "green"; }

public:
    explicit SplitImpureVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex{graphp, nodep} {}
};

class SplitStmtVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitStmtVertex, SplitNodeVertex)

    std::string dotColor() const override { return "yellow"; }

public:
    SplitStmtVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex{graphp, nodep} {}
};

class SplitVarStdVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitVarStdVertex, SplitNodeVertex)

    std::string dotColor() const override { return "skyblue"; }

public:
    SplitVarStdVertex(V3Graph* graphp, AstVarScope* vscp)
        : SplitNodeVertex{graphp, vscp} {}
};

class SplitVarPostVertex final : public SplitNodeVertex {
    VL_RTTI_IMPL(SplitVarPostVertex, SplitNodeVertex)

    std::string name() const override { return "POST "s + SplitNodeVertex::name(); }
    std::string dotColor() const override { return "CadetBlue"; }

public:
    SplitVarPostVertex(V3Graph* graphp, AstVarScope* vscp)
        : SplitNodeVertex{graphp, vscp} {}
};

class SplitVisitor final : public VNVisitor {
    // NODE STATE - Only under AstAlways
    // AstVarScope::user1p  -> SplitVarStdVertex*: Regular program-flow variable vertex
    // AstVarScope::user2p  -> SplitVarPostVertex*: NBA written delayed variable vertex
    // Ast{StmtIsh}::user1p -> SplitStmtVertex*

    // NODE STATE
    // AstAlways::user3     -> bool: Block created by splitting, needs no further splitting
    const VNUser3InUse m_inuser3;

    // STATE
    V3Graph* m_graphp = nullptr;  // Dependency graph to analyze statement connectivity
    std::vector<SplitStmtVertex*> m_stmtStackps;  // Current statements being tracked
    SplitImpureVertex* m_impureVtxp = nullptr;  // Vertex connecting impure statements
    const char* m_noSplitWhy = nullptr;  // Reason current block cannot be split
    bool m_inDly = false;  // Inside AstAssignDly Lhs
    const AstIf* m_currIfp = nullptr;  // The AstIf whose condition is currently visited
    VDouble0 m_statSplits;  // Statistic tracking

    // METHODS
    void addEdge(V3GraphVertex* fromp, V3GraphVertex* top) {
        new V3GraphEdge{m_graphp, fromp, top, 1};
    }

    // Iterate the given list of statements, building the dependency graph
    void scanBlock(AstNode* stmtsp) {
        if (m_noSplitWhy) return;
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            // Skip comments. They have no dependencies at all, so would always
            // form an independent component, and hence a split block, of their
            // own, which would be subsequently deleted as it does nothing.
            if (VN_IS(stmtp, Comment)) continue;
            UASSERT_OBJ(!stmtp->user1p(), stmtp, "user1p should not be set");
            SplitStmtVertex* const vtxp = new SplitStmtVertex{m_graphp, stmtp};
            stmtp->user1p(vtxp);
            m_stmtStackps.push_back(vtxp);
            iterate(stmtp);
            m_stmtStackps.pop_back();
        }
    }

    // Remove unnecessary edges, then color to find weakly connected components
    uint32_t colorAlwaysGraph() {
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_built", false);

        // Prune duplicate edges. Not necessary for correctness, but simplifies dumps.
        m_graphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_nodup", false);

        // Remove variable vertices that are not written in the block.
        // These are input-only to the block, so carry no dependency.
        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            SplitVarStdVertex* const vstdp = vtxp->cast<SplitVarStdVertex>();
            if (!vstdp || !vstdp->outEmpty()) continue;
            UINFOTREE(9, vstdp->nodep(), "", "Will remove deps on block input var:");
            vstdp->nodep()->user1p(nullptr);  // Don't leave a dangling pointer behind
            VL_DO_DANGLING(vstdp->unlinkDelete(m_graphp), vstdp);
        }
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_noinputs", false);

        // A statement under an 'if' also has an edge to the 'if' itself, from
        // each variable it writes, so an 'if' holds its whole body together.
        // An 'if' has out edges only for what its own condition reads. If
        // after the pruning of block inputs above, an 'if' has no remaining
        // out edges (dependencies of its condition), then it constrains
        // nothing. If so, then remove the 'if' statement vertex, so
        // its contents can split apart, each part taking a copy of the
        // condition.  This is what allows splitting within an if/else at all,
        // and is what breaks up the reset tree in the example at the top of
        // this file.
        for (V3GraphVertex* const vtxp : m_graphp->vertices().unlinkable()) {
            SplitStmtVertex* const stmtVtxp = vtxp->cast<SplitStmtVertex>();
            if (!stmtVtxp || !VN_IS(stmtVtxp->nodep(), If)) continue;
            // Can't remove if dependent on a variable written in the block
            if (!stmtVtxp->outEmpty()) continue;
            // Depends only on block inputs, so can be split. Remove the vertex.
            stmtVtxp->nodep()->user1p(nullptr);
            stmtVtxp->unlinkDelete(m_graphp);
        }
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_nofreeifs", false);

        // Weak coloring to determine what must stay together in a single block
        const uint32_t numColors = m_graphp->weaklyConnected(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 9) m_graphp->dumpDotFilePrefixed("splitg_colored", false);
        return numColors;
    }

    // Take the statements of the given list, and return them distributed into one list per color.
    static std::vector<AstNode*> splitStatements(AstNode* stmtsp, uint32_t numColors) {
        std::vector<AstNode*> result{numColors, nullptr};
        for (AstNode *stmtp = stmtsp, *nextp = nullptr; stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();  // 'stmtp' is unlinked below

            // Comments are dropped if the block is split
            if (VN_IS(stmtp, Comment)) continue;

            // Pick up the statement vertex, which might be nullptr after pruning during analysis
            const SplitStmtVertex* const vtxp = stmtp->user1u().to<SplitStmtVertex*>();

            // If statements are duplicated for each split branch
            if (AstIf* const ifp = VN_CAST(stmtp, If)) {
                const auto thens = splitStatements(ifp->thensp(), numColors);
                const auto elses = splitStatements(ifp->elsesp(), numColors);
                FileLine* const flp = ifp->fileline();
                // Rebuild the 'if' for each color present in either branch
                bool empty = true;
                for (uint32_t color = 0; color < numColors; ++color) {
                    if (!thens[color] && !elses[color]) continue;
                    empty = false;
                    // The condition is cloned for each color. An impure condition
                    // keeps the 'if' and all it holds in one component, so just once.
                    AstIf* const clonep = new AstIf{flp, ifp->condp()->cloneTree(true),
                                                    thens[color], elses[color]};
                    // Preserve pragmas from unique if's so assertions work properly
                    clonep->uniquePragma(ifp->uniquePragma());
                    clonep->unique0Pragma(ifp->unique0Pragma());
                    clonep->priorityPragma(ifp->priorityPragma());
                    result[color] = AstNode::addNext(result[color], clonep);
                }
                // There is nothing under the 'if' to guard. If its vertex was
                // removed as having no dependencies at all, then its
                // condition reads only block inputs and is pure, so the whole
                // 'if' can go. Otherwise the condition might have a side
                // effect, so keep just the condition, evaluated as a
                // statement, under the color of the 'if' itself.
                if (empty && vtxp) {
                    const uint32_t color = vtxp->color();
                    AstNodeExpr* const condp = ifp->condp();
                    condp->unlinkFrBack();
                    result[color] = AstNode::addNext(result[color], new AstStmtExpr{flp, condp});
                }
                continue;
            }

            // Move the leaf into its color's list
            const uint32_t color = vtxp->color();
            result[color] = AstNode::addNext(result[color], stmtp->unlinkFrBack());
        }
        return result;
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        // Skip blocks created below
        if (nodep->user3()) return;

        UASSERT_OBJ(!m_graphp, nodep, "AstAlways should not nest");
        VL_RESTORER(m_graphp);
        VL_RESTORER(m_impureVtxp);
        VL_RESTORER(m_noSplitWhy);
        VL_RESTORER(m_inDly);
        V3Graph graph;
        m_graphp = &graph;
        m_impureVtxp = nullptr;
        m_noSplitWhy = nullptr;
        m_inDly = false;
        UASSERT_OBJ(m_stmtStackps.empty(), nodep, "Statement stack not empty");

        // Build the graph
        const VNUser1InUse user1InUse;
        const VNUser2InUse user2InUse;
        scanBlock(nodep->stmtsp());

        // We might have to give up
        if (m_noSplitWhy) {
            UINFO(9, "  NoSplitBlock because " << m_noSplitWhy);
            return;
        }

        // Color the graph to identify separable statements
        const uint32_t numColors = colorAlwaysGraph();
        // If the whole block is one component (or empty), then nothing to split
        if (numColors <= 1) return;

        UINFO(6, "  splitting always " << nodep);

        // Count the number of new blocks inserted into the Ast: '1 -> n' split, so 'n - 1' extra
        m_statSplits += numColors - 1;

        // Unpick the statements out of the original block, into one list per color
        const auto lists = splitStatements(nodep->stmtsp(), numColors);
        UASSERT_OBJ(lists.size() == numColors, nodep, "Inconsistent split");

        // Whatever 'splitStatements' did not take, (comments, empty ifs) is not needed any more
        if (AstNode* const restp = nodep->stmtsp()) {
            VL_DO_DANGLING(restp->unlinkFrBackWithNext()->deleteTree(), restp);
        }

        // Every color has a statement in it. Reuse the original block for the
        // first color, and add a new block after it for each of the rest.
        UASSERT_OBJ(lists.front(), nodep, "Color with no statements");
        nodep->addStmtsp(lists.front());
        AstNode* lastp = nodep;
        FileLine* const flp = nodep->fileline();
        const VAlwaysKwd kwd = nodep->keyword();
        for (size_t i = 1; i < numColors; ++i) {
            AstNode* const stmtsp = lists[i];
            UASSERT_OBJ(stmtsp, nodep, "Color with no statements");
            AstAlways* const newp = new AstAlways{flp, kwd, nullptr, stmtsp};
            newp->user3(1);  // Do not split again
            lastp->addNextHere(newp);
            lastp = newp;
        }
    }

    void visit(AstIf* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        {
            VL_RESTORER(m_currIfp);
            m_currIfp = nodep;
            iterateAndNextNull(nodep->condp());
        }
        scanBlock(nodep->thensp());
        scanBlock(nodep->elsesp());
    }

    void visit(AstExprStmt* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        VL_RESTORER(m_inDly);
        m_inDly = false;
        iterateChildren(nodep);
    }

    void visit(AstAssignDly* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        iterate(nodep->rhsp());
        VL_RESTORER(m_inDly);
        m_inDly = true;
        iterate(nodep->lhsp());
    }

    void visit(AstJumpGo*) override {
        if (!m_graphp || m_noSplitWhy) return;
        m_noSplitWhy = "JumpGo";
    }

    void visit(AstVarRef* nodep) override {
        if (!m_graphp || m_noSplitWhy) return;
        UASSERT_OBJ(!m_stmtStackps.empty(), nodep, "Not under a statement");

        // Constant lookups can be ignored
        if (nodep->varp()->isConst()) return;

        AstVarScope* const vscp = nodep->varScopep();

        // SPEEDUP: We add duplicate edges, that should be fixed
        if (m_inDly && nodep->access().isWriteOrRW()) {
            // Delayed variable: is different from non-delayed variable, writes to it
            // are not observable while executing this block (NBA not yet committed),
            // so add only a write edge to a separate 'post' vertex.
            if (!vscp->user2p()) vscp->user2p(new SplitVarPostVertex{m_graphp, vscp});
            SplitVarPostVertex* const vpostp = vscp->user2u().to<SplitVarPostVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vpostp, vtxp);
        } else if (nodep->access().isWriteOrRW()) {
            // Regular (non-blocking) write: Need to maintain program-flow order
            if (!vscp->user1p()) vscp->user1p(new SplitVarStdVertex{m_graphp, vscp});
            SplitVarStdVertex* const vstdp = vscp->user1u().to<SplitVarStdVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vstdp, vtxp);
        } else {
            // Regular (non-blocking) read: Need to maintain program-flow order
            if (!vscp->user1p()) vscp->user1p(new SplitVarStdVertex{m_graphp, vscp});
            SplitVarStdVertex* const vstdp = vscp->user1u().to<SplitVarStdVertex*>();
            for (SplitStmtVertex* const vtxp : m_stmtStackps) {
                // If this is an if statement it only depends on refs in its
                // own condition only (not those in its branches). For other
                // statements, just record the referene as normal.
                if (const AstIf* const ifp = VN_CAST(vtxp->nodep(), If)) {
                    if (ifp != m_currIfp) continue;
                }
                addEdge(vtxp, vstdp);
            }
        }
    }

    void visit(AstNode* nodep) override {
        // Outside AstAlways, just descend
        if (!m_graphp) {
            iterateChildren(nodep);
            return;
        }
        // Early exit if decided not to split
        if (m_noSplitWhy) return;

        UASSERT_OBJ(!m_stmtStackps.empty(), nodep, "Not under a statement");

        // Timing control prevents splitting
        if (nodep->isTimingControl()) {
            m_noSplitWhy = "TimingControl";
            return;
        }

        // All impure statements must be grouped together.
        if (!nodep->isPure()) {
            if (!m_impureVtxp) m_impureVtxp = new SplitImpureVertex{m_graphp, nodep};
            // One edge is enough to find the weakly connected components, but
            // it must point at the impure vertex, so it is an out edge (input
            // dependency) of any enclosing 'if' to prevent pruning.
            for (SplitStmtVertex* const vtxp : m_stmtStackps) addEdge(vtxp, m_impureVtxp);
        }

        iterateChildren(nodep);
    }

    // CONSTRUCTORS
    explicit SplitVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SplitVisitor() override { V3Stats::addStat("Optimizations, Split always", m_statSplits); }
    VL_UNCOPYABLE(SplitVisitor);

public:
    static void apply(AstNetlist* nodep) { SplitVisitor{nodep}; }
};

//######################################################################
// Split class functions

void V3Split::splitAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    SplitVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("split", 0, dumpTreeEitherLevel() >= 3);
}
