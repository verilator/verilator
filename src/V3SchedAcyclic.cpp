// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling - break combinational cycles
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
//
// Combinational loops are broken by the introduction of instances of the
// 'hybrid' logic. Hybrid logic is like combinational logic, but also has
// explicit sensitivities. Any explicit sensitivity of hybrid logic suppresses
// the implicit sensitivity of the logic on the same variable. This enables us
// to cut combinational logic loops and perform ordering as if the logic is
// acyclic.  See the internals documentation for more details.
//
// To achieve this we build a dependency graph of all combinational logic in
// the design, and then breaks all combinational cycles by converting all
// combinational logic that consumes a variable driven via a 'back-edge' into
// hybrid logic. Here back-edge' just means a graph edge that points from a
// higher rank vertex to a lower rank vertex in some consistent ranking of
// the directed graph. Variables driven via a back-edge in the dependency
// graph are marked, and all combinational logic that depends on such
// variables is converted into hybrid logic, with the back-edge driven
// variables listed as explicit 'changed' sensitivities.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Graph.h"
#include "V3Sched.h"
#include "V3SenTree.h"
#include "V3SplitVar.h"
#include "V3Stats.h"

#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

// ##############################################################################
//  Data structures (graph types)

class SchedAcyclicLogicVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SchedAcyclicLogicVertex, V3GraphVertex)
    AstNode* const m_logicp;  // The logic node this vertex represents
    AstScope* const m_scopep;  // The enclosing AstScope of the logic node

public:
    SchedAcyclicLogicVertex(V3Graph* graphp, AstNode* logicp, AstScope* scopep)
        : V3GraphVertex{graphp}
        , m_logicp{logicp}
        , m_scopep{scopep} {}
    V3GraphVertex* clone(V3Graph* graphp) const override {
        return new SchedAcyclicLogicVertex{graphp, logicp(), scopep()};
    }

    AstNode* logicp() const { return m_logicp; }
    AstScope* scopep() const { return m_scopep; }

    // LCOV_EXCL_START // Debug code
    string name() const override VL_MT_STABLE { return m_logicp->fileline()->ascii(); };
    string dotShape() const override { return "rectangle2"; }
    // LCOV_EXCL_STOP
};

class SchedAcyclicVarVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SchedAcyclicVarVertex, V3GraphVertex)
    AstVarScope* const m_vscp;  // The AstVarScope this vertex represents

public:
    SchedAcyclicVarVertex(V3Graph* graphp, AstVarScope* vscp)
        : V3GraphVertex{graphp}
        , m_vscp{vscp} {}
    AstVarScope* vscp() const { return m_vscp; }
    AstVar* varp() const { return m_vscp->varp(); }
    V3GraphVertex* clone(V3Graph* graphp) const override {
        return new SchedAcyclicVarVertex{graphp, vscp()};
    }

    // LCOV_EXCL_START // Debug code
    string name() const override VL_MT_STABLE { return m_vscp->name(); }
    string dotShape() const override { return "ellipse"; }
    string dotColor() const override { return "blue"; }
    // LCOV_EXCL_STOP
};

class Graph final : public V3Graph {
    void loopsVertexCb(V3GraphVertex* vtxp) override {
        // TODO: 'typeName' is an internal thing. This should be more human readable.
        if (SchedAcyclicLogicVertex* const lvtxp = vtxp->cast<SchedAcyclicLogicVertex>()) {
            AstNode* const logicp = lvtxp->logicp();
            std::cerr << logicp->fileline()->warnOtherStandalone()
                      << "     Example path: " << logicp->typeName() << endl;
        } else {
            SchedAcyclicVarVertex* const vvtxp = vtxp->as<SchedAcyclicVarVertex>();
            AstVarScope* const vscp = vvtxp->vscp();
            std::cerr << vscp->fileline()->warnOtherStandalone()
                      << "     Example path: " << vscp->prettyName() << endl;
        }
    }
};

//##############################################################################
// Algorithm implementation

std::unique_ptr<Graph> buildGraph(const LogicByScope& lbs) {
    std::unique_ptr<Graph> graphp{new Graph};

    // AstVarScope::user1() -> VarVertx
    const VNUser1InUse user1InUse;
    const auto getVarVertex = [&](AstVarScope* vscp) {
        if (!vscp->user1p()) vscp->user1p(new SchedAcyclicVarVertex{graphp.get(), vscp});
        return vscp->user1u().to<SchedAcyclicVarVertex*>();
    };

    const auto addEdge = [&](V3GraphVertex* fromp, V3GraphVertex* top, int weight, bool cuttable) {
        new V3GraphEdge{graphp.get(), fromp, top, weight, cuttable};
    };

    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        UASSERT_OBJ(activep->hasCombo(), activep, "Not combinational logic");
        for (AstNode* nodep = activep->stmtsp(); nodep; nodep = nodep->nextp()) {
            // Can safely ignore Postponed as we generate them all
            if (VN_IS(nodep, AlwaysPostponed)) continue;

            SchedAcyclicLogicVertex* const lvtxp
                = new SchedAcyclicLogicVertex{graphp.get(), nodep, scopep};
            const VNUser2InUse user2InUse;
            const VNUser3InUse user3InUse;

            nodep->foreach([&](AstVarRef* refp) {
                AstVarScope* const vscp = refp->varScopep();
                SchedAcyclicVarVertex* const vvtxp = getVarVertex(vscp);
                // We want to cut the narrowest signals
                const int weight = vscp->width() / 8 + 1;
                // If written, add logic -> var edge
                if (refp->access().isWriteOrRW() && !vscp->user2SetOnce())
                    addEdge(lvtxp, vvtxp, weight, true);
                // If read, add var -> logic edge
                // Note: Use same heuristic as ordering does to ignore written variables
                // TODO: Use live variable analysis.
                if (refp->access().isReadOrRW() && !vscp->user3SetOnce() && !vscp->user2())
                    addEdge(vvtxp, lvtxp, weight, true);
            });
        }
    }

    return graphp;
}

void removeNonCyclic(Graph* graphp) {
    // Work queue
    std::vector<V3GraphVertex*> queue;

    const auto enqueue = [&](V3GraphVertex* vtxp) {
        if (vtxp->user()) return;  // Already in queue
        vtxp->user(1);
        queue.push_back(vtxp);
    };

    // Start with vertices with no inputs or outputs
    for (V3GraphVertex* vtxp = graphp->verticesBeginp(); vtxp; vtxp = vtxp->verticesNextp()) {
        if (vtxp->inEmpty() || vtxp->outEmpty()) enqueue(vtxp);
    }

    // Iterate while we still have candidates
    while (!queue.empty()) {
        // Pop next candidate
        V3GraphVertex* const vtxp = queue.back();
        queue.pop_back();
        vtxp->user(0);  // No longer in queue

        if (vtxp->inEmpty()) {
            // Enqueue children for consideration, remove out edges, and delete this vertex
            for (V3GraphEdge *edgep = vtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
                nextp = edgep->outNextp();
                enqueue(edgep->top());
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            }
            VL_DO_DANGLING(vtxp->unlinkDelete(graphp), vtxp);
        } else if (vtxp->outEmpty()) {
            // Enqueue parents for consideration, remove in edges, and delete this vertex
            for (V3GraphEdge *edgep = vtxp->inBeginp(), *nextp; edgep; edgep = nextp) {
                nextp = edgep->inNextp();
                enqueue(edgep->fromp());
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            }
            VL_DO_DANGLING(vtxp->unlinkDelete(graphp), vtxp);
        }
    }
}

// Has this VarVertex been cut? (any edges in or out has been cut)
bool isCut(const SchedAcyclicVarVertex* vtxp) {
    for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        if (edgep->weight() == 0) return true;
    }
    for (V3GraphEdge* edgep = vtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
        if (edgep->weight() == 0) return true;
    }
    return false;
}

std::vector<SchedAcyclicVarVertex*> findCutVertices(Graph* graphp) {
    std::vector<SchedAcyclicVarVertex*> result;
    const VNUser1InUse user1InUse;  // bool: already added to result
    for (V3GraphVertex* vtxp = graphp->verticesBeginp(); vtxp; vtxp = vtxp->verticesNextp()) {
        if (SchedAcyclicVarVertex* const vvtxp = vtxp->cast<SchedAcyclicVarVertex>()) {
            if (!vvtxp->vscp()->user1SetOnce() && isCut(vvtxp)) result.push_back(vvtxp);
        }
    }
    return result;
}

void resetEdgeWeights(const std::vector<SchedAcyclicVarVertex*>& cutVertices) {
    for (SchedAcyclicVarVertex* const vvtxp : cutVertices) {
        for (V3GraphEdge* ep = vvtxp->inBeginp(); ep; ep = ep->inNextp()) ep->weight(1);
        for (V3GraphEdge* ep = vvtxp->outBeginp(); ep; ep = ep->outNextp()) ep->weight(1);
    }
}

// A VarVertex together with its fanout
using Candidate = std::pair<SchedAcyclicVarVertex*, unsigned>;

// Gather all splitting candidates that are in the same SCC as the given vertex
void gatherSCCCandidates(V3GraphVertex* vtxp, std::vector<Candidate>& candidates) {
    if (vtxp->user()) return;  // Already done
    vtxp->user(true);

    if (SchedAcyclicVarVertex* const vvtxp = vtxp->cast<SchedAcyclicVarVertex>()) {
        AstVar* const varp = vvtxp->varp();
        const string name = varp->prettyName();
        if (!varp->user3SetOnce()  // Only consider each AstVar once
            && varp->width() != 1  // Ignore 1-bit signals (they cannot be split further)
            && name.find("__Vdly") == string::npos  // Ignore internal signals
            && name.find("__Vcell") == string::npos) {
            // Also compute the fanout of this vertex
            unsigned fanout = 0;
            for (V3GraphEdge* ep = vtxp->outBeginp(); ep; ep = ep->outNextp()) ++fanout;
            candidates.emplace_back(vvtxp, fanout);
        }
    }

    // Iterate through all the vertices within the same strongly connected component (same color)
    for (V3GraphEdge* edgep = vtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
        V3GraphVertex* const top = edgep->top();
        if (top->color() == vtxp->color()) gatherSCCCandidates(top, candidates);
    }
    for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        V3GraphVertex* const fromp = edgep->fromp();
        if (fromp->color() == vtxp->color()) gatherSCCCandidates(fromp, candidates);
    }
}

// Find all variables in a loop (SCC) that are candidates for splitting to break loops.
void reportLoopVars(Graph* graphp, SchedAcyclicVarVertex* vvtxp) {
    // Vector of variables in UNOPTFLAT loop that are candidates for splitting.
    std::vector<Candidate> candidates;
    {
        // AstNode::user3 is used to mark if we have done a particular variable.
        // V3GraphVertex::user is used to mark if we have seen this vertex before.
        const VNUser3InUse user3InUse;
        graphp->userClearVertices();
        gatherSCCCandidates(vvtxp, candidates);
        graphp->userClearVertices();
    }

    // Possible we only have candidates the user cannot do anything about, so don't bother them.
    if (candidates.empty()) return;

    // There may be a very large number of candidates, so only report up to 10 of the "most
    // important" signals.
    unsigned splittable = 0;
    const auto reportFirst10 = [&](std::function<bool(const Candidate&, const Candidate&)> less) {
        std::stable_sort(candidates.begin(), candidates.end(), less);
        for (size_t i = 0; i < 10; i++) {
            if (i == candidates.size()) break;
            const Candidate& candidate = candidates[i];
            AstVar* const varp = candidate.first->varp();
            std::cerr << V3Error::warnMoreStandalone() << "    " << varp->fileline() << " "
                      << varp->prettyName() << ", width " << std::dec << varp->width()
                      << ", circular fanout " << candidate.second;
            if (V3SplitVar::canSplitVar(varp)) {
                std::cerr << ", can split_var";
                ++splittable;
            }
            std::cerr << '\n';
        }
    };

    // Widest variables
    std::cerr << V3Error::warnMoreStandalone() << "... Widest variables candidate to splitting:\n";
    reportFirst10([](const Candidate& a, const Candidate& b) {
        return a.first->varp()->width() > b.first->varp()->width();
    });

    // Highest fanout
    std::cerr << V3Error::warnMoreStandalone() << "... Candidates with the highest fanout:\n";
    reportFirst10([](const Candidate& a, const Candidate& b) {  //
        return a.second > b.second;
    });

    if (splittable) {
        std::cerr << V3Error::warnMoreStandalone()
                  << "... Suggest add /*verilator split_var*/ to appropriate variables above."
                  << std::endl;
    }
    V3Stats::addStat("Scheduling, split_var, candidates", splittable);
}

void reportCycles(Graph* graphp, const std::vector<SchedAcyclicVarVertex*>& cutVertices) {
    for (SchedAcyclicVarVertex* vvtxp : cutVertices) {
        AstVarScope* const vscp = vvtxp->vscp();
        FileLine* const flp = vscp->fileline();

        // First v3warn not inside warnIsOff so we can see the suppressions with --debug
        vscp->v3warn(UNOPTFLAT, "Signal unoptimizable: Circular combinational logic: "
                                    << vscp->prettyNameQ());
        if (!flp->warnIsOff(V3ErrorCode::UNOPTFLAT) && !flp->lastWarnWaived()) {
            // Complain just once
            flp->modifyWarnOff(V3ErrorCode::UNOPTFLAT, true);
            // Calls Graph::loopsVertexCb
            graphp->reportLoops(&V3GraphEdge::followAlwaysTrue, vvtxp);
            if (v3Global.opt.reportUnoptflat()) {
                // Report candidate variables for splitting
                reportLoopVars(graphp, vvtxp);
                // Create a subgraph for the UNOPTFLAT loop
                V3Graph loopGraph;
                graphp->subtreeLoops(&V3GraphEdge::followAlwaysTrue, vvtxp, &loopGraph);
                loopGraph.dumpDotFilePrefixedAlways("unoptflat");
            }
        }
    }
}

LogicByScope fixCuts(AstNetlist* netlistp,
                     const std::vector<SchedAcyclicVarVertex*>& cutVertices) {
    // For all logic that reads a cut vertex, build a map from logic -> list of cut AstVarScope
    // they read. Also build a vector of the involved logic for deterministic results.
    std::unordered_map<SchedAcyclicLogicVertex*, std::vector<AstVarScope*>> lvtx2Cuts;
    std::vector<SchedAcyclicLogicVertex*> lvtxps;
    {
        const VNUser1InUse user1InUse;  // bool: already added to 'lvtxps'
        for (SchedAcyclicVarVertex* const vvtxp : cutVertices) {
            for (V3GraphEdge* edgep = vvtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                SchedAcyclicLogicVertex* const lvtxp
                    = static_cast<SchedAcyclicLogicVertex*>(edgep->top());
                if (!lvtxp->logicp()->user1SetOnce()) lvtxps.push_back(lvtxp);
                lvtx2Cuts[lvtxp].push_back(vvtxp->vscp());
            }
        }
    }

    // Make the logic reading cut vertices use a hybrid sensitivity (combinational, but with some
    // explicit additional triggers on the cut variables)
    LogicByScope result;
    SenTreeFinder finder{netlistp};
    for (SchedAcyclicLogicVertex* const lvtxp : lvtxps) {
        AstNode* const logicp = lvtxp->logicp();
        logicp->unlinkFrBack();
        FileLine* const flp = logicp->fileline();
        // Build the hybrid sensitivity list
        AstSenItem* senItemsp = nullptr;
        for (AstVarScope* const vscp : lvtx2Cuts[lvtxp]) {
            AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::READ};
            AstSenItem* const nextp = new AstSenItem{flp, VEdgeType::ET_HYBRID, refp};
            senItemsp = AstNode::addNext(senItemsp, nextp);
        }
        AstSenTree* const senTree = new AstSenTree{flp, senItemsp};
        // Add logic to result with new sensitivity
        result.add(lvtxp->scopep(), finder.getSenTree(senTree), logicp);
        // SenTreeFinder::getSenTree clones, so clean up
        VL_DO_DANGLING(senTree->deleteTree(), senTree);
    }
    return result;
}

}  // namespace

LogicByScope breakCycles(AstNetlist* netlistp, const LogicByScope& combinationalLogic) {
    // Build the dataflow (dependency) graph
    const std::unique_ptr<Graph> graphp = buildGraph(combinationalLogic);

    // Remove nodes that don't form part of a cycle
    removeNonCyclic(graphp.get());

    // Nothing to do if no cycles, yay!
    if (graphp->empty()) return LogicByScope{};

    // Dump for debug
    if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("sched-comb-cycles");

    // Make graph acyclic by cutting some edges. Note: This also colors strongly connected
    // components which reportCycles uses to print each SCCs separately.
    // TODO: A more optimal algorithm that cuts by removing/marking VarVertex vertices is possible
    //       Search for "Feedback vertex set" (current algorithm is "Feedback arc set")
    graphp->acyclic(&V3GraphEdge::followAlwaysTrue);

    // Find all cut vertices
    const std::vector<SchedAcyclicVarVertex*> cutVertices = findCutVertices(graphp.get());

    // Reset edge weights for reporting
    resetEdgeWeights(cutVertices);

    // Report warnings/diagnostics
    reportCycles(graphp.get(), cutVertices);

    // Fix cuts by converting dependent logic to use hybrid sensitivities
    return fixCuts(netlistp, cutVertices);
}

}  // namespace V3Sched
