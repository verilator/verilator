// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Code scheduling
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
//
// Prepares the TimingKit used by V3Sched.cpp to integrate static scheduling
// with timing features. Creates the actives resuming the timing schedulers,
// and computes the variables written by suspendable processes, together with
// their external domains: the sentrees the writing processes can resume on.
// These are computed over the call graph of the code executed by suspendable
// processes, including the processes started by forks, condensed into its
// strongly connected components.
//
// See the internals documentation docs/internals.rst for more details.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Ast.h"
#include "V3ClassGraph.h"
#include "V3Graph.h"
#include "V3Sched.h"
#include "V3Stats.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

//============================================================================
// Creates the actives resuming the timing schedulers

class ResumeActiveBuilder final {
    // NODE STATE
    //  AstSenTree::user1()  -> bool.  Set true if the sentree has been visited.
    const VNUser1InUse m_inuser1;

    // STATE
    AstScope* const m_scopeTopp;  // Scope at the top
    LogicByScope m_lbs;  // Timing resume actives
    AstNodeStmt* m_postUpdatesp = nullptr;  // Post updates for the trigger eval function

    // METHODS
    // Create an active with a timing scheduler resume() call
    void createResumeActive(AstCAwait* const awaitp) {
        AstCMethodHard* const methodp = VN_AS(awaitp->exprp(), CMethodHard);
        AstVarScope* const schedp = VN_AS(methodp->fromp(), VarRef)->varScopep();
        AstSenTree* const sentreep = awaitp->sentreep();
        FileLine* const flp = sentreep->fileline();
        // Create a resume() call on the timing scheduler
        AstNodeExpr* const schedRefp = new AstVarRef{flp, schedp, VAccess::READWRITE};
        AstCMethodHard* const resumep = new AstCMethodHard{flp, schedRefp, VCMethod::SCHED_RESUME};
        resumep->dtypeSetVoid();
        AstBasicDType* const basicp = schedp->dtypep()->basicp();
        if (basicp->isTriggerScheduler()) {
            // Pass on the event description, the third argument of trigger(), see V3Timing
            AstNode* const descp = methodp->pinsp()->nextp()->nextp();
            resumep->addPinsp(VN_AS(descp, NodeExpr)->cloneTree(false));
        } else if (basicp->isDynamicTriggerScheduler()) {
            AstCMethodHard* const postp = resumep->cloneTree(false);
            postp->method(VCMethod::SCHED_DO_POST_UPDATES);
            UASSERT_OBJ(!m_postUpdatesp, awaitp, "Multiple dynamic trigger schedulers");
            m_postUpdatesp = postp->makeStmt();
        }
        // Put it in an active
        AstActive* const activep = new AstActive{flp, "_timing", sentreep};
        activep->addStmtsp(resumep->makeStmt());
        m_lbs.add(m_scopeTopp, activep);
    }

    // CONSTRUCTORS
    explicit ResumeActiveBuilder(AstNetlist* netlistp)
        : m_scopeTopp{netlistp->topScopep()->scopep()} {
        netlistp->foreach([&](AstCAwait* awaitp) {
            AstSenTree* const sentreep = awaitp->sentreep();
            if (sentreep && !sentreep->user1SetOnce()) createResumeActive(awaitp);
        });
    }

public:
    // Returns the resume actives and the post updates for the trigger eval function
    static std::pair<LogicByScope, AstNodeStmt*> apply(AstNetlist* netlistp) {
        ResumeActiveBuilder builder{netlistp};
        return {std::move(builder.m_lbs), builder.m_postUpdatesp};
    }
};

//============================================================================
// Computes the variables written by suspendables, and their external domains

class ExternalDomainsVisitor final : public VNVisitorConst {
    // TYPES
    // Vertex of what is approximately a call graph. Each vertex represents either a:
    // - suspendable process
    // - coroutine, or function called by suspendable code
    // - fork
    class Vertex final : public V3GraphVertex {
        VL_RTTI_IMPL(Vertex, V3GraphVertex)
    public:
        std::set<AstSenTree*> m_domains;  // Sentrees waited on
        std::set<AstVarScope*> m_writes;  // Variables written
        explicit Vertex(V3Graph* graphp)
            : V3GraphVertex{graphp} {}
    };

    // NODE STATE
    //  AstCFunc::user1()          -> Vertex*.  Vertex, if coroutine or called by suspendable code
    //  AstFork::user1()           -> Vertex*.  Vertex
    //  AstNodeProcedure::user1()  -> Vertex*.  Vertex, if suspendable
    const VNUser1InUse m_inuser1;

    // STATE
    // Class graph to get possibly called functions from a virtual call
    std::unique_ptr<V3ClassGraph> m_classGraphp;
    V3Graph m_graph;  // The call graph used for analysis
    Vertex* m_vtxp = nullptr;  // Vertex of the current body, if suspendable code
    std::vector<AstCFunc*> m_funcps;  // Functions not yet recorded when visited
    // External domains of the variables written by suspendables
    std::map<const AstVarScope*, std::set<AstSenTree*>> m_externalDomains;

    // METHODS
    // Get the call graph vertex of the given function, process or fork. If it is new,
    // walk the body with it to record its contents and callees.
    Vertex* recordBody(AstNode* nodep) {
        if (!nodep->user1p()) {
            Vertex* const vtxp = new Vertex{&m_graph};
            nodep->user1p(vtxp);
            VL_RESTORER(m_vtxp);
            m_vtxp = vtxp;
            iterateChildrenConst(nodep);
        }
        return nodep->user1u().to<Vertex*>();
    }

    // Add an edge from m_vtxp (current body) to the given vertex
    void addEdge(Vertex* const vtxp) { new V3GraphEdge{&m_graph, m_vtxp, vtxp, 1}; }

    // Contract each strongly connected component of the call graph (direct or mutual recursion,
    // including through forks) into a single vertex. This effectively treats the whole SCC as a
    // single body of code.
    void contractSCCs() {
        m_graph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);
        m_graph.stronglyConnected(&V3GraphEdge::followAlwaysTrue);
        std::unordered_map<uint32_t, Vertex*> colorToVtxp;
        for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
            // Zero color means the vertex is in no cycle, so it is a component on its own
            if (!vtxp->color()) continue;

            // The first vertex is the one all others of the same SCC are merged into
            Vertex*& keepp = colorToVtxp[vtxp->color()];
            if (!keepp) {
                keepp = vtxp->as<Vertex>();
                continue;
            }

            // Merge the other vertices into the first one
            Vertex* const mergep = vtxp->as<Vertex>();
            keepp->m_domains.insert(mergep->m_domains.begin(), mergep->m_domains.end());
            keepp->m_writes.insert(mergep->m_writes.begin(), mergep->m_writes.end());
            for (V3GraphEdge* const ep : mergep->outEdges().unlinkable()) ep->relinkFromp(keepp);
            for (V3GraphEdge* const ep : mergep->inEdges().unlinkable()) ep->relinkTop(keepp);
            VL_DO_DANGLING(mergep->unlinkDelete(&m_graph), mergep);
        }
        // Edges within a component are now self loops on its vertex, remove them
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            for (V3GraphEdge* const edgep : vtx.outEdges().unlinkable()) {
                if (edgep->top() == &vtx) VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            }
        }
    }

    void computeExternalDomains() {
        // Two passes over the graph to propagate the domains up and down, this ensures
        // a sensitivity anywhere in the call graph reaches all relevant variables. This
        // over-approximates: only the awaits that can precede a write ("reaching awaits")
        // are needed for correctness.

        // Propagate the domains up the graph
        for (const V3GraphVertex& vtx : vlstd::reverse_view(m_graph.vertices())) {
            const std::set<AstSenTree*>& domains = vtx.as<Vertex>()->m_domains;
            for (const V3GraphEdge& edge : vtx.inEdges()) {
                Vertex* const callerp = edge.fromp()->as<Vertex>();
                callerp->m_domains.insert(domains.begin(), domains.end());
            }
        }
        // Propagate the domains down the graph
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            const std::set<AstSenTree*>& domains = vtx.as<Vertex>()->m_domains;
            for (V3GraphEdge& edge : vtx.outEdges()) {
                Vertex* const calleep = edge.top()->as<Vertex>();
                calleep->m_domains.insert(domains.begin(), domains.end());
            }
        }

        // Mark variables written by suspendables, and compute their external domains
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            const Vertex* const vtxp = vtx.as<Vertex>();
            for (AstVarScope* const vscp : vtxp->m_writes) {
                m_externalDomains[vscp].insert(vtxp->m_domains.begin(), vtxp->m_domains.end());
                vscp->varp()->setWrittenBySuspendable();
            }
        }

        if (v3Global.opt.stats()) {
            size_t nDomains = 0;
            std::set<const AstSenTree*> sentreeps;
            for (const auto& vscpDomains : m_externalDomains) {
                nDomains += vscpDomains.second.size();
                sentreeps.insert(vscpDomains.second.begin(), vscpDomains.second.end());
            }
            V3Stats::addStat("Scheduling, Timing, variables written by suspendables",
                             m_externalDomains.size());
            V3Stats::addStat("Scheduling, Timing, external sensitivities, total", nDomains);
            V3Stats::addStat("Scheduling, Timing, unique external sentrees", sentreeps.size());
        }
    }

    // VISITORS
    void visit(AstNodeProcedure* const nodep) override {
        UASSERT_OBJ(!m_vtxp, nodep, "Should not nest");
        // If the process is suspendable, record its body
        if (nodep->isSuspendable()) {
            recordBody(nodep);
            return;
        }
        // A non-suspendable process is walked only to find its forks
        iterateChildrenConst(nodep);
    }
    void visit(AstCFunc* const nodep) override {
        UASSERT_OBJ(!m_vtxp, nodep, "Should not nest");
        // A coroutine is suspendable, so record its body
        if (nodep->isCoroutine()) {
            recordBody(nodep);
            return;
        }
        // Gather regular functions not yet recorded during the walk,
        // they will be analyzed at the end to minimize repeated traversals
        if (!nodep->user1p()) m_funcps.push_back(nodep);
    }
    void visit(AstFork* nodep) override {
        // Fork branches are always suspendable, so record their body
        Vertex* const vtxp = recordBody(nodep);
        // Add edge if started from suspendable code
        if (m_vtxp) addEdge(vtxp);
    }
    void visit(AstCAwait* nodep) override {
        UASSERT_OBJ(m_vtxp, nodep, "Await not in suspendable code");
        // Record the domain
        if (AstSenTree* const senTreep = nodep->sentreep()) m_vtxp->m_domains.insert(senTreep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* const nodep) override {
        iterateChildrenConst(nodep);
        if (!m_vtxp) return;  // Not in suspendable code
        // Add edges to all functions that may be called, including through virtual calls
        const std::unordered_set<AstCFunc*>& cfuncps = m_classGraphp->getCallPossibleCFuncs(nodep);
        if (cfuncps.empty()) {
            addEdge(recordBody(nodep->funcp()));
        } else {
            for (AstCFunc* const cfuncp : cfuncps) addEdge(recordBody(cfuncp));
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        if (!m_vtxp) return;  // Not in suspendable code, or outside processes/functions
        if (nodep->access().isWriteOrRW() && !nodep->varp()->ignoreSchedWrite()) {
            m_vtxp->m_writes.insert(nodep->varScopep());
        }
    }
    void visit(AstConst*) override {}  // Accelerate
    void visit(AstVar*) override {}  // Accelerate
    void visit(AstVarScope*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit ExternalDomainsVisitor(AstNetlist* nodep)
        : m_classGraphp{V3ClassGraph::build(nodep)} {
        // Record the bodies of suspendable processes, coroutines, and forks
        iterateConst(nodep);
        // Regular functions not called by any of the above are walked only to find their forks
        for (AstCFunc* const funcp : m_funcps) {
            if (!funcp->user1p()) iterateChildrenConst(funcp);
        }
        // Contract each strongly connected component into a single vertex
        contractSCCs();
        // Topological order, callers first
        m_graph.order();
        // Propagate the domains up and down the graph to compute external sensitivities
        computeExternalDomains();
    }

public:
    // Returns the external domains of variables written by suspendables
    static std::map<const AstVarScope*, std::set<AstSenTree*>> apply(AstNetlist* nodep) {
        ExternalDomainsVisitor visitor{nodep};
        return std::move(visitor.m_externalDomains);
    }
};

TimingKit prepareTiming(AstNetlist* const netlistp) {
    if (!v3Global.usesTiming()) return {};
    std::pair<LogicByScope, AstNodeStmt*> resumes = ResumeActiveBuilder::apply(netlistp);
    std::map<const AstVarScope*, std::set<AstSenTree*>> externalDomains
        = ExternalDomainsVisitor::apply(netlistp);
    return {std::move(resumes.first), resumes.second, std::move(externalDomains)};
}

}  // namespace V3Sched
