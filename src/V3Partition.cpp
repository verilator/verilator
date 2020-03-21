// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's logic to mtask partitioner
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Os.h"
#include "V3File.h"
#include "V3GraphAlg.h"
#include "V3GraphPathChecker.h"
#include "V3GraphStream.h"
#include "V3InstrCount.h"
#include "V3Partition.h"
#include "V3PartitionGraph.h"
#include "V3Scoreboard.h"
#include "V3Stats.h"

#include <list>
#include <memory>
#include VL_INCLUDE_UNORDERED_SET

class MergeCandidate;

//######################################################################
// Partitioner tunable settings:
//
// Before describing these settings, a bit of background:
//
// Early during the development of the partitioner, V3Split was failing to
// split large always blocks (with ~100K assignments) so we had to handle
// very large vertices with ~100K incoming and outgoing edges.
//
// The partitioner attempts to deal with such densely connected
// graphs. Some of the tuning parameters below reference "huge vertices",
// that's what they're talking about, vertices with tens of thousands of
// edges in and out. Whereas most graphs have only tens of edges in and out
// of most vertices.
//
// V3Split has since been fixed to more reliably split large always
// blocks. It's kind of an open question whether the partitioner must
// handle huge nodes gracefully. Maybe not!  But it still can, given
// appropriate tuning.


//   PART_SIBLING_EDGE_LIMIT (integer)
//
// Arbitrarily limit the number of edges on a single vertex that will be
// considered when enumerating siblings, to the given value.  This protects
// the partitioner runtime in the presence of huge vertices.
//
// The sibling-merge is less important than the edge merge.  (You can
// totally disable the sibling merge and get halfway decent partitions; you
// can't disable edge merges, those are fundamental to the process.) So,
// skipping the enumeration of some siblings on a few vertices does not
// have a large impact on the result of the partitioner.
//
// If your vertices are small, the limit (at 25) approaches a no-op.  Hence
// there's basically no cost to applying this limit even when we don't
// expect huge vertices.
//
// If you don't care about partitioner runtime and you want the most
// aggressive partition, set the limit very high.  If you have huge
// vertices, leave this as is.
#define PART_SIBLING_EDGE_LIMIT 25


//   PART_STEPPED_COST (boolean)
//
// When computing critical path costs, use a step function on the actual
// underlying vertex cost.
//
// If there are huge vertices, when a tiny vertex merges into a huge
// vertex, we can often avoid increasing the huge vertex's stepped cost.
// If the stepped cost hasn't increased, and the critical path into the huge
// vertex hasn't increased, we can avoid propagating a new critical path to
// vertices past the huge vertex. Since huge vertices tend to have huge lists
// of children and parents, this can be a substantial savings.
//
// Does not seem to reduce the quality of the partitioner's output.
//
// If you have huge vertices, leave this 'true', it is the major setting
// that allows the partitioner to handle such difficult graphs on anything
// like a human time scale.
//
// If you don't have huge vertices, the 'true' value doesn't help much but
// should cost almost nothing in terms of partitioner quality.
//
// If you want the most aggressive possible partition, set it "false" and
// be prepared to be disappointed when the improvement in the partition is
// negligible / in the noise.
//
// Q) Why retain the control, if there is really no downside?
//
// A) Cost stepping can lead to corner cases. A developer may wish to
//    disable cost stepping to rule it out as the cause of unexpected
//    behavior.
#define PART_STEPPED_COST true


//   PART_STEPPED_RESCORE_LIMIT (boolean)
//
// If false, we always try to merge the absolute lowest (best) scoring
// mtask pair among all candidates.
//
// If true, we're willing to merge mtask pairs with scores up to 5% higher
// (worse) than the best, in exchange for doing a Rescore() operation
// somewhat less often.
//
// A true setting can result in a much faster compile in the presence of
// huge vertices, eg. 45 minutes versus 4.5 minutes for one particular
// model. HOWEVER, a true setting usually results in modestly worse
// partitions, often around 10% more MTasks and 10% longer cycle times.
//
// (TODO: Why does this setting save time with huge vertices?
// Is there a way to get best of both worlds without the trade off?)
//
// If you have huge vertices, you may wish to set this true.  If you don't
// have huge vertices (which should be everyone, we think, now that V3Split
// is fixed) leave it set false for the most aggressive partition.
#define PART_STEPPED_RESCORE_LIMIT false


// Don't produce more than a certain maximum number of MTasks.  This helps
// the TSP variable sort not to blow up (a concern for some of the tests)
// and we probably don't want a huge number of mtasks in practice anyway
// (50 to 100 is typical.)
//
// If the user doesn't give one with '--threads-max-mtasks', we'll set the
// maximum # of MTasks to
//  (# of threads * PART_DEFAULT_MAX_MTASKS_PER_THREAD)
#define PART_DEFAULT_MAX_MTASKS_PER_THREAD 50

//   end tunables.

//######################################################################
// Misc graph and assertion utilities

static void partCheckCachedScoreVsActual(uint32_t cached, uint32_t actual) {
#if PART_STEPPED_COST
    // Cached CP might be a little bigger than actual, due to stepped CPs.
    // Example:
    // Let's say we have a parent with stepped_cost 40 and a grandparent
    // with stepped_cost 27. Our forward-cp is 67. Then our parent and
    // grandparent get merged, the merged node has stepped cost 66.  We
    // won't propagate that new CP to children as it hasn't grown.  So,
    // children may continue to think that the CP coming through this path
    // is a little higher than it really is; permit that.
    UASSERT((((cached * 10) <= (actual * 11))
             && (cached * 11) >= (actual * 10)),
            "Calculation error in scoring (approximate, may need tweak)");
#else
    UASSERT(cached == actual, "Calculation error in scoring");
#endif
}

//######################################################################
// PartPropagateCp

// Propagate increasing critical path (CP) costs through a graph.
//
// Usage:
//  * Client increases the cost and/or CP at a node or small set of nodes
//    (often a pair in practice, eg. edge contraction.)
//  * Client instances a PartPropagateCp object
//  * Client calls PartPropagateCp::cpHasIncreased() one or more times.
//    Each call indicates that the inclusive CP of some "seed" vertex
//    has increased to a given value.
//    * NOTE: PartPropagateCp will neither read nor modify the cost
//      or CPs at the seed vertices, it only accesses and modifies
//      vertices wayward from the seeds.
//  * Client calls PartPropagateCp::go(). Internally, this iteratively
//    propagates the new CPs wayward through the graph.
//
template <class T_CostAccessor> class PartPropagateCp : GraphAlg<> {
private:
    // MEMBERS
    GraphWay m_way;  // CPs oriented in this direction: either FORWARD
    //               // from graph-start to current node, or REVERSE
    //               // from graph-end to current node.
    T_CostAccessor* m_accessp;  // Access cost and CPs on V3GraphVertex's.
    vluint64_t m_generation;  // Mark each vertex with this number;
    //                        // confirm we only process each vertex once.
    bool m_slowAsserts;  // Enable nontrivial asserts
    typedef SortByValueMap<V3GraphVertex*, uint32_t> PropCpPendSet;
    PropCpPendSet m_pending;  // Pending rescores

public:
    // CONSTRUCTORS
    PartPropagateCp(V3Graph* graphp, GraphWay way, T_CostAccessor* accessp,
                    bool slowAsserts,
                    V3EdgeFuncP edgeFuncp = &V3GraphEdge::followAlwaysTrue)
        : GraphAlg<>(graphp, edgeFuncp)
        , m_way(way)
        , m_accessp(accessp)
        , m_generation(0)
        , m_slowAsserts(slowAsserts) {}

    // METHODS
    void cpHasIncreased(V3GraphVertex* vxp, uint32_t newInclusiveCp) {
        // For *vxp, whose CP-inclusive has just increased to
        // newInclusiveCp, iterate to all wayward nodes, update the edges
        // of each, and add each to m_pending if its overall CP has grown.
        for (V3GraphEdge* edgep = vxp->beginp(m_way);
             edgep; edgep = edgep->nextp(m_way)) {
            if (!m_edgeFuncp(edgep)) continue;
            V3GraphVertex* relativep = edgep->furtherp(m_way);
            m_accessp->notifyEdgeCp(relativep, m_way, vxp, newInclusiveCp);

            if (m_accessp->critPathCost(relativep, m_way) < newInclusiveCp) {
                // relativep's critPathCost() is out of step with its
                // longest !wayward edge. Schedule that to be resolved.
                uint32_t newPendingVal =
                    newInclusiveCp - m_accessp->critPathCost(relativep, m_way);
                if (m_pending.has(relativep)) {
                    if (newPendingVal > m_pending.at(relativep)) {
                        m_pending.set(relativep, newPendingVal);
                    }
                } else {
                    m_pending.set(relativep, newPendingVal);
                }
            }
        }
    }

    void go() {
        // m_pending maps each pending vertex to the amount that it wayward
        // CP will grow.
        //
        // We can iterate over the pending set in reverse order, always
        // choosing the nodes with the largest pending CP-growth.
        //
        // The intuition is: if the original seed node had its CP grow by
        // 50, the most any wayward node can possibly grow is also 50.  So
        // for anything pending to grow by 50, we know we can process it
        // once and we won't have to grow its CP again on the current pass.
        // After we're done with all the grow-by-50s, nothing else will
        // grow by 50 again on the current pass, and we can process the
        // grow-by-49s and we know we'll only have to process each one
        // once.  And so on.
        //
        // This generalizes to multiple seed nodes also.
        while (!m_pending.empty()) {
            PropCpPendSet::reverse_iterator it = m_pending.rbegin();
            V3GraphVertex* updateMep = (*it).key();
            uint32_t cpGrowBy = (*it).value();
            m_pending.erase(it);

            // For *updateMep, whose critPathCost was out-of-date with respect
            // to its edges, update the critPathCost.
            uint32_t startCp = m_accessp->critPathCost(updateMep, m_way);
            uint32_t newCp = startCp + cpGrowBy;
            if (m_slowAsserts) {
                m_accessp->checkNewCpVersusEdges(updateMep, m_way, newCp);
            }

            m_accessp->setCritPathCost(updateMep, m_way, newCp);
            cpHasIncreased(updateMep, newCp + m_accessp->cost(updateMep));
        }
    }

private:
    VL_DEBUG_FUNC;
    VL_UNCOPYABLE(PartPropagateCp);
};

class PartPropagateCpSelfTest {
private:
    // MEMBERS
    V3Graph m_graph;  // A graph
    V3GraphVertex* m_vx[50];  // All vertices within the graph
    typedef vl_unordered_map<V3GraphVertex*, uint32_t> CpMap;
    CpMap m_cp;  // Vertex-to-CP map
    CpMap m_seen;  // Set of vertices we've seen

    // CONSTRUCTORS
    PartPropagateCpSelfTest() {}
    ~PartPropagateCpSelfTest() {}

    // METHODS
protected:
    friend class PartPropagateCp<PartPropagateCpSelfTest>;
    void notifyEdgeCp(V3GraphVertex* vxp, GraphWay way,
                      V3GraphVertex* throughp, uint32_t cp) const {
        uint32_t throughCost = critPathCost(throughp, way);
        UASSERT_SELFTEST(uint32_t, cp, (1 + throughCost));
    }
private:
    void checkNewCpVersusEdges(V3GraphVertex* vxp,
                               GraphWay way, uint32_t cp) const {
        // Don't need to check this in the self test; it supports an assert
        // that runs in production code.
    }
    void setCritPathCost(V3GraphVertex* vxp,
                         GraphWay way, uint32_t cost) {
        m_cp[vxp] = cost;
        // Confirm that we only set each node's CP once.  That's an
        // important property of PartPropagateCp which allows it to be far
        // faster than a recursive algorithm on some graphs.
        CpMap::iterator it = m_seen.find(vxp);
        UASSERT_OBJ(it == m_seen.end(), vxp, "Set CP on node twice");
        m_seen[vxp] = cost;
    }
    uint32_t critPathCost(V3GraphVertex* vxp, GraphWay way) const {
        CpMap::const_iterator it = m_cp.find(vxp);
        if (it != m_cp.end()) return it->second;
        return 0;
    }
    uint32_t cost(const V3GraphVertex*) const { return 1; }
    void partInitCriticalPaths(bool checkOnly) {
        // Set up the FORWARD cp's only.  This test only looks in one
        // direction, it assumes REVERSE is symmetrical and would be
        // redundant to test.
        GraphStreamUnordered order(&m_graph);
        while (const V3GraphVertex* cvxp = order.nextp()) {
            V3GraphVertex* vxp = const_cast<V3GraphVertex*>(cvxp);
            uint32_t cpCost = 0;
            for (V3GraphEdge* edgep = vxp->inBeginp();
                 edgep; edgep = edgep->inNextp()) {
                V3GraphVertex* parentp = edgep->fromp();
                cpCost = std::max(cpCost,
                                  critPathCost(parentp, GraphWay::FORWARD) + 1);
            }
            if (checkOnly) {
                UASSERT_SELFTEST(uint32_t, cpCost,
                                 critPathCost(vxp, GraphWay::FORWARD));
            } else {
                setCritPathCost(vxp, GraphWay::FORWARD, cpCost);
            }
        }
    }
    void go() {
        // Generate a pseudo-random graph
        vluint64_t rngState[2] = {VL_ULL(0x12345678), VL_ULL(0x9abcdef0)};
        // Create 50 vertices
        for (unsigned i = 0; i < 50; ++i) {
            m_vx[i] = new V3GraphVertex(&m_graph);
        }
        // Create 250 edges at random. Edges must go from
        // lower-to-higher index vertices, so we get a DAG.
        for (unsigned i = 0; i < 250; ++i) {
            unsigned idx1 = V3Os::rand64(rngState) % 50;
            unsigned idx2 = V3Os::rand64(rngState) % 50;
            if (idx1 > idx2) {
                new V3GraphEdge(&m_graph, m_vx[idx2], m_vx[idx1], 1);
            } else if (idx2 > idx1) {
                new V3GraphEdge(&m_graph, m_vx[idx1], m_vx[idx2], 1);
            }
        }

        partInitCriticalPaths(false);

        // This SelfTest class is also the T_CostAccessor
        PartPropagateCp<PartPropagateCpSelfTest>
            prop(&m_graph, GraphWay::FORWARD, this, true);

        // Seed the propagator with every input node;
        // This should result in the complete graph getting all CP's assigned.
        for (unsigned i = 0; i < 50; ++i) {
            if (!m_vx[i]->inBeginp()) {
                prop.cpHasIncreased(m_vx[i], 1 /* inclusive CP starts at 1 */);
            }
        }

        // Run the propagator.
        //  * The setCritPathCost() routine checks that each node's CP changes
        //    at most once.
        //  * The notifyEdgeCp routine is also self checking.
        m_seen.clear();
        prop.go();

        // Finally, confirm that the entire graph appears to have correct CPs.
        partInitCriticalPaths(true);
    }
public:
    static void selfTest() {
        PartPropagateCpSelfTest().go();
    }
};

//######################################################################
// LogicMTask

class LogicMTask : public AbstractLogicMTask {
public:
    // TYPES
    typedef std::list<MTaskMoveVertex*> VxList;

    struct CmpLogicMTask {
        bool operator() (const LogicMTask* ap, const LogicMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

    // This adaptor class allows the PartPropagateCp class to be somewhat
    // independent of the LogicMTask class
    //  - PartPropagateCp can thus be declared before LogicMTask
    //  - PartPropagateCp could be reused with graphs of other node types
    //    in the future, using another Accessor adaptor.
    class CpCostAccessor {
    public:
        CpCostAccessor() {}
        ~CpCostAccessor() {}
        // Return cost of this node
        uint32_t cost(const V3GraphVertex* vxp) const {
            const LogicMTask* mtaskp = dynamic_cast<const LogicMTask*>(vxp);
            return mtaskp->stepCost();
        }
        // Return stored CP to this node
        uint32_t critPathCost(const V3GraphVertex* vxp, GraphWay way) const {
            const LogicMTask* mtaskp = dynamic_cast<const LogicMTask*>(vxp);
            return mtaskp->critPathCost(way);
        }
        // Store a new CP to this node
        void setCritPathCost(V3GraphVertex* vxp,
                             GraphWay way, uint32_t cost) const {
            LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(vxp);
            mtaskp->setCritPathCost(way, cost);
        }
        // Notify vxp that the wayward CP at the throughp-->vxp edge
        // has increased to 'cp'. (vxp is wayward from throughp.)
        // This is our cue to update vxp's m_edges[!way][throughp].
        void notifyEdgeCp(V3GraphVertex* vxp, GraphWay way,
                          V3GraphVertex* throuvhVxp, uint32_t cp) const {
            LogicMTask* updateVxp = dynamic_cast<LogicMTask*>(vxp);
            LogicMTask* lthrouvhVxp = dynamic_cast<LogicMTask*>(throuvhVxp);
            EdgeSet& edges = updateVxp->m_edges[way.invert()];
            uint32_t edgeCp = edges.at(lthrouvhVxp);
            if (cp > edgeCp) edges.set(lthrouvhVxp, cp);
        }
        // Check that CP matches that of the longest edge wayward of vxp.
        void checkNewCpVersusEdges(V3GraphVertex* vxp,
                                   GraphWay way, uint32_t cp) const {
            LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(vxp);
            EdgeSet& edges = mtaskp->m_edges[way.invert()];
            // This is mtaskp's relative with longest !wayward inclusive CP:
            EdgeSet::reverse_iterator edgeIt = edges.rbegin();
            uint32_t edgeCp = (*edgeIt).value();
            UASSERT_OBJ(edgeCp == cp, vxp, "CP doesn't match longest wayward edge");
        }
    private:
        VL_UNCOPYABLE(CpCostAccessor);
    };

private:
    // MEMBERS

    // Set of MTaskMoveVertex's assigned to this mtask. LogicMTask does not
    // own the MTaskMoveVertex objects, we merely keep pointers to them
    // here.
    VxList m_vertices;

    // Cost estimate for this LogicMTask, derived from V3InstrCount.
    // In abstract time units.
    uint32_t m_cost;

    // Cost of critical paths going FORWARD from graph-start to the start
    // of this vertex, and also going REVERSE from the end of the graph to
    // the end of the vertex. Same units as m_cost.
    uint32_t m_critPathCost[GraphWay::NUM_WAYS];

    uint32_t m_serialId;  // Unique MTask ID number

    // Count "generations" which are just operations that scan through the
    // graph. We'll mark each node with the last generation that scanned
    // it. We can use this to avoid recursing through the same node twice
    // while searching for a path.
    vluint64_t m_generation;

    // Redundant with the V3GraphEdge's, store a map of relatives so we can
    // quickly check if we have a given parent or child.
    //
    // 'm_edges[way]' maps a wayward relative to the !way critical path at
    // our edge with them. The SortByValueMap supports iterating over
    // relatives in longest-to-shortest CP order.  We rely on this ordering
    // in more than one place.
    typedef SortByValueMap<LogicMTask*, uint32_t, CmpLogicMTask> EdgeSet;
    EdgeSet m_edges[GraphWay::NUM_WAYS];

public:
    // CONSTRUCTORS
    LogicMTask(V3Graph* graphp, MTaskMoveVertex* mtmvVxp)
        : AbstractLogicMTask(graphp)
        , m_cost(0)
        , m_generation(0) {
        for (int i=0; i<GraphWay::NUM_WAYS; ++i) m_critPathCost[i] = 0;
        if (mtmvVxp) {  // Else null for test
            m_vertices.push_back(mtmvVxp);
            if (OrderLogicVertex* olvp = mtmvVxp->logicp()) {
                m_cost += V3InstrCount::count(olvp->nodep(), true);
            }
        }
        // Start at 1, so that 0 indicates no mtask ID.
        static uint32_t s_nextId = 1;
        m_serialId = s_nextId++;
        UASSERT(s_nextId < 0xFFFFFFFFUL, "Too many mtasks");
    }

    // METHODS
    void moveAllVerticesFrom(LogicMTask* otherp) {
        // splice() is constant time
        m_vertices.splice(m_vertices.end(), otherp->m_vertices);
        m_cost += otherp->m_cost;
    }
    virtual const VxList* vertexListp() const {
        return &m_vertices;
    }
    static vluint64_t incGeneration() {
        static vluint64_t s_generation = 0;
        ++s_generation;
        return s_generation;
    }

    // Use this instead of pointer-compares to compare LogicMTasks. Avoids
    // nondeterministic output.  Also name mtasks based on this number in
    // the final C++ output.
    virtual uint32_t id() const { return m_serialId; }
    void id(uint32_t id) { m_serialId = id; }
    // Abstract cost of every logic mtask
    virtual uint32_t cost() const { return m_cost; }
    void setCost(uint32_t cost) { m_cost = cost; }  // For tests only
    uint32_t stepCost() const { return stepCost(m_cost); }
    static uint32_t stepCost(uint32_t cost) {
#if PART_STEPPED_COST
        // Round cost up to the nearest 5%. Use this when computing all
        // critical paths. The idea is that critical path changes don't
        // need to propagate when they don't exceed the next step, saving a
        // lot of recursion.
        if (cost == 0) return 0;

        double logcost = log(cost);
        // log(1.05) is about 0.05
        // So, round logcost up to the next 0.05 boundary
        logcost *= 20.0;
        logcost = ceil(logcost);
        logcost = logcost / 20.0;

        uint32_t stepCost = static_cast<uint32_t>(exp(logcost));
        UASSERT_STATIC(stepCost >= cost, "stepped cost error exceeded");
        UASSERT_STATIC(stepCost <= ((cost * 11 / 10)), "stepped cost error exceeded");
        return stepCost;
#else
        return cost;
#endif
    }

    void addRelative(GraphWay way, LogicMTask* relativep) {
        EdgeSet& edges = m_edges[way];
        UASSERT(!edges.has(relativep), "Adding existing edge");
        // value is !way cp to this edge
        edges.set(relativep,
                  relativep->stepCost()
                  + relativep->critPathCost(way.invert()));
    }
    void removeRelative(GraphWay way, LogicMTask* relativep) {
        EdgeSet& edges = m_edges[way];
        edges.erase(relativep);
    }
    bool hasRelative(GraphWay way, LogicMTask* relativep) {
        const EdgeSet& edges = m_edges[way];
        return edges.has(relativep);
    }
    void checkRelativesCp(GraphWay way) const {
        const EdgeSet& edges = m_edges[way];
        for (EdgeSet::const_reverse_iterator it = edges.rbegin();
             it != edges.rend(); ++it) {
            LogicMTask* relativep = (*it).key();
            uint32_t cachedCp = (*it).value();
            partCheckCachedScoreVsActual
                (cachedCp,
                 relativep->critPathCost(way.invert()) + relativep->stepCost());
        }
    }

    virtual string name() const {
        // Display forward and reverse critical path costs. This gives a quick
        // read on whether graph partitioning looks reasonable or bad.
        std::ostringstream out;
        out <<"mt"<<m_serialId<<"."<<this
            <<" [b"<<m_critPathCost[GraphWay::FORWARD]
            <<" a"<<m_critPathCost[GraphWay::REVERSE]
            <<" c"<<cost();
        return out.str();
    }

    void setCritPathCost(GraphWay way, uint32_t cost) { m_critPathCost[way] = cost; }
    uint32_t critPathCost(GraphWay way) const { return m_critPathCost[way]; }
    uint32_t critPathCostWithout(GraphWay way,
                                 const V3GraphEdge* withoutp) const {
        // Compute the critical path cost wayward to this node, without
        // considering edge 'withoutp'
        UASSERT(this == withoutp->furtherp(way),
                "In critPathCostWithout(), edge 'withoutp' must "
                "further to 'this'");

        // Iterate through edges until we get a relative other than
        // wayEdgeEndp(way, withoutp). This should take 2 iterations max.
        const EdgeSet& edges = m_edges[way.invert()];
        uint32_t result = 0;
        for (EdgeSet::const_reverse_iterator it = edges.rbegin();
             it != edges.rend(); ++it) {
            if ((*it).key() != withoutp->furtherp(way.invert())) {
                // Use the cached cost. It could be a small overestimate
                // due to stepping. This is consistent with critPathCost()
                // which also returns the cached cost.
                result = (*it).value();
                break;
            }
        }
        return result;
    }

private:
    static bool pathExistsFromInternal(LogicMTask* fromp,
                                       LogicMTask* top,
                                       const V3GraphEdge* excludedEdgep,
                                       vluint64_t generation) {
        // Q) Why does this take LogicMTask instead of generic V3GraphVertex?
        // A) We'll use the critical paths known to LogicMTask to prune the
        //    recursion for speed. Also store 'generation' in
        //    LogicMTask::m_generation so we can prune the search and avoid
        //    recursing through the same node more than once in a single
        //    search.

        if (fromp->m_generation == generation) {
            // Already looked at this node in the current search.
            // Since we're back again, we must not have found a path on the
            // first go.
            return false;
        }
        fromp->m_generation = generation;

        // Base case: we found a path.
        if (fromp == top) return true;

        // Base case: fromp is too late, cannot possibly be a prereq for top.
        if (fromp->critPathCost(GraphWay::REVERSE)
            < (top->critPathCost(GraphWay::REVERSE) + top->stepCost())) return false;
        if ((fromp->critPathCost(GraphWay::FORWARD) + fromp->stepCost())
            > top->critPathCost(GraphWay::FORWARD)) return false;

        // Recursively look for a path
        for (const V3GraphEdge* followp = fromp->outBeginp();
             followp; followp = followp->outNextp()) {
            if (followp == excludedEdgep) continue;
            LogicMTask* nextp = dynamic_cast<LogicMTask*>(followp->top());
            if (pathExistsFromInternal(nextp, top, NULL, generation))
                return true;
        }
        return false;
    }

    // True if there's a path from 'fromp' to 'top' excluding
    // 'excludedEdgep', false otherwise.
    //
    // 'excludedEdgep' may be NULL in which case no edge is excluded.  If
    // 'excludedEdgep' is non-NULL it must connect fromp and top.
    //
    // TODO: consider changing this API to the 'isTransitiveEdge' API
    // used by GraphPathChecker
public:
    static bool pathExistsFrom(LogicMTask* fromp,
                               LogicMTask* top,
                               const V3GraphEdge* excludedEdgep) {
        return pathExistsFromInternal(fromp, top, excludedEdgep,
                                      incGeneration());
    }

    static void dumpCpFilePrefixed(const V3Graph* graphp,
                                   const string& nameComment) {
        string filename = v3Global.debugFilename(nameComment)+".txt";
        UINFO(1,"Writing "<<filename<<endl);
        vl_unique_ptr<std::ofstream> ofp(V3File::new_ofstream(filename));
        std::ostream* osp = &(*ofp);  // &* needed to deref unique_ptr
        if (osp->fail()) v3fatalStatic("Can't write "<<filename);

        // Find start vertex with longest CP
        const LogicMTask* startp = NULL;
        for (const V3GraphVertex* vxp = graphp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            const LogicMTask* mtaskp = dynamic_cast<const LogicMTask*>(vxp);
            if (!startp) {
                startp = mtaskp;
                continue;
            }
            if (mtaskp->cost() + mtaskp->critPathCost(GraphWay::REVERSE)
                > startp->cost() + startp->critPathCost(GraphWay::REVERSE)) {
                startp = mtaskp;
            }
        }

        // Follow the entire critical path
        std::vector<const LogicMTask*> path;
        uint32_t totalCost = 0;
        for (const LogicMTask* nextp = startp; nextp;) {
            path.push_back(nextp);
            totalCost += nextp->cost();

            const EdgeSet& children = nextp->m_edges[GraphWay::FORWARD];
            EdgeSet::const_reverse_iterator it = children.rbegin();
            if (it == children.rend()) nextp = NULL;
            else nextp = (*it).key();
        }

        *osp<<"totalCost = "<<totalCost
            <<" (should match the computed critical path cost (CP) for the graph)\n";

        // Dump
        for (std::vector<const LogicMTask*>::iterator it = path.begin();
             it != path.end(); ++it) {
            const LogicMTask* mtaskp = *it;
            *osp<<"begin mtask with cost "<<mtaskp->cost()<<endl;
            for (VxList::const_iterator lit = mtaskp->vertexListp()->begin();
                 lit != mtaskp->vertexListp()->end(); ++lit) {
                const OrderLogicVertex* logicp = (*lit)->logicp();
                if (!logicp) continue;
                if (0) {
                    // Show nodes only
                    *osp<<"> "; logicp->nodep()->dumpTree(*osp);
                } else {
                    // Show nodes with hierarchical costs
                    V3InstrCount::count(logicp->nodep(), false, osp);
                }
            }
        }
    }

private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(LogicMTask);
};

//######################################################################
// MTask utility classes

// Sort AbstractMTask objects into deterministic order by calling id()
// which is a unique and stable serial number.
class MTaskIdLessThan {
public:
    MTaskIdLessThan() {}
    virtual ~MTaskIdLessThan() {}
    virtual bool operator() (const AbstractMTask* lhsp,
                             const AbstractMTask* rhsp) const {
        return lhsp->id() < rhsp->id();
    }
};

// Information associated with scoreboarding an MTask
class MergeCandidate {
private:
    bool m_removedFromSb;  // Not on scoreboard, generally ignore
    vluint64_t m_id;  // Serial number for ordering
public:
    // CONSTRUCTORS
    MergeCandidate() : m_removedFromSb(false) {
        static vluint64_t serial = 0;
        ++serial;
        m_id = serial;
    }
    virtual bool mergeWouldCreateCycle() const = 0;
    // METHODS
    bool removedFromSb() const { return m_removedFromSb; }
    void removedFromSb(bool removed) { m_removedFromSb = removed; }
    bool operator<(const MergeCandidate& other) const {
        return m_id < other.m_id;
    }
};

// A pair of associated LogicMTask's that are merge candidates for sibling
// contraction
class SiblingMC : public MergeCandidate {
private:
    LogicMTask* m_ap;
    LogicMTask* m_bp;
    // CONSTRUCTORS
    SiblingMC() VL_EQ_DELETE;
public:
    SiblingMC(LogicMTask* ap, LogicMTask* bp) {
        // Assign 'ap' and 'bp' in a canonical order, so we can more easily
        // compare pairs of SiblingMCs
        if (ap->id() > bp->id()) {
            m_ap = ap;
            m_bp = bp;
        } else {
            m_ap = bp;
            m_bp = ap;
        }
    }
    virtual ~SiblingMC() {}
    // METHODS
    LogicMTask* ap() const { return m_ap; }
    LogicMTask* bp() const { return m_bp; }
    bool mergeWouldCreateCycle() const {
        return (LogicMTask::pathExistsFrom(m_ap, m_bp, NULL)
                || LogicMTask::pathExistsFrom(m_bp, m_ap, NULL));
    }
    bool operator<(const SiblingMC& other) const {
        if (m_ap->id() < other.m_ap->id()) { return true; }
        if (m_ap->id() > other.m_ap->id()) { return false; }
        return m_bp->id() < other.m_bp->id();
    }
};

// GraphEdge for the MTask graph
class MTaskEdge : public V3GraphEdge, public MergeCandidate {
public:
    // CONSTRUCTORS
    MTaskEdge(V3Graph* graphp, LogicMTask* fromp, LogicMTask* top, int weight)
        : V3GraphEdge(graphp, fromp, top, weight) {
        fromp->addRelative(GraphWay::FORWARD, top);
        top->addRelative(GraphWay::REVERSE, fromp);
    }
    virtual ~MTaskEdge() {
        fromMTaskp()->removeRelative(GraphWay::FORWARD, toMTaskp());
        toMTaskp()->removeRelative(GraphWay::REVERSE, fromMTaskp());
    }
    // METHODS
    LogicMTask* furtherMTaskp(GraphWay way) const {
        return dynamic_cast<LogicMTask*>(this->furtherp(way));
    }
    LogicMTask* fromMTaskp() const {
        return dynamic_cast<LogicMTask*>(fromp());
    }
    LogicMTask* toMTaskp() const {
        return dynamic_cast<LogicMTask*>(top());
    }
    virtual bool mergeWouldCreateCycle() const {
        return LogicMTask::pathExistsFrom(fromMTaskp(), toMTaskp(), this);
    }
    static MTaskEdge* cast(V3GraphEdge* edgep) {
        if (!edgep) return NULL;
        MTaskEdge* resultp = dynamic_cast<MTaskEdge*>(edgep);
        UASSERT(resultp, "Failed to cast in MTaskEdge::cast");
        return resultp;
    }
    // Following initial assignment of critical paths, clear this MTaskEdge
    // out of the edge-map for each node and reinsert at a new location
    // with updated critical path.
    void resetCriticalPaths() {
        LogicMTask* fromp = fromMTaskp();
        LogicMTask* top = toMTaskp();
        fromp->removeRelative(GraphWay::FORWARD, top);
        top->removeRelative(GraphWay::REVERSE, fromp);
        fromp->addRelative(GraphWay::FORWARD, top);
        top->addRelative(GraphWay::REVERSE, fromp);
    }
private:
    VL_UNCOPYABLE(MTaskEdge);
};

//######################################################################
// Vertex utility classes

class OrderByPtrId {
    PartPtrIdMap m_ids;
public:
    virtual bool operator() (const OrderVarStdVertex* lhsp,
                             const OrderVarStdVertex* rhsp) const {
        vluint64_t l_id = m_ids.findId(lhsp);
        vluint64_t r_id = m_ids.findId(rhsp);
        return l_id < r_id;
    }
};

//######################################################################
// PartParallelismEst - Estimate parallelism of graph

class PartParallelismEst {
    // MEMBERS
    const V3Graph* m_graphp;  // Mtask-containing graph

    // Total cost of evaluating the whole graph.
    // The ratio of m_totalGraphCost to longestCpCost gives us an estimate
    // of the parallelizability of this graph which is only as good as the
    // guess returned by LogicMTask::cost().
    uint32_t m_totalGraphCost;

    // Cost of the longest critical path, in abstract units (the same units
    // returned by the vertexCost)
    uint32_t m_longestCpCost;

    size_t m_vertexCount;  // Number of vertexes calculated
    size_t m_edgeCount;  // Number of edges calculated

public:
    // CONSTRUCTORS
    explicit PartParallelismEst(const V3Graph* graphp)
        : m_graphp(graphp),
          m_totalGraphCost(0),
          m_longestCpCost(0),
          m_vertexCount(0),
          m_edgeCount(0) {}

    // METHODS
    uint32_t totalGraphCost() const { return m_totalGraphCost; }
    uint32_t longestCritPathCost() const { return m_longestCpCost; }
    size_t vertexCount() const { return m_vertexCount; }
    size_t edgeCount() const { return m_edgeCount; }
    double parallelismFactor() const {
        return (static_cast<double>(m_totalGraphCost) / m_longestCpCost);
    }
    void traverse() {
        // For each node, record the critical path cost from the start
        // of the graph through the end of the node.
        vl_unordered_map<const V3GraphVertex*, uint32_t> critPaths;
        GraphStreamUnordered serialize(m_graphp);
        for (const V3GraphVertex* vertexp;
             (vertexp = serialize.nextp());) {
            m_vertexCount++;
            uint32_t cpCostToHere = 0;
            for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep;
                 edgep = edgep->inNextp()) {
                ++m_edgeCount;
                // For each upstream item, add its critical path cost to
                // the cost of this edge, to form a new candidate critical
                // path cost to the current node. Whichever is largest is
                // the critical path to reach the start of this node.
                cpCostToHere = std::max(cpCostToHere, critPaths[edgep->fromp()]);
            }
            // Include the cost of the current vertex in the critical
            // path, so it represents the critical path to the end of
            // this vertex.
            cpCostToHere += vertexCost(vertexp);
            critPaths[vertexp] = cpCostToHere;
            m_longestCpCost = std::max(m_longestCpCost, cpCostToHere);
            // Tally the total cost contributed by vertices.
            m_totalGraphCost += vertexCost(vertexp);
        }
    }
    void statsReport(const string& stage) {
        V3Stats::addStat("MTask graph, "+stage+", critical path cost",
                         m_longestCpCost);
        V3Stats::addStat("MTask graph, "+stage+", total graph cost",
                         m_totalGraphCost);
        V3Stats::addStat("MTask graph, "+stage+", mtask count",
                         m_vertexCount);
        V3Stats::addStat("MTask graph, "+stage+", edge count",
                         m_edgeCount);
        V3Stats::addStat("MTask graph, "+stage+", parallelism factor",
                         parallelismFactor());
    }
    void debugReport() {
        UINFO(0, "    Critical path cost = "<<m_longestCpCost<<endl);
        UINFO(0, "    Total graph cost = "<<m_totalGraphCost<<endl);
        UINFO(0, "    MTask vertex count = "<<m_vertexCount<<endl);
        UINFO(0, "    Edge count = "<<m_edgeCount<<endl);
        UINFO(0, "    Parallelism factor = "<<parallelismFactor()<<endl);
    }
    static uint32_t vertexCost(const V3GraphVertex* vertexp) {
        return dynamic_cast<const AbstractMTask*>(vertexp)->cost();
    }

private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(PartParallelismEst);
};

//######################################################################

// Look at vertex costs (in one way) to form critical paths for each
// vertex.
static void partInitHalfCriticalPaths(GraphWay way, V3Graph* mtasksp, bool checkOnly) {
    GraphStreamUnordered order(mtasksp, way);
    GraphWay rev = way.invert();
    for (const V3GraphVertex* vertexp;
         (vertexp = order.nextp());) {
        const LogicMTask* mtaskcp = dynamic_cast<const LogicMTask*>(vertexp);
        LogicMTask* mtaskp = const_cast<LogicMTask*>(mtaskcp);
        uint32_t cpCost = 0;
        vl_unordered_set<V3GraphVertex*> relatives;
        for (V3GraphEdge* edgep = vertexp->beginp(rev);
             edgep; edgep = edgep->nextp(rev)) {
            // Run a few asserts on the initial mtask graph,
            // while we're iterating through...
            UASSERT_OBJ(edgep->weight() != 0, mtaskp,
                        "Should be no cut edges in mtasks graph");
            UASSERT_OBJ(relatives.find(edgep->furtherp(rev)) == relatives.end(), mtaskp,
                        "Should be no redundant edges in mtasks graph");
            relatives.insert(edgep->furtherp(rev));

            LogicMTask* relativep
                = dynamic_cast<LogicMTask*>(edgep->furtherp(rev));
            cpCost = std::max(cpCost,
                              (relativep->critPathCost(way)
                               + static_cast<uint32_t>(relativep->stepCost())));
        }
        if (checkOnly) {
            partCheckCachedScoreVsActual(mtaskp->critPathCost(way), cpCost);
        } else {
            mtaskp->setCritPathCost(way, cpCost);
        }
    }
}

// Look at vertex costs to form critical paths for each vertex.
static void partInitCriticalPaths(V3Graph* mtasksp) {
    partInitHalfCriticalPaths(GraphWay::FORWARD, mtasksp, false);
    partInitHalfCriticalPaths(GraphWay::REVERSE, mtasksp, false);

    // Reset all MTaskEdges so that 'm_edges' will show correct CP numbers.
    // They would have been all zeroes on initial creation of the MTaskEdges.
    for (V3GraphVertex* vxp = mtasksp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        for (V3GraphEdge* edgep = vxp->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            MTaskEdge* mtedgep = dynamic_cast<MTaskEdge*>(edgep);
            mtedgep->resetCriticalPaths();
        }
    }
}

// Do an EXPENSIVE check to make sure that all incremental CP updates have
// gone correctly.
static void partCheckCriticalPaths(V3Graph* mtasksp) {
    partInitHalfCriticalPaths(GraphWay::FORWARD, mtasksp, true);
    partInitHalfCriticalPaths(GraphWay::REVERSE, mtasksp, true);
    for (V3GraphVertex* vxp = mtasksp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(vxp);
        mtaskp->checkRelativesCp(GraphWay::FORWARD);
        mtaskp->checkRelativesCp(GraphWay::REVERSE);
    }
}

// Advance to nextp(way) and delete edge
static V3GraphEdge* partBlastEdgep(GraphWay way, V3GraphEdge* edgep) {
    V3GraphEdge* nextp = edgep->nextp(way);
    VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
    return nextp;
}

// Merge edges from a LogicMtask.
//
// This code removes 'hasRelative' edges. When this occurs, mark it in need
// of a rescore, in case its score has fallen and we need to move it up
// toward the front of the scoreboard.
//
// Wait, whaaat? Shouldn't the scores only increase as we merge nodes? Well
// that's almost true. But there is one exception.
//
// Suppose we have A->B, B->C, and A->C.
//
// The A->C edge is a "transitive" edge. It's ineligible to be merged, as
// the merge would create a cycle. We score it on the scoreboard like any
// other edge.
//
// However, our "score" estimate for A->C is bogus, because the forward
// critical path to C and the reverse critical path to A both contain the
// same node (B) so we overestimate the score of A->C. At first this
// doesn't matter, since transitive edges aren't eligible to merge anyway.
//
// Later, suppose the edge contractor decides to merge the B->C edge, with
// B donating all its incoming edges into C, say.  (So we reach this
// function.)
//
// With B going away, the A->C edge will no longer be transitive and it
// will become eligible to merge. But if we don't mark it for rescore,
// it'll stay in the scoreboard with its old (overestimate) score. We'll
// merge it too late due to the bogus score. When we finally merge it, we
// fail the assert in the main edge contraction loop which checks that the
// actual score did not fall below the scoreboard's score.
//
// Another way of stating this: this code ensures that scores of
// non-transitive edges only ever increase.
static void partMergeEdgesFrom(V3Graph* mtasksp, LogicMTask* recipientp,
                               LogicMTask* donorp,
                               V3Scoreboard<MergeCandidate, uint32_t>* sbp) {
    for (unsigned wi = 0; wi < 2; ++wi) {
        GraphWay way = wi ? GraphWay::REVERSE : GraphWay::FORWARD;
        for (V3GraphEdge* edgep = donorp->beginp(way);
             edgep; edgep = partBlastEdgep(way, edgep)) {
            MTaskEdge* tedgep = MTaskEdge::cast(edgep);
            if (sbp && !tedgep->removedFromSb())
                sbp->removeElem(tedgep);
            // Existing edge; mark it in need of a rescore
            if (recipientp->hasRelative(way, tedgep->furtherMTaskp(way))) {
                if (sbp) {
                    MTaskEdge* existMTaskEdgep =
                        MTaskEdge::cast(recipientp->findConnectingEdgep
                                        (way, tedgep->furtherMTaskp(way)));
                    UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge");
                    if (!existMTaskEdgep->removedFromSb()) {
                        sbp->hintScoreChanged(existMTaskEdgep);
                    }
                }
            } else {
                // No existing edge into *this, make one.
                MTaskEdge* newEdgep;
                if (way == GraphWay::REVERSE) {
                    newEdgep = new MTaskEdge(mtasksp, tedgep->fromMTaskp(),
                                             recipientp, 1);
                } else {
                    newEdgep = new MTaskEdge(mtasksp, recipientp,
                                             tedgep->toMTaskp(), 1);
                }
                if (sbp) sbp->addElem(newEdgep);
            }
        }
    }
}

//######################################################################
// PartContraction

// Perform edge or sibling contraction on the partition graph
class PartContraction {
private:
    // TYPES

    // TODO: might get a little more speed by making this a
    // vl_unordered_set and defining hash and equal_to functors for the
    // SiblingMC:
    typedef std::set<SiblingMC> SibSet;
    typedef vl_unordered_set<const SiblingMC*> SibpSet;
    typedef vl_unordered_map<const LogicMTask*, SibpSet> MTask2Sibs;

    // New CP information for mtaskp reflecting an upcoming merge
    struct NewCp {
        uint32_t cp;
        uint32_t propagateCp;
        bool propagate;
    };

    // MEMBERS
    V3Graph* m_mtasksp;  // Mtask graph
    uint32_t m_scoreLimit;  // Sloppy score allowed when picking merges
    uint32_t m_scoreLimitBeforeRescore;  // Next score rescore at
    unsigned m_mergesSinceRescore;  // Merges since last rescore
    bool m_slowAsserts;  // Take extra time to validate algorithm
    V3Scoreboard<MergeCandidate, uint32_t> m_sb;  // Scoreboard
    SibSet m_pairs;  // Storage for each SiblingMC
    MTask2Sibs m_mtask2sibs;  // SiblingMC set for each mtask

public:
    // CONSTRUCTORS
    PartContraction(V3Graph* mtasksp, uint32_t scoreLimit, bool slowAsserts)
        : m_mtasksp(mtasksp)
        , m_scoreLimit(scoreLimit)
        , m_scoreLimitBeforeRescore(0xffffffff)
        , m_mergesSinceRescore(0)
        , m_slowAsserts(slowAsserts)
        , m_sb(&mergeCandidateScore, slowAsserts) { }

    // METHODS
    void go() {
        unsigned maxMTasks = v3Global.opt.threadsMaxMTasks();
        if (maxMTasks == 0) {  // Unspecified so estimate
            if (v3Global.opt.threads() > 1) {
                maxMTasks = (PART_DEFAULT_MAX_MTASKS_PER_THREAD
                             * v3Global.opt.threads());
            } else {
                // Running PartContraction with --threads <= 1 means self-test
                maxMTasks = 500;
            }
        }

        // OPTIMIZATION PASS: Edge contraction and sibling contraction.
        //  - Score each pair of mtasks which is a candidate to merge.
        //    * Each edge defines such a candidate pair
        //    * Two mtasks that are prereqs or postreqs of a common third
        //      vertex are "siblings", these are also a candidate pair.
        //  - Build a list of MergeCandidates, sorted by score.
        //  - Merge the best pair.
        //  - Incrementally recompute critical paths near the merged mtask.

        for (V3GraphVertex* itp = m_mtasksp->verticesBeginp(); itp;
             itp = itp->verticesNextp()) {
            vl_unordered_set<const V3GraphVertex*> neighbors;
            for (V3GraphEdge* edgep = itp->outBeginp(); edgep;
                 edgep=edgep->outNextp()) {
                m_sb.addElem(MTaskEdge::cast(edgep));
                UASSERT_OBJ(neighbors.find(edgep->top()) == neighbors.end(), itp,
                            "Redundant edge found in input to PartContraction()");
                neighbors.insert(edgep->top());
            }
            siblingPairFromRelatives(GraphWay::REVERSE, itp, true);
            siblingPairFromRelatives(GraphWay::FORWARD, itp, true);
        }

        doRescore();  // Set initial scores in scoreboard

        while (1) {
            // This is the best edge to merge, with the lowest
            // score (shortest local critical path)
            MergeCandidate* mergeCanp = const_cast<MergeCandidate*>(m_sb.bestp());
            if (!mergeCanp) {
                // Scoreboard found no eligible merges. Maybe a rescore
                // will produce some merge-able pairs?
                if (m_sb.needsRescore()) {
                    doRescore();
                    continue;
                }
                break;
            }

            if (m_slowAsserts) {
                UASSERT(!m_sb.needsRescore(mergeCanp),
                        "Need-rescore items should not be returned by bestp");
            }
            uint32_t cachedScore = m_sb.cachedScore(mergeCanp);
            uint32_t actualScore = mergeCandidateScore(mergeCanp);

            if (actualScore > cachedScore) {
                // Cached score is out-of-date.
                // Mark this elem as in need of a rescore and continue.
                m_sb.hintScoreChanged(mergeCanp);
                continue;
            }
            // ... we'll also confirm that actualScore hasn't shrunk relative
            // to cached score, after the mergeWouldCreateCycle() check.

            if (actualScore > m_scoreLimit) {
                // Our best option isn't good enough
                if (m_sb.needsRescore()) {
                    // Some pairs need a rescore, maybe those will be
                    // eligible to merge afterward.
                    doRescore();
                    continue;
                } else {
                    // We've exhausted everything below m_scoreLimit; stop.

                    // Except, if we have too many mtasks, raise the score
                    // limit and keep going...
                    unsigned mtaskCount = 0;
                    for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp();
                         vxp; vxp = vxp->verticesNextp()) {
                        ++mtaskCount;
                    }
                    if (mtaskCount > maxMTasks) {
                        uint32_t oldLimit = m_scoreLimit;
                        m_scoreLimit = (m_scoreLimit * 120) / 100;
                        v3Global.rootp()->fileline()->v3warn(
                            UNOPTTHREADS, "Thread scheduler is unable to provide requested parallelism; consider asking for fewer threads.");
                        UINFO(1,"Critical path limit was="<<oldLimit
                              <<" now="<<m_scoreLimit<<endl);
                        continue;
                    }
                    // Really stop
                    break;
                }
            }
            if (actualScore > m_scoreLimitBeforeRescore) {
                // Time to rescore, that will result in a higher
                // scoreLimitBeforeRescore, and possibly lower-scoring
                // elements returned from bestp().
                doRescore();
                continue;
            }

            // Avoid merging any edge that would create a cycle.
            //
            // For example suppose we begin with vertices A, B, C and edges
            // A->B, B->C, A->C.
            //
            // Suppose we want to merge A->C into a single vertex.
            // New edges would be AC->B and B->AC which is not a DAG.
            // Do not allow this.
            if (mergeCanp->mergeWouldCreateCycle()) {
                // Remove this edge from scoreboard so we don't keep
                // reconsidering it on every loop.
                m_sb.removeElem(mergeCanp);
                mergeCanp->removedFromSb(true);
                continue;
            }

            partCheckCachedScoreVsActual(cachedScore, actualScore);

            // Finally there's no cycle risk, no need to rescore, we're
            // within m_scoreLimit and m_scoreLimitBeforeRescore.
            // This is the edge to merge.
            //
            // Bookkeeping: if this is the first edge we'll merge since
            // the last rescore, compute the new m_scoreLimitBeforeRescore
            // to be somewhat higher than this edge's score.
            if (m_mergesSinceRescore == 0) {
#if PART_STEPPED_RESCORELIMIT
                m_scoreLimitBeforeRescore = (actualScore * 105) / 100;
#else
                m_scoreLimitBeforeRescore = actualScore;
#endif

                // This print can serve as a progress indicator, as it
                // increases from low numbers up toward cpLimit. It may be
                // helpful to see progress during slow partitions. Maybe
                // display something by default even?
                UINFO(6, "New scoreLimitBeforeRescore: "
                      <<m_scoreLimitBeforeRescore<<endl);
            }

            // Finally merge this candidate.
            contract(mergeCanp);
        }
    }

private:
    NewCp newCp(GraphWay way, LogicMTask* mtaskp, LogicMTask* otherp,
                MTaskEdge* mergeEdgep) {
        // Return new wayward-CP for mtaskp reflecting its upcoming merge
        // with otherp. Set 'result.propagate' if mtaskp's wayward
        // relatives will see a new wayward CP from this merge.
        uint32_t newCp;
        if (mergeEdgep) {
            if (mtaskp == mergeEdgep->furtherp(way)) {
                newCp = std::max(otherp->critPathCost(way),
                                 mtaskp->critPathCostWithout(way, mergeEdgep));
            } else {
                newCp = std::max(mtaskp->critPathCost(way),
                                 otherp->critPathCostWithout(way, mergeEdgep));
            }
        } else {
            newCp = std::max(otherp->critPathCost(way), mtaskp->critPathCost(way));
        }

        uint32_t origRelativesCp
            = mtaskp->critPathCost(way) + mtaskp->stepCost();
        uint32_t newRelativesCp
            = newCp + LogicMTask::stepCost(mtaskp->cost() + otherp->cost());

        NewCp result;
        result.cp = newCp;
        result.propagate = (newRelativesCp > origRelativesCp);
        result.propagateCp = newRelativesCp;
        return result;
    }

    void removeSiblingMCsWith(LogicMTask* mtaskp) {
        for (SibpSet::iterator it = m_mtask2sibs[mtaskp].begin();
             it != m_mtask2sibs[mtaskp].end(); ++it) {
            const SiblingMC* pairp = *it;
            if (!pairp->removedFromSb()) {
                m_sb.removeElem(pairp);
            }
            LogicMTask* otherp = (pairp->bp() == mtaskp) ?
                pairp->ap() : pairp->bp();
            size_t erased = m_mtask2sibs[otherp].erase(pairp);
            UASSERT_OBJ(erased > 0, otherp, "Expected existing mtask");
            erased = m_pairs.erase(*pairp);
            UASSERT_OBJ(erased > 0, mtaskp, "Expected existing mtask");
        }
        size_t erased = m_mtask2sibs.erase(mtaskp);
        UASSERT_OBJ(erased > 0, mtaskp, "Expected existing mtask");
    }

    void contract(MergeCandidate* mergeCanp) {
        LogicMTask *top = NULL;
        LogicMTask *fromp = NULL;
        MTaskEdge* mergeEdgep = dynamic_cast<MTaskEdge*>(mergeCanp);
        SiblingMC* mergeSibsp = NULL;
        if (mergeEdgep) {
            top = dynamic_cast<LogicMTask*>(mergeEdgep->top());
            fromp = dynamic_cast<LogicMTask*>(mergeEdgep->fromp());
        } else {
            mergeSibsp = dynamic_cast<SiblingMC*>(mergeCanp);
            UASSERT(mergeSibsp,
                    "Failed to cast mergeCanp to either MTaskEdge or SiblingMC");
            top = mergeSibsp->ap();
            fromp = mergeSibsp->bp();
        }

        // Merge the smaller mtask into the larger mtask.  If one of them
        // is much larger, this will save time in partMergeEdgesFrom().
        // Assume the more costly mtask has more edges.
        //
        // [TODO: now that we have edge maps, we could count the edges
        //  exactly without a linear search.]
        LogicMTask* recipientp;
        LogicMTask* donorp;
        if (fromp->cost() > top->cost()) {
            recipientp = fromp;
            donorp = top;
        } else {
            donorp = fromp;
            recipientp = top;
        }
        VL_DANGLING(fromp); VL_DANGLING(top);  // Use donorp and recipientp now instead

        // Recursively update forward and reverse CP numbers.
        //
        // Doing this before merging the mtasks lets us often avoid
        // recursing through either incoming or outgoing edges on one or
        // both mtasks.
        //
        // These 'NewCp' objects carry a bit indicating whether we must
        // propagate CP for each of the four cases:
        NewCp recipientNewCpFwd
            = newCp(GraphWay::FORWARD, recipientp, donorp, mergeEdgep);
        NewCp donorNewCpFwd
            = newCp(GraphWay::FORWARD, donorp, recipientp, mergeEdgep);
        NewCp recipientNewCpRev
            = newCp(GraphWay::REVERSE, recipientp, donorp, mergeEdgep);
        NewCp donorNewCpRev
            = newCp(GraphWay::REVERSE, donorp, recipientp, mergeEdgep);

        if (mergeEdgep) {
            // Remove and free the connecting edge. Must do this before
            // propagating CP's below.
            m_sb.removeElem(mergeCanp);
            VL_DO_CLEAR(mergeEdgep->unlinkDelete(), mergeEdgep=NULL);
        }

        // This also updates cost and stepCost on recipientp
        recipientp->moveAllVerticesFrom(donorp);

        UINFO(9, "recipient = "<<recipientp->id()
              << ", donor = "<<donorp->id()
              << ", mergeEdgep = "<<mergeEdgep
              << "\n"
              << "recipientNewCpFwd = "<<recipientNewCpFwd.cp
              << (recipientNewCpFwd.propagate ? " true " : " false ")
              << recipientNewCpFwd.propagateCp
              << "\n"
              << "donorNewCpFwd = "<<donorNewCpFwd.cp
              << (donorNewCpFwd.propagate ? " true " : " false ")
              << donorNewCpFwd.propagateCp
              << endl);

        LogicMTask::CpCostAccessor cpAccess;
        PartPropagateCp<LogicMTask::CpCostAccessor>
            forwardPropagator(m_mtasksp, GraphWay::FORWARD, &cpAccess, m_slowAsserts);
        PartPropagateCp<LogicMTask::CpCostAccessor>
            reversePropagator(m_mtasksp, GraphWay::REVERSE, &cpAccess, m_slowAsserts);

        recipientp->setCritPathCost(GraphWay::FORWARD,
                                    recipientNewCpFwd.cp);
        if (recipientNewCpFwd.propagate) {
            forwardPropagator.cpHasIncreased(recipientp, recipientNewCpFwd.propagateCp);
        }
        recipientp->setCritPathCost(GraphWay::REVERSE,
                                    recipientNewCpRev.cp);
        if (recipientNewCpRev.propagate) {
            reversePropagator.cpHasIncreased(recipientp, recipientNewCpRev.propagateCp);
        }
        if (donorNewCpFwd.propagate) {
            forwardPropagator.cpHasIncreased(donorp, donorNewCpFwd.propagateCp);
        }
        if (donorNewCpRev.propagate) {
            reversePropagator.cpHasIncreased(donorp, donorNewCpRev.propagateCp);
        }
        forwardPropagator.go();
        reversePropagator.go();

        // Remove all SiblingMCs that include donorp. This Includes the one
        // we're merging, if we're merging a SiblingMC.
        removeSiblingMCsWith(donorp);
        // Remove all SiblingMCs that include recipientp also, so we can't
        // get huge numbers of SiblingMCs.  We'll recreate them below, up
        // to a bounded number.
        removeSiblingMCsWith(recipientp);

        // Merge all edges
        partMergeEdgesFrom(m_mtasksp, recipientp, donorp, &m_sb);

        // Delete the donorp mtask from the graph
        VL_DO_CLEAR(donorp->unlinkDelete(m_mtasksp), donorp = NULL);

        m_mergesSinceRescore++;

        // Do an expensive check, confirm we haven't botched the CP
        // updates.
        if (m_slowAsserts) partCheckCriticalPaths(m_mtasksp);

        // Finally, make new sibling pairs as needed:
        //  - prereqs and postreqs of recipientp
        //  - prereqs of recipientp's postreqs
        //  - postreqs of recipientp's prereqs
        // Note that this depends on the updated critical paths (above).
        siblingPairFromRelatives(GraphWay::REVERSE, recipientp, true);
        siblingPairFromRelatives(GraphWay::FORWARD, recipientp, true);
        unsigned edges = 0;
        for (V3GraphEdge* edgep = recipientp->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            LogicMTask* postreqp = dynamic_cast<LogicMTask*>(edgep->top());
            siblingPairFromRelatives(GraphWay::REVERSE, postreqp, false);
            edges++;
            if (edges > PART_SIBLING_EDGE_LIMIT) break;
        }
        edges = 0;
        for (V3GraphEdge* edgep = recipientp->inBeginp();
             edgep; edgep = edgep->inNextp()) {
            LogicMTask* prereqp = dynamic_cast<LogicMTask*>(edgep->fromp());
            siblingPairFromRelatives(GraphWay::FORWARD, prereqp, false);
            edges++;
            if (edges > PART_SIBLING_EDGE_LIMIT) break;
        }
    }

    void doRescore() {
        // During rescore, we know that graph isn't changing, so allow
        // the critPathCost*Without() routines to cache some data in
        // each LogicMTask. This is just an optimization, things should
        // behave identically without the caching (just slower)

        m_sb.rescore();
        UINFO(6, "Did rescore. Merges since previous = "
              << m_mergesSinceRescore << endl);

        m_mergesSinceRescore = 0;
        m_scoreLimitBeforeRescore = 0xffffffff;
    }

    static uint32_t mergeCandidateScore(const MergeCandidate* pairp) {
        const MTaskEdge* edgep = dynamic_cast<const MTaskEdge*>(pairp);
        if (edgep) {
            // The '1 +' favors merging a SiblingMC over an otherwise-
            // equal-scoring MTaskEdge. The comment on selfTest() talks
            // about why.
            return 1 + edgeScore(edgep);
        }
        const SiblingMC* sibsp = dynamic_cast<const SiblingMC*>(pairp);
        if (sibsp) {
            return siblingScore(sibsp);
        }
        v3fatalSrc("Failed to cast pairp to either MTaskEdge or SiblingMC in mergeCandidateScore");
        return 0;
    }

    static uint32_t siblingScore(const SiblingMC* sibsp) {
        LogicMTask* ap = sibsp->ap();
        LogicMTask* bp = sibsp->bp();
        uint32_t mergedCpCostFwd = std::max(ap->critPathCost(GraphWay::FORWARD),
                                            bp->critPathCost(GraphWay::FORWARD));
        uint32_t mergedCpCostRev = std::max(ap->critPathCost(GraphWay::REVERSE),
                                            bp->critPathCost(GraphWay::REVERSE));
        return mergedCpCostRev + mergedCpCostFwd
            + LogicMTask::stepCost(ap->cost() + bp->cost());
    }

    static uint32_t edgeScore(const V3GraphEdge* edgep) {
        // Score this edge. Lower is better. The score is the new local CP
        // length if we merge these mtasks.  ("Local" means the longest
        // critical path running through the merged node.)
        LogicMTask* top = dynamic_cast<LogicMTask*>(edgep->top());
        LogicMTask* fromp = dynamic_cast<LogicMTask*>(edgep->fromp());
        uint32_t mergedCpCostFwd = std::max
            (fromp->critPathCost(GraphWay::FORWARD),
             top->critPathCostWithout(GraphWay::FORWARD, edgep));
        uint32_t mergedCpCostRev = std::max
            (fromp->critPathCostWithout(GraphWay::REVERSE, edgep),
             top->critPathCost(GraphWay::REVERSE));
        return mergedCpCostRev + mergedCpCostFwd
            + LogicMTask::stepCost(fromp->cost() + top->cost());
    }

    void makeSiblingMC(LogicMTask* ap, LogicMTask *bp) {
        SiblingMC newSibs(ap, bp);
        std::pair<SibSet::iterator, bool> insertResult = m_pairs.insert(newSibs);
        if (insertResult.second) {
            const SiblingMC* newSibsp = &(*insertResult.first);
            m_mtask2sibs[ap].insert(newSibsp);
            m_mtask2sibs[bp].insert(newSibsp);
            m_sb.addElem(newSibsp);
        } else if (m_slowAsserts) {
            // It's fine if we already have this SiblingMC, we may have
            // created it earlier. Just confirm that we have associated data.
            UASSERT_OBJ(m_mtask2sibs.find(ap) != m_mtask2sibs.end(), ap,
                        "Sibling not found");
            UASSERT_OBJ(m_mtask2sibs.find(bp) != m_mtask2sibs.end(), bp,
                        "Sibling not found");
            bool found = false;
            for (SibpSet::iterator it = m_mtask2sibs[ap].begin();
                 it != m_mtask2sibs[ap].end(); ++it) {
                const SiblingMC* sibsp = *it;
                UASSERT_OBJ(!(!sibsp->removedFromSb() && !m_sb.contains(sibsp)), ap,
                            "One sibling must be the one we collided with");
                if (   (sibsp->ap() == ap && sibsp->bp() == bp)
                    || (sibsp->bp() == ap && sibsp->ap() == bp))
                    found = true;
            }
            UASSERT_OBJ(found, ap, "Sibling not found");
        }
    }

    static const GraphWay* s_shortestWaywardCpInclusiveWay;
    static int shortestWaywardCpInclusive(const void* vap, const void* vbp) {
        const GraphWay* wp = s_shortestWaywardCpInclusiveWay;
        const LogicMTask* ap = *reinterpret_cast<const LogicMTask* const *>(vap);
        const LogicMTask* bp = *reinterpret_cast<const LogicMTask* const *>(vbp);
        uint32_t aCp = ap->critPathCost(*wp) + ap->stepCost();
        uint32_t bCp = bp->critPathCost(*wp) + bp->stepCost();
        if (aCp < bCp) { return -1; }
        if (aCp > bCp) { return 1; }
        if (ap->id() < bp->id()) { return -1; }
        if (ap->id() > bp->id()) { return 1; }
        return 0;
    }

    void siblingPairFromRelatives(GraphWay way, V3GraphVertex* mtaskp,
                                  bool exhaustive) {
        std::vector<LogicMTask*> shortestPrereqs;

        for (V3GraphEdge* edgep = mtaskp->beginp(way);
             edgep; edgep = edgep->nextp(way)) {
            LogicMTask* prereqp = dynamic_cast<LogicMTask*>(edgep->furtherp(way));
            shortestPrereqs.push_back(prereqp);
            // Prevent nodes with huge numbers of edges from massively
            // slowing down the partitioner:
            if (shortestPrereqs.size() > PART_SIBLING_EDGE_LIMIT) break;
        }

        if (shortestPrereqs.empty()) return;

        // qsort_r would be nice here, but it isn't portable
        s_shortestWaywardCpInclusiveWay = &way;
        qsort(&shortestPrereqs[0], shortestPrereqs.size(),
              sizeof(LogicMTask*), &shortestWaywardCpInclusive);

        // Don't make all NxN/2 possible pairs of prereqs, that's a lot
        // to cart around. Just make a few pairs.
        std::vector<LogicMTask*>::iterator it = shortestPrereqs.begin();
        for (unsigned i = 0; exhaustive || (i < 3); ++i) {
            if (it == shortestPrereqs.end()) break;
            LogicMTask* ap = *(it++);
            if (it == shortestPrereqs.end()) break;
            LogicMTask* bp = *(it++);
            makeSiblingMC(ap, bp);
        }
    }

    // SELF TESTS

    // This is a performance test, its intent is to demonstrate that the
    // partitioner doesn't run on this chain in N^2 time or worse. Overall
    // runtime should be N*log(N) for a chain-shaped graph.
    //
    static void selfTestChain() {
        vluint64_t usecsSmall = partitionChainUsecs(5);
        vluint64_t usecsLarge = partitionChainUsecs(500);
        // Large input is 50x bigger than small input.
        // Its runtime should be about 10x longer -- not about 2500x longer
        // or worse which would suggest N^2 scaling or worse.
        UASSERT(usecsLarge < (usecsSmall * 1500),
                "selfTestChain() took longer than expected. Small input runtime = "
                <<usecsSmall<<", large input runtime = "<<usecsLarge);
    }

    static vluint64_t partitionChainUsecs(unsigned chain_len) {
        // NOTE: To get a dot file run with --debugi-V3Partition 4 or more.
        vluint64_t startUsecs = V3Os::timeUsecs();
        V3Graph mtasks;
        LogicMTask* lastp = NULL;
        for (unsigned i=0; i<chain_len; ++i) {
            LogicMTask* mtp = new LogicMTask(&mtasks, NULL);
            mtp->setCost(1);
            if (lastp) {
                new MTaskEdge(&mtasks, lastp, mtp, 1);
            }
            lastp = mtp;
        }
        partInitCriticalPaths(&mtasks);

        // Since slowAsserts mode is *expected* to cause N^2 runtime, and the
        // intent of this test is to demonstrate better-than-N^2 runtime, disable
        // slowAsserts.
        PartContraction ec(&mtasks,
                           // Any CP limit >chain_len should work:
                           chain_len * 2,
                           false /* slowAsserts */);
        ec.go();

        PartParallelismEst check(&mtasks);
        check.traverse();

        vluint64_t endUsecs = V3Os::timeUsecs();
        vluint64_t elapsedUsecs = endUsecs - startUsecs;

        if (debug()>=6) {
            UINFO(0, "Chain self test stats:\n");
            check.debugReport();
            UINFO(0, "Elapsed usecs = " << elapsedUsecs << "\n");
        }

        // All vertices should merge into one
        UASSERT_SELFTEST(size_t, check.vertexCount(), 1);
        return elapsedUsecs;
    }

    // This test defends against a particular failure mode that the
    // partitioner exhibited during development:
    //
    // At one time, the partitioner consistently favored edge-merges over
    // equal-scoring sibling merges. Every edge and sibling merge in this
    // test starts out with an equal score. If you only do edge-merges, all
    // possible merges will continue to have equal score as the center node
    // grows and grows. Soon the critical path budget is exhausted by a
    // large center node, and we still have many small leaf nodes -- it's
    // literally the worst partition possible.
    //
    // Now, instead, the partitioner gives slight favoritism to sibling
    // merges in the event that scores are tied. This is better for the
    // test and also real designs.
    static void selfTestX() {
        // NOTE: To get a dot file run with --debugi-V3Partition 4 or more.
        V3Graph mtasks;
        LogicMTask* center = new LogicMTask(&mtasks, NULL);
        center->setCost(1);
        unsigned i;
        for (i=0; i<50; ++i) {
            LogicMTask* mtp = new LogicMTask(&mtasks, NULL);
            mtp->setCost(1);
            // Edge from every input -> center
            new MTaskEdge(&mtasks, mtp, center, 1);
        }
        for (i=0; i<50; ++i) {
            LogicMTask* mtp = new LogicMTask(&mtasks, NULL);
            mtp->setCost(1);
            // Edge from center -> every output
            new MTaskEdge(&mtasks, center, mtp, 1);
        }

        partInitCriticalPaths(&mtasks);
        PartContraction(&mtasks, 20, true).go();

        PartParallelismEst check(&mtasks);
        check.traverse();

        // Checking exact values here is maybe overly precise.  What we're
        // mostly looking for is a healthy reduction in the number of
        // mtasks.
        if (debug()>=5) {
            UINFO(0, "X self test stats:\n");
            check.debugReport();
        }
        UASSERT_SELFTEST(uint32_t, check.longestCritPathCost(), 19);
        UASSERT_SELFTEST(uint32_t, check.totalGraphCost(), 101);
        UASSERT_SELFTEST(uint32_t, check.vertexCount(), 14);
        UASSERT_SELFTEST(uint32_t, check.edgeCount(), 13);
    }
public:
    static void selfTest() {
        selfTestX();
        selfTestChain();
    }

private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(PartContraction);
};

const GraphWay* PartContraction::s_shortestWaywardCpInclusiveWay = NULL;

//######################################################################
// DpiImportCallVisitor

// Scan node, indicate whether it contains a call to a DPI imported
// routine.
class DpiImportCallVisitor : public AstNVisitor {
private:
    bool m_hasDpiHazard;  // Found a DPI import call.
    bool m_tracingCall;  // Iterating into a CCall to a CFunc
    // METHODS
    VL_DEBUG_FUNC;

    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        if (!m_tracingCall) return;
        m_tracingCall = false;
        if (nodep->dpiImportWrapper()) {
            if (nodep->pure() ? !v3Global.opt.threadsDpiPure()
                : !v3Global.opt.threadsDpiUnpure()) {
                m_hasDpiHazard = true;
            }
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCCall* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Enter the function and trace it
        m_tracingCall = true;
        iterate(nodep->funcp());
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit DpiImportCallVisitor(AstNode* nodep)
        : m_hasDpiHazard(false)
        , m_tracingCall(false) {
        iterate(nodep);
    }
    bool hasDpiHazard() const { return m_hasDpiHazard; }
    virtual ~DpiImportCallVisitor() {}

private:
    VL_UNCOPYABLE(DpiImportCallVisitor);
};

//######################################################################
// PartFixDataHazards

// Fix data hazards in the partition graph.
//
// The fine-grained graph from V3Order may contain data hazards which are
// not a problem for serial mode, but which would be a problem in parallel
// mode.
//
// There are basically two classes: unordered pairs of writes, and
// unordered write-read pairs. We fix both here, with a combination of
// MTask-merges and new edges to ensure no such unordered pairs remain.
//
// ABOUT UNORDERED WRITE-WRITE PAIRS
//
//   The V3Order dependency graph treats these as unordered events:
//
//    a)  sig[15:8] = stuff;
//          ...
//    b)  sig[7:0]  = other_stuff;
//
//   Seems OK right? They are writes to disjoint bits of the same
//   signal. They can run in either order, in serial mode, and the result
//   will be the same.
//
//   The resulting C code for each of this isn't a pure write, it's
//   actually an R-M-W sequence:
//
//    a)  sig = (sig & 0xff)   | (0xff00 & (stuff << 8));
//          ...
//    b)  sig = (sig & 0xff00) | (0xff & other_stuff);
//
//   In serial mode, order doesn't matter so long as these run serially.
//   In parallel mode, we must serialize these RMW's to avoid a race.
//
//   We don't actually check here if each write would involve an R-M-W, we
//   just assume that it would. If this routine ever causes a drastic
//   increase in critical path, it could be optimized to make a better
//   prediction (with all the risk that word implies!) about whether a
//   given write is likely to turn into an R-M-W.
//
// ABOUT UNORDERED WRITE-READ PAIRS
//
//   If we don't put unordered write-read pairs into some order at verilation
//   time, we risk a runtime race.
//
//   How do such unordered writer/reader pairs happen? Here's a partial list
//   of scenarios:
//
//   Case 1: Circular logic
//
//     If the design has circular logic, V3Order has by now generated some
//     dependency cycles, and also cut some of the edges to make it
//     acyclic.
//
//     For serial mode, that was fine. We can break logic circles at an
//     arbitrary point. At runtime, we'll repeat the _eval() until no
//     changes are detected, which papers over the discarded dependency.
//
//     For parallel mode, this situation can lead to unordered reads and
//     writes of the same variable, causing a data race. For example if the
//     original code is this:
//
//       assign b = b | a << 2;
//       assign out = b;
//
//     ... there's originally a dependency edge which records that 'b'
//     depends on the first assign. V3Order may cut this edge, making the
//     statements unordered. In serial mode that's fine, they can run in
//     either order. In parallel mode it's a reader/writer race.
//
//   Case 2: Race Condition in Verilog Sources
//
//     If the input has races, eg. blocking assignments in always blocks
//     that share variables, the graph at this point will contain unordered
//     writes and reads (or unordered write-write pairs) reflecting that.
//
//   Case 3: Interesting V3Order Behavior
//
//     There's code in V3Order that explicitly avoids making a dependency
//     edge from a clock-gater signal to the logic node that produces the
//     clock signal. This leads to unordered reader/writer pairs in
//     parallel mode.
//
class PartFixDataHazards {
private:
    // TYPES
    typedef std::set<LogicMTask*, MTaskIdLessThan> LogicMTaskSet;
    typedef std::map<uint32_t/*rank*/, LogicMTaskSet> TasksByRank;
    typedef std::set<const OrderVarStdVertex*, OrderByPtrId&> OvvSet;
    typedef vl_unordered_map<const OrderLogicVertex*, LogicMTask*> Olv2MTaskMap;

    // MEMBERS
    V3Graph* m_mtasksp;  // Mtask graph
    Olv2MTaskMap m_olv2mtask;  // Map OrderLogicVertex to LogicMTask who wraps it
    unsigned m_mergesDone;  // Number of MTasks merged. For stats only.
public:
    // CONSTRUCTORs
    explicit PartFixDataHazards(V3Graph* mtasksp)
        : m_mtasksp(mtasksp), m_mergesDone(0) {}
    // METHODS
private:
    void findAdjacentTasks(OvvSet::iterator ovvIt, TasksByRank* tasksByRankp) {
        // Find all writer tasks for this variable, group by rank.
        for (V3GraphEdge* edgep = (*ovvIt)->inBeginp();
             edgep; edgep = edgep->inNextp()) {
            OrderLogicVertex* logicp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            if (!logicp) continue;
            if (logicp->domainp()->hasInitial()
                || logicp->domainp()->hasSettle()) continue;
            LogicMTask* writerMtaskp = m_olv2mtask.at(logicp);
            (*tasksByRankp)[writerMtaskp->rank()].insert(writerMtaskp);
        }
        // Find all reader tasks for this variable, group by rank.
        for (V3GraphEdge* edgep = (*ovvIt)->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            OrderLogicVertex* logicp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            if (!logicp) continue;
            if (logicp->domainp()->hasInitial()
                || logicp->domainp()->hasSettle()) continue;
            LogicMTask* readerMtaskp = m_olv2mtask.at(logicp);
            (*tasksByRankp)[readerMtaskp->rank()].insert(readerMtaskp);
        }
    }
    void mergeSameRankTasks(TasksByRank* tasksByRankp) {
        LogicMTask* lastMergedp = NULL;
        for (TasksByRank::iterator rankIt = tasksByRankp->begin();
             rankIt != tasksByRankp->end(); ++rankIt) {
            // Find the largest node at this rank, merge into it.  (If we
            // happen to find a huge node, this saves time in
            // partMergeEdgesFrom() versus merging into an arbitrary node.)
            LogicMTask* mergedp = NULL;
            for (LogicMTaskSet::iterator it = rankIt->second.begin();
                 it != rankIt->second.end(); ++it) {
                LogicMTask* mtaskp = *it;
                if (mergedp) {
                    if (mergedp->cost() < mtaskp->cost()) {
                        mergedp = mtaskp;
                    }
                } else {
                    mergedp = mtaskp;
                }
            }
            rankIt->second.erase(mergedp);

            while (!rankIt->second.empty()) {
                LogicMTaskSet::iterator begin = rankIt->second.begin();
                LogicMTask* donorp = *begin;
                UASSERT_OBJ(donorp != mergedp, donorp, "Donor can't be merged edge");
                rankIt->second.erase(begin);
                // Merge donorp into mergedp.
                // Fix up the map, so donor's OLVs map to mergedp
                for (LogicMTask::VxList::const_iterator tmvit =
                         donorp->vertexListp()->begin();
                     tmvit != donorp->vertexListp()->end(); ++tmvit) {
                    MTaskMoveVertex* tmvp = *tmvit;
                    OrderLogicVertex* logicp = tmvp->logicp();
                    if (logicp) m_olv2mtask[logicp] = mergedp;
                }
                // Move all vertices from donorp to mergedp
                mergedp->moveAllVerticesFrom(donorp);
                // Move edges from donorp to recipientp
                partMergeEdgesFrom(m_mtasksp, mergedp, donorp, NULL);
                // Remove donorp from the graph
                VL_DO_DANGLING(donorp->unlinkDelete(m_mtasksp), donorp);
                m_mergesDone++;
            }

            if (lastMergedp) {
                UASSERT_OBJ(lastMergedp->rank() < mergedp->rank(), mergedp,
                            "Merging must be on lower rank");
                if (!lastMergedp->hasRelative(GraphWay::FORWARD, mergedp)) {
                    new MTaskEdge(m_mtasksp, lastMergedp, mergedp, 1);
                }
            }
            lastMergedp = mergedp;
        }
    }
    bool hasDpiHazard(LogicMTask* mtaskp) {
        for (LogicMTask::VxList::const_iterator it = mtaskp->vertexListp()->begin();
             it != mtaskp->vertexListp()->end(); ++it) {
            if (!(*it)->logicp()) continue;
            AstNode* nodep = (*it)->logicp()->nodep();
            // NOTE: We don't handle DPI exports. If testbench code calls a
            // DPI-exported function at any time during eval() we may have
            // a data hazard. (Likewise in non-threaded mode if an export
            // messes with an ordered variable we're broken.)

            // Find all calls to DPI-imported functions, we can put those
            // into a serial order at least. That should solve the most
            // likely DPI-related data hazards.
            if (DpiImportCallVisitor(nodep).hasDpiHazard()) {
                return true;
            }
        }
        return false;
    }
public:
    void go() {
        vluint64_t startUsecs = 0;
        if (debug() >= 3) startUsecs = V3Os::timeUsecs();

        // Build an OLV->mtask map and a set of OVVs
        OrderByPtrId ovvOrder;
        OvvSet ovvSet(ovvOrder);
        // OVV's which wrap systemC vars will be handled slightly specially
        OvvSet ovvSetSystemC(ovvOrder);

        for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(vxp);
            // Should be only one MTaskMoveVertex in each mtask at this
            // stage, but whatever, write it as a loop:
            for (LogicMTask::VxList::const_iterator it
                     = mtaskp->vertexListp()->begin();
                 it != mtaskp->vertexListp()->end(); ++it) {
                MTaskMoveVertex* tmvp = *it;
                if (OrderLogicVertex* logicp = tmvp->logicp()) {
                    m_olv2mtask[logicp] = mtaskp;
                    // Look at downstream vars.
                    for (V3GraphEdge *edgep = logicp->outBeginp();
                         edgep; edgep = edgep->outNextp()) {
                        // Only consider OrderVarStdVertex which reflects
                        // an actual lvalue assignment; the others do not.
                        OrderVarStdVertex* ovvp
                            = dynamic_cast<OrderVarStdVertex*>(edgep->top());
                        if (!ovvp) continue;
                        if (ovvp->varScp()->varp()->isSc()) {
                            ovvSetSystemC.insert(ovvp);
                        } else {
                            ovvSet.insert(ovvp);
                        }
                    }
                }
            }
        }

        // Rank the graph.
        // DGS is faster than V3GraphAlg's recursive rank, in the worst
        // cases where the recursive rank must pass through the same node
        // many times. (We saw 22s for DGS vs. 500s for recursive rank on
        // one large design.)
        {
            GraphStreamUnordered serialize(m_mtasksp);
            const V3GraphVertex* vertexp;
            while ((vertexp = serialize.nextp())) {
                uint32_t rank = 0;
                for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep;
                     edgep = edgep->inNextp()) {
                    rank = std::max(edgep->fromp()->rank() + 1, rank);
                }
                const_cast<V3GraphVertex*>(vertexp)->rank(rank);
            }
        }

        // For each OrderVarVertex, look at its writer and reader mtasks.
        //
        // If there's a set of writers and readers at the same rank, we
        // know these are unordered with respect to one another, so merge
        // those mtasks all together.
        //
        // At this point, we have at most one merged mtask per rank (for a
        // given OVV.) Create edges across these remaining mtasks to ensure
        // they run in serial order (going along with the existing ranks.)
        //
        // NOTE: we don't update the CP's stored in the LogicMTasks to
        // reflect the changes we make to the graph. That's OK, as we
        // haven't yet initialized CPs when we call this routine.
        for (OvvSet::iterator ovvit = ovvSet.begin();
             ovvit != ovvSet.end(); ++ovvit) {
            // Build a set of mtasks, per rank, which access this var.
            // Within a rank, sort by MTaskID to avoid nondeterminism.
            TasksByRank tasksByRank;

            // Find all reader and writer tasks for this variable, add to
            // tasksByRank.
            findAdjacentTasks(ovvit, &tasksByRank);

            // Merge all writer and reader tasks from same rank together.
            //
            // NOTE: Strictly speaking, we don't need to merge all the
            // readers together. That may lead to extra serialization. The
            // least amount of ordering we could impose here would be to
            // merge all writers at a given rank together; then make edges
            // from the merged writer node to each reader node at the same
            // rank; and then from each reader node to the merged writer at
            // the next rank.
            //
            // Whereas, merging all readers and writers at the same rank
            // together is "the simplest thing that could possibly work"
            // and it seems to.  It also creates fairly few edges. We don't
            // want to create tons of edges here, doing so is not nice to
            // the main edge contraction pass.
            mergeSameRankTasks(&tasksByRank);
        }

        // Handle SystemC vars just a little differently. Instead of
        // treating each var as an independent entity, and serializing
        // writes to that one var, we treat ALL systemC vars as a single
        // entity and serialize writes (and, conservatively, reads) across
        // all of them.
        //
        // Reasoning: writing a systemC var actually turns into a call to a
        // var.write() method, which under the hood is accessing some data
        // structure that's shared by many SC vars. It's not thread safe.
        //
        // Hopefully we only have a few SC vars -- top level ports, probably.
        {
            TasksByRank tasksByRank;
            for (OvvSet::iterator ovvit = ovvSetSystemC.begin();
                 ovvit != ovvSetSystemC.end(); ++ovvit) {
                findAdjacentTasks(ovvit, &tasksByRank);
            }
            mergeSameRankTasks(&tasksByRank);
        }

        // Handle nodes containing DPI calls, we want to serialize those
        // by default unless user gave --threads-dpi-concurrent.
        // Same basic strategy as above to serialize access to SC vars.
        if (!v3Global.opt.threadsDpiPure() || !v3Global.opt.threadsDpiUnpure()) {
            TasksByRank tasksByRank;
            for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp();
                 vxp; vxp = vxp->verticesNextp()) {
                LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(vxp);
                if (hasDpiHazard(mtaskp)) {
                    tasksByRank[vxp->rank()].insert(mtaskp);
                }
            }
            mergeSameRankTasks(&tasksByRank);
        }

        UINFO(4, "PartFixDataHazards() merged "<<m_mergesDone
              <<" pairs of nodes in "<<(V3Os::timeUsecs() - startUsecs)
              <<" usecs.\n");
    }

private:
    VL_UNCOPYABLE(PartFixDataHazards);
    VL_DEBUG_FUNC;
};


//######################################################################
// PartPackMTasks

// Statically pack tasks into threads.
//
// The simplest thing that could possibly work would be to assume that our
// predictions of task runtimes are precise, and that every thread will
// make progress at an equal rate. Simulate a single "clock", pack the the
// highest priority ready task into whatever thread becomes ready earliest,
// repeating until no tasks remain.
//
// That doesn't work well, as our predictions of task runtimes have wide
// error bars (+/- 60% is typical.)
//
// So be a little more clever: let each task have a different end time,
// depending on which thread is looking. Be a little bit pessimistic when
// thread A checks the end time of an mtask running on thread B. This extra
// "padding" avoids tight "layovers" at cross-thread dependencies.
class PartPackMTasks {
private:
    // TYPES
    struct MTaskState {
        uint32_t completionTime;  // Estimated time this mtask will complete
    };
    struct MTaskCmp {
        bool operator() (const ExecMTask* ap, ExecMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

    // MEMBERS
    V3Graph* m_mtasksp;  // Mtask graph
    uint32_t m_nThreads;  // Number of threads
    uint32_t m_sandbagNumerator;  // Numerator padding for est runtime
    uint32_t m_sandbagDenom;  // Denomerator padding for est runtime

    typedef vl_unordered_map<const ExecMTask*, MTaskState> MTaskStateMap;
    MTaskStateMap m_mtaskState;  // State for each mtask.

    MTaskCmp m_mtaskCmp;  // Comparison functor
    typedef std::set<ExecMTask*, MTaskCmp&> ReadyMTasks;
    ReadyMTasks m_ready;  // MTasks ready to be assigned next; all their
    //                    // dependencies are already assigned.

    typedef std::vector<ExecMTask*> MTaskVec;
    MTaskVec m_prevMTask;  // Previous mtask scheduled to each thread.
    std::vector<uint32_t> m_busyUntil;  // Time each thread is occupied until

public:
    // CONSTRUCTORS
    explicit PartPackMTasks(V3Graph* mtasksp,
                            uint32_t nThreads = v3Global.opt.threads(),
                            unsigned sandbagNumerator = 30,
                            unsigned sandbagDenom = 100)
        : m_mtasksp(mtasksp)
        , m_nThreads(nThreads)
        , m_sandbagNumerator(sandbagNumerator)
        , m_sandbagDenom(sandbagDenom)
        , m_ready(m_mtaskCmp) {}
    ~PartPackMTasks() {}

    // METHODS
    uint32_t completionTime(const ExecMTask* mtaskp, uint32_t thread) {
        const MTaskState& state = m_mtaskState[mtaskp];
        UASSERT(mtaskp->thread() != 0xffffffff, "Mtask should have assigned thread");
        if (thread == mtaskp->thread()) {
            // No overhead on native thread
            return state.completionTime;
        }

        // Add some padding to the estimated runtime when looking from
        // another thread
        uint32_t sandbaggedEndTime = state.completionTime
            + (m_sandbagNumerator * mtaskp->cost()) / m_sandbagDenom;

        // If task B is packed after task A on thread 0, don't let thread 1
        // think that A finishes later than thread 0 thinks that B
        // finishes, otherwise we get priority inversions and fail the self
        // test.
        if (mtaskp->packNextp()) {
            uint32_t successorEndTime
                = completionTime(mtaskp->packNextp(), mtaskp->thread());
            if ((sandbaggedEndTime >= successorEndTime)
                && (successorEndTime > 1)) {
                sandbaggedEndTime = successorEndTime - 1;
            }
        }

        UINFO(6, "Sandbagged end time for "<<mtaskp->name()
              <<" on th "<<thread<<" = "<<sandbaggedEndTime<<endl);
        return sandbaggedEndTime;
    }

    void setCompletionTime(ExecMTask* mtaskp, uint32_t time) {
        MTaskState& state = m_mtaskState[mtaskp];
        state.completionTime = time;
    }

    void go() {
        // Build initial ready list
        for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            ExecMTask* mtaskp = dynamic_cast<ExecMTask*>(vxp);
            if (vxp->inEmpty()) m_ready.insert(mtaskp);
        }

        m_prevMTask.clear();
        m_prevMTask.resize(m_nThreads);
        m_busyUntil.clear();
        m_busyUntil.resize(m_nThreads);

        while (!m_ready.empty()) {
            // For each task in the ready set, compute when it might start
            // on each thread (in that thread's local time frame.)
            uint32_t bestTime = 0xffffffff;
            uint32_t bestTh = 0;
            ExecMTask* bestMtaskp = NULL;
            for (uint32_t th = 0; th < m_nThreads; ++th) {
                for (ReadyMTasks::iterator taskIt = m_ready.begin();
                     taskIt != m_ready.end(); ++taskIt) {
                    uint32_t timeBegin = m_busyUntil[th];
                    if (timeBegin > bestTime) {
                        UINFO(6, "th "<<th<<" busy until "<<timeBegin
                              <<", later than bestTime "<<bestTime
                              <<", skipping thread.\n");
                        break;
                    }
                    ExecMTask* taskp = *taskIt;
                    for (V3GraphEdge* edgep = taskp->inBeginp();
                         edgep; edgep = edgep->inNextp()) {
                        ExecMTask* priorp
                            = dynamic_cast<ExecMTask*>(edgep->fromp());
                        uint32_t priorEndTime = completionTime(priorp, th);
                        if (priorEndTime > timeBegin) {
                            timeBegin = priorEndTime;
                        }
                    }
                    UINFO(6, "Task "<<taskp->name()
                          <<" start at "<<timeBegin
                          <<" on thread "<<th<<endl);
                    if ((timeBegin < bestTime)
                        || ((timeBegin == bestTime)
                            && bestMtaskp  // Redundant, but appeases static analysis tools
                            && (taskp->priority() > bestMtaskp->priority()))) {
                        bestTime = timeBegin;
                        bestTh = th;
                        bestMtaskp = taskp;
                    }
                }
            }

            if (!bestMtaskp) v3fatalSrc("Should have found some task");
            UINFO(6, "Will schedule "<<bestMtaskp->name()
                  <<" onto thread "<<bestTh<<endl);
            uint32_t bestEndTime = bestTime + bestMtaskp->cost();
            setCompletionTime(bestMtaskp, bestEndTime);

            // Update the ready list
            size_t erased = m_ready.erase(bestMtaskp);
            UASSERT_OBJ(erased > 0, bestMtaskp, "Should have erased something?");
            for (V3GraphEdge* edgeOutp = bestMtaskp->outBeginp();
                 edgeOutp; edgeOutp = edgeOutp->outNextp()) {
                ExecMTask* nextp = dynamic_cast<ExecMTask*>(edgeOutp->top());

                UASSERT(nextp->thread() == 0xffffffff,
                        "Tasks after one being assigned should not be assigned yet");
                // They also should not be ready yet, since they only now
                // may become ready
                UASSERT_OBJ(m_ready.find(nextp) == m_ready.end(), nextp,
                            "Tasks after one being assigned should not be ready");
                bool isReady = true;
                for (V3GraphEdge* edgeInp = nextp->inBeginp();
                     edgeInp; edgeInp = edgeInp->inNextp()) {
                    ExecMTask* priorp = dynamic_cast<ExecMTask*>(edgeInp->fromp());
                    if (priorp == bestMtaskp) continue;
                    if (priorp->thread() == 0xffffffff) {
                        // This prior is not assigned yet
                        isReady = false;
                    }
                }
                if (isReady) {
                    m_ready.insert(nextp);
                    UINFO(6, "Inserted "<<nextp->name()<<" into ready\n");
                }
            }

            // Update the ExecMTask itself
            if (m_prevMTask[bestTh]) {
                m_prevMTask[bestTh]->packNextp(bestMtaskp);
                UINFO(6, "Packing "<<bestMtaskp->name()
                      <<" after "<<m_prevMTask[bestTh]->name()<<endl);
            } else {
                UINFO(6, "Marking "<<bestMtaskp->name()<<" as thread root\n");
                bestMtaskp->threadRoot(true);
            }
            bestMtaskp->thread(bestTh);

            // Update the thread state
            m_prevMTask[bestTh] = bestMtaskp;
            m_busyUntil[bestTh] = bestEndTime;
        }
    }

    // SELF TEST
    static void selfTest() {
        V3Graph graph;
        ExecMTask* t0 = new ExecMTask(&graph, NULL, 0);
        t0->cost(1000);
        t0->priority(1100);
        ExecMTask* t1 = new ExecMTask(&graph, NULL, 1);
        t1->cost(100);
        t1->priority(100);
        ExecMTask* t2 = new ExecMTask(&graph, NULL, 2);
        t2->cost(100);
        t2->priority(100);

        new V3GraphEdge(&graph, t0, t1, 1);
        new V3GraphEdge(&graph, t0, t2, 1);

        PartPackMTasks packer(&graph,
                              2,  // Threads
                              3,  // Sandbag numerator
                              10);  // Sandbag denom
        packer.go();

        UASSERT_SELFTEST(bool, t0->threadRoot(), true);
        UASSERT_SELFTEST(uint32_t, t0->thread(), 0);
        UASSERT_SELFTEST(const void*, t0->packNextp(), t1);

        UASSERT_SELFTEST(uint32_t, t1->thread(), 0);
        UASSERT_SELFTEST(bool, t1->threadRoot(), false);
        UASSERT_SELFTEST(const void*, t1->packNextp(), NULL);

        UASSERT_SELFTEST(uint32_t, t2->thread(), 1);
        UASSERT_SELFTEST(bool, t2->threadRoot(), true);
        UASSERT_SELFTEST(const void*, t2->packNextp(), NULL);

        // On its native thread, we see the actual end time for t0:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t0, 0), 1000);
        // On the other thread, we see a sandbagged end time which does not
        // exceed the t1 end time:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t0, 1), 1099);

        // Actual end time on native thread:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t1, 0), 1100);
        // Sandbagged end time seen on thread 1.  Note it does not compound
        // with t0's sandbagged time; compounding caused trouble in
        // practice.
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t1, 1), 1130);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t2, 0), 1229);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(t2, 1), 1199);
    }

private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(PartPackMTasks);
};

//######################################################################
// V3Partition implementation

void V3Partition::debugMTaskGraphStats(const V3Graph* graphp, const string& stage) {
    if (!debug()) return;

    UINFO(4, "\n");
    UINFO(4, " Stats for "<<stage<<endl);
    uint32_t mtaskCount = 0;
    uint32_t totalCost = 0;
    uint32_t mtaskCostHist[32]; memset(mtaskCostHist, 0, sizeof(mtaskCostHist));

    for (const V3GraphVertex* mtaskp = graphp->verticesBeginp(); mtaskp;
         mtaskp = mtaskp->verticesNextp()) {
        ++mtaskCount;
        uint32_t mtaskCost = dynamic_cast<const AbstractMTask*>(mtaskp)->cost();
        totalCost += mtaskCost;

        unsigned log2Cost = 0;
        while (mtaskCost >>= 1) ++log2Cost;
        UASSERT(log2Cost < 32, "log2Cost overflow in debugMTaskGraphStats");
        ++mtaskCostHist[log2Cost];
    }
    UINFO(4, "  Total mtask cost = "<<totalCost<<"\n");
    UINFO(4, "  Mtask count = "<<mtaskCount<<"\n");
    UINFO(4, "  Avg cost / mtask = "
          << ((mtaskCount > 0)
              ? cvtToStr(totalCost / mtaskCount)
              : "INF!") << "\n");
    UINFO(4, "  Histogram of mtask costs:\n");
    for (unsigned i = 0; i < 32; ++i) {
        if (mtaskCostHist[i]) {
            UINFO(4, "    2^"<<i<<": "<<mtaskCostHist[i]<<endl);
            V3Stats::addStat("MTask graph, "+stage+", mtask cost 2^"
                             +(i<10 ? " ":"")
                             +cvtToStr(i), mtaskCostHist[i]);
        }
    }

    if (mtaskCount < 1000) {
        string filePrefix("ordermv_");
        filePrefix += stage;
        if (debug() >= 4) graphp->dumpDotFilePrefixedAlways(filePrefix);
    }

    // Look only at the cost of each mtask, neglect communication cost.
    // This will show us how much parallelism we expect, assuming cache-miss
    // costs are minor and the cost of running logic is the dominant cost.
    PartParallelismEst vertexParEst(graphp);
    vertexParEst.traverse();
    vertexParEst.statsReport(stage);
    if (debug()>=4) {
        UINFO(0, "\n");
        UINFO(0, "  Parallelism estimate for based on mtask costs:\n");
        vertexParEst.debugReport();
    }
}

// Print a hash of the shape of graphp.  If you are battling
// nondeterminism, this can help to pinpoint where in the pipeline it's
// creeping in.
void V3Partition::hashGraphDebug(const V3Graph* graphp, const char* debugName) {
    // Disabled when there are no nondeterminism issues in flight.
    if (!v3Global.opt.debugNondeterminism()) return;

    vl_unordered_map<const V3GraphVertex*, uint32_t> vx2Id;
    unsigned id = 0;
    for (const V3GraphVertex* vxp = graphp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        vx2Id[vxp] = id++;
    }
    unsigned hash = 0;
    for (const V3GraphVertex* vxp = graphp->verticesBeginp();
         vxp; vxp = vxp->verticesNextp()) {
        for (const V3GraphEdge* edgep = vxp->outBeginp();
             edgep; edgep= edgep->outNextp()) {
            const V3GraphVertex* top = edgep->top();
            hash = vx2Id[top] + 31u * hash;  // The K&R hash function
        }
    }
    UINFO(0, "Hash of shape (not contents) of "<<debugName
          <<" = "<<cvtToStr(hash)<<endl);
}

void V3Partition::setupMTaskDeps(V3Graph* mtasksp, const Vx2MTaskMap* vx2mtaskp) {
    // Look at each mtask
    for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp;
         itp=itp->verticesNextp()) {
        LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(itp);
        const LogicMTask::VxList* vertexListp = mtaskp->vertexListp();

        // For each logic vertex in this mtask, create an mtask-to-mtask
        // edge based on the logic-to-logic edge.
        for (LogicMTask::VxList::const_iterator vit = vertexListp->begin();
             vit != vertexListp->end(); ++vit) {
            for (V3GraphEdge* outp = (*vit)->outBeginp(); outp;
                 outp = outp->outNextp()) {
                UASSERT(outp->weight() > 0, "Mtask not assigned weight");
                const MTaskMoveVertex* top
                    = dynamic_cast<MTaskMoveVertex*>(outp->top());
                UASSERT(top, "MoveVertex not associated to mtask");
                Vx2MTaskMap::const_iterator it = vx2mtaskp->find(top);
                UASSERT(it != vx2mtaskp->end(), "MTask map can't find id");
                LogicMTask* otherMTaskp = it->second;
                UASSERT(otherMTaskp, "NULL other Mtask");
                UASSERT_OBJ(otherMTaskp != mtaskp, mtaskp, "Would create a cycle edge");

                // Don't create redundant edges.
                if (mtaskp->hasRelative(GraphWay::FORWARD, otherMTaskp)) {
                    continue;
                }
                new MTaskEdge(mtasksp, mtaskp, otherMTaskp, 1);
            }
        }
    }
}

void V3Partition::go(V3Graph* mtasksp) {
    // Called by V3Order
    hashGraphDebug(m_fineDepsGraphp, "v3partition initial fine-grained deps");

    // Create the first MTasks. Initially, each MTask just wraps one
    // MTaskMoveVertex. Over time, we'll merge MTasks together and
    // eventually each MTask will wrap a large number of MTaskMoveVertices
    // (and the logic nodes therein.)
    uint32_t totalGraphCost = 0;
    {
        // The V3InstrCount within LogicMTask will set user5 on each AST
        // node, to assert that we never count any node twice.
        AstUser5InUse inUser5;
        Vx2MTaskMap vx2mtask;
        for (V3GraphVertex* vxp = m_fineDepsGraphp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            MTaskMoveVertex* mtmvVxp = dynamic_cast<MTaskMoveVertex*>(vxp);
            UASSERT_OBJ(mtmvVxp, vxp, "Every vertex here should be an MTaskMoveVertex");

            LogicMTask* mtaskp = new LogicMTask(mtasksp, mtmvVxp);
            vx2mtask[mtmvVxp] = mtaskp;

            totalGraphCost += mtaskp->cost();
        }

        // Create the mtask->mtask dep edges based on vertex deps
        setupMTaskDeps(mtasksp, &vx2mtask);
    }

    V3Partition::debugMTaskGraphStats(mtasksp, "initial");

    // For debug: print out the longest critical path.  This allows us to
    // verify that the costs look reasonable, that we aren't combining
    // nodes that should probably be split, etc.
    if (v3Global.opt.dumpTreeLevel(__FILE__) >= 3) {
        LogicMTask::dumpCpFilePrefixed(mtasksp, "cp");
    }

    // Merge nodes that could present data hazards; see comment within.
    {
        PartFixDataHazards(mtasksp).go();
        V3Partition::debugMTaskGraphStats(mtasksp, "hazards");
        hashGraphDebug(mtasksp, "mtasksp after fixDataHazards()");
    }

    // Setup the critical path into and out of each node.
    partInitCriticalPaths(mtasksp);
    hashGraphDebug(mtasksp, "after partInitCriticalPaths()");

    // Order the graph. We know it's already ranked from fixDataHazards()
    // so we don't need to rank it again.
    //
    // On at least some models, ordering the graph here seems to help
    // performance. (Why? Is it just triggering noise in a lucky direction?
    // Is it just as likely to harm results?)
    //
    // More diversity of models that can build with --threads will
    // eventually tell us. For now keep the order() so we don't forget
    // about it, in case it actually helps.  TODO: get more data and maybe
    // remove this later if it doesn't really help.
    mtasksp->orderPreRanked();

    int targetParFactor = v3Global.opt.threads();
    if (targetParFactor < 2) {
        v3fatalSrc("We should not reach V3Partition when --threads <= 1");
    }

    // Set cpLimit to roughly totalGraphCost / nThreads
    //
    // Actually set it a bit lower, by a hardcoded fudge factor. This
    // results in more smaller mtasks, which helps reduce fragmentation
    // when scheduling them.
    unsigned fudgeNumerator = 3;
    unsigned fudgeDenominator = 5;
    uint32_t cpLimit = ((totalGraphCost * fudgeNumerator)
                        / (targetParFactor * fudgeDenominator));
    UINFO(4, "V3Partition set cpLimit = "<<cpLimit<<endl);

    // Merge MTask nodes together, repeatedly, until the CP budget is
    // reached.  Coarsens the graph, usually by several orders of
    // magnitude.
    //
    // Some tests disable this, hence the test on threadsCoarsen().
    // Coarsening is always enabled in production.
    if (v3Global.opt.threadsCoarsen()) {
        PartContraction(mtasksp, cpLimit,
                        // --debugPartition is used by tests
                        // to enable slow assertions.
                        v3Global.opt.debugPartition()).go();
        V3Partition::debugMTaskGraphStats(mtasksp, "contraction");
    }
    {
        mtasksp->removeTransitiveEdges();
        V3Partition::debugMTaskGraphStats(mtasksp, "transitive1");
    }

    // Reassign MTask IDs onto smaller numbers, which should be more stable
    // across small logic changes.  Keep MTask IDs in the same relative
    // order though, otherwise we break CmpLogicMTask for still-existing
    // EdgeSet's that haven't destructed yet.
    {
        typedef std::set<LogicMTask*, LogicMTask::CmpLogicMTask> SortedMTaskSet;
        SortedMTaskSet sorted;
        for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp;
             itp = itp->verticesNextp()) {
            LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(itp);
            sorted.insert(mtaskp);
        }
        uint32_t nextId = 1;
        for (SortedMTaskSet::iterator it = sorted.begin();
             it != sorted.end(); ++it) {
            // We shouldn't perturb the sort order of the set, despite
            // changing the IDs, they should all just remain in the same
            // relative order. Confirm that:
            UASSERT(nextId <= (*it)->id(), "Should only shrink MTaskIDs here");
            UINFO(4, "Reassigning MTask id " << (*it)->id()
                  << " to id " << nextId << "\n");
            (*it)->id(nextId);
            nextId++;
        }
    }

    // Set color to indicate an mtaskId on every underlying MTaskMoveVertex.
    for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp;
         itp = itp->verticesNextp()) {
        LogicMTask* mtaskp = dynamic_cast<LogicMTask*>(itp);
        for (LogicMTask::VxList::const_iterator it
                 = mtaskp->vertexListp()->begin();
             it != mtaskp->vertexListp()->end(); ++it) {
            MTaskMoveVertex* mvertexp = *it;
            mvertexp->color(mtaskp->id());
        }
    }
}

void V3Partition::finalizeCosts(V3Graph* execMTaskGraphp) {
    GraphStreamUnordered ser(execMTaskGraphp, GraphWay::REVERSE);

    while (const V3GraphVertex* vxp = ser.nextp()) {
        ExecMTask* mtp = dynamic_cast<ExecMTask*>(const_cast<V3GraphVertex*>(vxp));
        uint32_t costCount = V3InstrCount::count(mtp->bodyp(), false);
        mtp->cost(costCount);
        mtp->priority(costCount);

        // "Priority" is the critical path from the start of the mtask, to
        // the end of the graph reachable from this mtask.  Given the
        // choice among several ready mtasks, we'll want to start the
        // highest priority one first, so we're always working on the "long
        // pole"
        for (V3GraphEdge* edgep = mtp->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            ExecMTask* followp = dynamic_cast<ExecMTask*>(edgep->top());
            if ((followp->priority() + mtp->cost()) > mtp->priority()) {
                mtp->priority(followp->priority() + mtp->cost());
            }
        }
    }

    // Some MTasks may now have zero cost, eliminate those.
    // (It's common for tasks to shrink to nothing when V3LifePost
    // removes dly assignments.)
    for (V3GraphVertex* vxp = execMTaskGraphp->verticesBeginp(); vxp; ) {
        ExecMTask* mtp = dynamic_cast<ExecMTask*>(vxp);
        vxp = vxp->verticesNextp();  // Advance before delete

        // Don't rely on checking mtp->cost() == 0 to detect an empty task.
        // Our cost-estimating logic is just an estimate. Instead, check
        // the MTaskBody to see if it's empty. That's the source of truth.
        AstMTaskBody* bodyp = mtp->bodyp();
        if (!bodyp->stmtsp()) {  // Kill this empty mtask
            UINFO(6, "Removing zero-cost "<<mtp->name()<<endl);
            for (V3GraphEdge* inp = mtp->inBeginp();
                 inp; inp = inp->inNextp()) {
                for (V3GraphEdge* outp = mtp->outBeginp();
                     outp; outp = outp->outNextp()) {
                    new V3GraphEdge(execMTaskGraphp, inp->fromp(),
                                    outp->top(), 1);
                }
            }
            VL_DO_DANGLING(mtp->unlinkDelete(execMTaskGraphp), mtp);
            // Also remove and delete the AstMTaskBody, otherwise it would
            // keep a dangling pointer to the ExecMTask.
            VL_DO_DANGLING(bodyp->unlinkFrBack()->deleteTree(), bodyp);
        }
    }

    // Removing tasks may cause edges that were formerly non-transitive to
    // become transitive. Also we just created new edges around the removed
    // tasks, which could be transitive. Prune out all transitive edges.
    {
        execMTaskGraphp->removeTransitiveEdges();
        V3Partition::debugMTaskGraphStats(execMTaskGraphp,
                                          "transitive2");
    }

    // Record summary stats for final m_tasks graph.
    // (More verbose stats are available with --debugi-V3Partition >= 3.)
    PartParallelismEst parEst(execMTaskGraphp);
    parEst.traverse();
    parEst.statsReport("final");
    if (debug() >= 3) {
        UINFO(0,"  Final mtask parallelism report:\n");
        parEst.debugReport();
    }
}

void V3Partition::finalize() {
    // Called by Verilator top stage
    AstExecGraph* execGraphp = v3Global.rootp()->execGraphp();
    UASSERT(execGraphp, "Couldn't find AstExecGraph singleton.");

    // Back in V3Order, we partitioned mtasks using provisional cost
    // estimates. However, V3Order precedes some optimizations (notably
    // V3LifePost) that can change the cost of logic within each mtask.
    // Now that logic is final, recompute the cost and priority of each
    // ExecMTask.
    finalizeCosts(execGraphp->mutableDepGraphp());

    // "Pack" the mtasks: statically associate each mtask with a thread,
    // and determine the order in which each thread will runs its mtasks.
    PartPackMTasks(execGraphp->mutableDepGraphp()).go();
}

void V3Partition::selfTest() {
    PartPropagateCpSelfTest::selfTest();
    PartPackMTasks::selfTest();
    PartContraction::selfTest();
}
