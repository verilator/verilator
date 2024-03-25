// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Multi-threaded code partitioning and ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//  Parallel code ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Config.h"
#include "V3ExecGraph.h"
#include "V3File.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3InstrCount.h"
#include "V3List.h"
#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"
#include "V3OrderMoveGraph.h"
#include "V3Os.h"
#include "V3PairingHeap.h"
#include "V3Scoreboard.h"
#include "V3Stats.h"

#include <array>
#include <memory>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class LogicMTask;
class MTaskEdge;
class MergeCandidate;
class SiblingMC;

// ######################################################################
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
// If your vertices are small, the limit (at 26) approaches a no-op.  Hence
// there's basically no cost to applying this limit even when we don't
// expect huge vertices.
//
// If you don't care about partitioner runtime and you want the most
// aggressive partition, set the limit very high.  If you have huge
// vertices, leave this as is.
constexpr unsigned PART_SIBLING_EDGE_LIMIT = 26;

//   PART_STEPPED_COST (defined/undef)
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

// Don't produce more than a certain maximum number of MTasks.  This helps
// the TSP variable sort not to blow up (a concern for some of the tests)
// and we probably don't want a huge number of mTaskGraphp in practice anyway
// (50 to 100 is typical.)
//
// If the user doesn't give one with '--threads-max-mTaskGraphp', we'll set the
// maximum # of MTasks to
//  (# of threads * PART_DEFAULT_MAX_MTASKS_PER_THREAD)
constexpr unsigned PART_DEFAULT_MAX_MTASKS_PER_THREAD = 50;

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
    UASSERT((((cached * 10) <= (actual * 11)) && (cached * 11) >= (actual * 10)),
            "Calculation error in scoring (approximate, may need tweak)");
#else
    UASSERT(cached == actual, "Calculation error in scoring");
#endif
}

//=============================================================================
// We keep MTaskEdge graph edges in a PairingHeap, sorted by score and id

struct EdgeKey final {
    // Node: Structure layout chosen to minimize padding in PairingHeao<*>::Node
    uint64_t m_id;  // Unique ID part of edge score
    uint32_t m_score;  // Score part of ID
    void increase(uint32_t score) {
        UDEBUGONLY(UASSERT(score >= m_score, "Must increase"););
        m_score = score;
    }
    bool operator<(const EdgeKey& other) const {
        // First by Score then by ID
        return m_score < other.m_score || (m_score == other.m_score && m_id < other.m_id);
    }
};

using EdgeHeap = PairingHeap<EdgeKey>;

//######################################################################
// MTask utility classes

struct MergeCandidateKey final {
    // Note: Structure layout chosen to minimize padding in PairingHeao<*>::Node
    uint64_t m_id;  // Unique ID part of edge score
    uint32_t m_score;  // Score part of ID
    bool operator<(const MergeCandidateKey& other) const {
        // First by Score then by ID, but notice that we want minimums using a max-heap, so reverse
        return m_score > other.m_score || (m_score == other.m_score && m_id > other.m_id);
    }
};

using MergeCandidateScoreboard = V3Scoreboard<MergeCandidate, MergeCandidateKey>;

// Information associated with scoreboarding a merge candidate
class MergeCandidate VL_NOT_FINAL : public MergeCandidateScoreboard::Node {
    // Only the known subclasses can create or delete one of these
    friend class SiblingMC;
    friend class MTaskEdge;

    // This structure is extremely hot. To save 8 bytes we pack
    // one bit indicating removedFromSb with the id. To save another
    // 8 bytes by not having a virtual function table, we implement the
    // few polymorphic methods over the two known subclasses explicitly,
    // using another bit of the id to denote the actual subtype.

    // By using the bottom bits for flags, we can still use < to compare IDs without masking.
    // <63:1> Serial number for ordering, <0> subtype (SiblingMC)
    static constexpr uint64_t IS_SIBLING_MASK = 1ULL << 0;
    static constexpr uint64_t ID_INCREMENT = 1ULL << 1;

    bool isSiblingMC() const { return m_key.m_id & IS_SIBLING_MASK; }

    // CONSTRUCTORS
    explicit MergeCandidate(bool isSiblingMC) {
        static uint64_t serial = 0;
        serial += ID_INCREMENT;  // +ID_INCREMENT so doesn't set the special bottom bits
        m_key.m_id = serial | (isSiblingMC * IS_SIBLING_MASK);
    }
    ~MergeCandidate() = default;

public:
    // METHODS
    SiblingMC* toSiblingMC();  // Instead of cast<>/as<>
    MTaskEdge* toMTaskEdge();  // Instead of cast<>/as<>
    bool mergeWouldCreateCycle() const;  // Instead of virtual method

    inline void rescore();
    uint32_t score() const { return m_key.m_score; }

    static MergeCandidate* heapNodeToElem(MergeCandidateScoreboard::Node* nodep) {
        return static_cast<MergeCandidate*>(nodep);
    }
};

static_assert(sizeof(MergeCandidate) == sizeof(MergeCandidateScoreboard::Node),
              "Should not have a vtable");

// A pair of associated LogicMTask's that are merge candidates for sibling
// contraction
class SiblingMC final : public MergeCandidate {
    LogicMTask* const m_ap;
    LogicMTask* const m_bp;

    V3ListLinks<SiblingMC> m_aLinks;  // List links to store instances of this class
    V3ListLinks<SiblingMC> m_bLinks;  // List links to store instances of this class

    V3ListLinks<SiblingMC>& aLinks() { return m_aLinks; }
    V3ListLinks<SiblingMC>& bLinks() { return m_bLinks; }

public:
    // List type to store instances of this class
    using AList = V3List<SiblingMC, &SiblingMC::aLinks>;
    using BList = V3List<SiblingMC, &SiblingMC::bLinks>;

    // CONSTRUCTORS
    SiblingMC(LogicMTask* ap, LogicMTask* bp);
    ~SiblingMC() = default;

    // METHODS
    void unlinkA();
    void unlinkB();

    LogicMTask* ap() const { return m_ap; }
    LogicMTask* bp() const { return m_bp; }
    bool mergeWouldCreateCycle() const;
};

static_assert(!std::is_polymorphic<SiblingMC>::value, "Should not have a vtable");

// GraphEdge for the MTask graph
class MTaskEdge final : public V3GraphEdge, public MergeCandidate {
    VL_RTTI_IMPL(MTaskEdge, V3GraphEdge)
    friend class LogicMTask;
    template <GraphWay::en T_Way>
    friend class PropagateCp;

    // MEMBERS
    // This edge can be in 2 EdgeHeaps, one forward and one reverse. We allocate the heap nodes
    // directly within the edge as they are always required and this makes association cheap.
    std::array<EdgeHeap::Node, GraphWay::NUM_WAYS> m_edgeHeapNode;

public:
    // CONSTRUCTORS
    MTaskEdge(V3Graph* graphp, LogicMTask* fromp, LogicMTask* top, int weight);
    // METHODS
    template <GraphWay::en T_Way>
    inline LogicMTask* furtherMTaskp() const;
    inline LogicMTask* fromMTaskp() const;
    inline LogicMTask* toMTaskp() const;
    bool mergeWouldCreateCycle() const;
    // Following initial assignment of critical paths, clear this MTaskEdge
    // out of the edge-map for each node and reinsert at a new location
    // with updated critical path.
    void resetCriticalPaths();

    uint32_t cachedCp(GraphWay way) const { return m_edgeHeapNode[way].key().m_score; }

    // Convert from the address of the m_edgeHeapNode[way] in an MTaskEdge back to the MTaskEdge
    static const MTaskEdge* toMTaskEdge(GraphWay way, const EdgeHeap::Node* nodep) {
        const size_t offset = VL_OFFSETOF(MTaskEdge, m_edgeHeapNode[way]);
        return reinterpret_cast<const MTaskEdge*>(reinterpret_cast<uintptr_t>(nodep) - offset);
    }

private:
    VL_UNCOPYABLE(MTaskEdge);
};

//=============================================================================
// LogicMTask

class LogicMTask final : public V3GraphVertex {
    VL_RTTI_IMPL(LogicMTask, V3GraphVertex)
    template <GraphWay::en T_Way>
    friend class PropagateCp;

public:
    // TYPES
    struct CmpLogicMTask final {
        bool operator()(const LogicMTask* ap, const LogicMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

private:
    // MEMBERS

    // List of OrderMoveVertex's assigned to this mtask. LogicMTask does not
    // own the OrderMoveVertex objects, we merely keep them in a list here.
    OrderMoveVertex::List m_mVertices;

    // Cost estimate for this LogicMTask, derived from V3InstrCount.
    // In abstract time units.
    uint32_t m_cost = 0;

    // Cost of critical paths going FORWARD from graph-start to the start
    // of this vertex, and also going REVERSE from the end of the graph to
    // the end of the vertex. Same units as m_cost.
    std::array<uint32_t, GraphWay::NUM_WAYS> m_critPathCost;

    const uint32_t m_id;  // Unique LogicMTask ID number
    static uint32_t s_nextId;  // Next ID number to use

    // Count "generations" which are just operations that scan through the
    // graph. We'll mark each node with the last generation that scanned
    // it. We can use this to avoid recursing through the same node twice
    // while searching for a path.
    uint64_t m_generation = 0;

    // Store a set of forward relatives so we can quickly check if we have a given child
    std::unordered_set<LogicMTask*> m_edgeSet;
    // Store the outgoing and incoming edges in a heap sorted by the critical path length
    std::array<EdgeHeap, GraphWay::NUM_WAYS> m_edgeHeap;

    // MTasks for which a SiblingMC exists with 'this' as the higher ID MTask (m_ap in SiblingMC)
    std::set<LogicMTask*> m_siblings;
    // List of SiblingMCs for which this is the higher ID MTask (m_ap in SiblingMC)
    SiblingMC::AList m_aSiblingMCs;
    // List of SiblingMCs for which this is the lower ID MTask (m_bp in SiblingMC)
    SiblingMC::BList m_bSiblingMCs;

public:
    // CONSTRUCTORS
    LogicMTask(V3Graph* graphp, OrderMoveVertex* mVtxp)
        : V3GraphVertex{graphp}
        , m_id{s_nextId++} {
        UASSERT(s_nextId < 0xFFFFFFFFUL, "Too many mTaskGraphp");
        for (uint32_t& item : m_critPathCost) item = 0;
        if (mVtxp) {
            m_mVertices.linkBack(mVtxp);
            if (const OrderLogicVertex* const olvp = mVtxp->logicp()) {
                m_cost += V3InstrCount::count(olvp->nodep(), true);
            }
        }
    }

    // METHODS
    std::set<LogicMTask*>& siblings() { return m_siblings; };
    SiblingMC::AList& aSiblingMCs() { return m_aSiblingMCs; };
    SiblingMC::BList& bSiblingMCs() { return m_bSiblingMCs; };

    OrderMoveVertex::List& vertexList() { return m_mVertices; }
    const OrderMoveVertex::List& vertexList() const { return m_mVertices; }
    void moveAllVerticesFrom(LogicMTask* otherp) {
        m_mVertices.splice(m_mVertices.end(), otherp->vertexList());
        m_cost += otherp->m_cost;
    }
    static uint64_t incGeneration() {
        static uint64_t s_generation = 0;
        ++s_generation;
        return s_generation;
    }

    // Use this instead of pointer-compares to compare LogicMTasks. Avoids
    // nondeterministic output.  Also name mTaskGraphp based on this number in
    // the final C++ output.
    uint32_t id() const { return m_id; }
    // Abstract cost of every logic mtask
    uint32_t cost() const VL_MT_SAFE { return m_cost; }
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

        const uint32_t stepCost = static_cast<uint32_t>(exp(logcost));
        UDEBUGONLY(UASSERT_STATIC(stepCost >= cost, "stepped cost error exceeded"););
        UDEBUGONLY(UASSERT_STATIC(stepCost <= ((cost * 11 / 10)), "stepped cost error exceeded"););
        return stepCost;
#else
        return cost;
#endif
    }

    template <GraphWay::en T_Way>
    void addRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{T_Way};
        constexpr GraphWay inv = way.invert();
        // Add to the edge heap
        LogicMTask* const relativep = edgep->furtherMTaskp<T_Way>();
        // Value is !way cp to this edge
        const uint32_t cp = relativep->stepCost() + relativep->critPathCost(inv);
        //
        m_edgeHeap[way].insert(&edgep->m_edgeHeapNode[way], {relativep->id(), cp});
    }
    template <GraphWay::en T_Way>
    void stealRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{T_Way};
        // Make heap node insertable, ruining the heap it is currently in.
        edgep->m_edgeHeapNode[way].yank();
        // Add the edge as new
        addRelativeEdge<T_Way>(edgep);
    }
    template <GraphWay::en T_Way>
    void removeRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{T_Way};
        // Remove from the edge heap
        m_edgeHeap[way].remove(&edgep->m_edgeHeapNode[way]);
    }

    void addRelativeMTask(LogicMTask* relativep) {
        // Add the relative to connecting edge map
        const bool exits = !m_edgeSet.emplace(relativep).second;
        UDEBUGONLY(UASSERT(!exits, "Adding existing relative"););
    }
    void removeRelativeMTask(LogicMTask* relativep) {
        const size_t removed = m_edgeSet.erase(relativep);
        UDEBUGONLY(UASSERT(removed, "Relative should have been in set"););
    }
    bool hasRelativeMTask(LogicMTask* relativep) const { return m_edgeSet.count(relativep); }

    template <GraphWay::en T_Way>
    void checkRelativesCp() const {
        constexpr GraphWay way{T_Way};
        for (const V3GraphEdge& edge : edges<T_Way>()) {
            const LogicMTask* const relativep
                = static_cast<const LogicMTask*>(edge.furtherp<T_Way>());
            const uint32_t cachedCp = static_cast<const MTaskEdge&>(edge).cachedCp(way);
            const uint32_t cp = relativep->critPathCost(way.invert()) + relativep->stepCost();
            partCheckCachedScoreVsActual(cachedCp, cp);
        }
    }

    string name() const override VL_MT_STABLE {
        // Display forward and reverse critical path costs. This gives a quick
        // read on whether graph partitioning looks reasonable or bad.
        std::ostringstream out;
        out << "mt" << m_id << "." << this << " [b" << m_critPathCost[GraphWay::FORWARD] << " a"
            << m_critPathCost[GraphWay::REVERSE] << " c" << cost();
        return out.str();
    }

    void setCritPathCost(GraphWay way, uint32_t cost) { m_critPathCost[way] = cost; }
    uint32_t critPathCost(GraphWay way) const { return m_critPathCost[way]; }
    template <GraphWay::en T_Way>
    uint32_t critPathCostWithout(const V3GraphEdge* withoutp) const {
        const GraphWay way{T_Way};
        const GraphWay inv = way.invert();
        // Compute the critical path cost wayward to this node, without considering edge
        // 'withoutp'. We need to look at two edges at most, the critical path if that is not via
        // 'withoutp', or the second-worst path, if the critical path is via 'withoutp'.
        UDEBUGONLY(UASSERT(withoutp->furtherp<T_Way>() == this,
                           "In critPathCostWithout(), edge 'withoutp' must further to 'this'"););
        const EdgeHeap& edgeHeap = m_edgeHeap[inv];
        const EdgeHeap::Node* const maxp = edgeHeap.max();
        if (!maxp) return 0;
        if (MTaskEdge::toMTaskEdge(inv, maxp) != withoutp) return maxp->key().m_score;
        const EdgeHeap::Node* const secp = edgeHeap.secondMax();
        if (!secp) return 0;
        return secp->key().m_score;
    }

private:
    static bool pathExistsFromInternal(LogicMTask* fromp, LogicMTask* top,
                                       const V3GraphEdge* excludedEdgep, uint64_t generation) {
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
            < (top->critPathCost(GraphWay::REVERSE) + top->stepCost())) {
            return false;
        }
        if ((fromp->critPathCost(GraphWay::FORWARD) + fromp->stepCost())
            > top->critPathCost(GraphWay::FORWARD)) {
            return false;
        }

        // Recursively look for a path
        for (const V3GraphEdge& follow : fromp->outEdges()) {
            if (&follow == excludedEdgep) continue;
            LogicMTask* const nextp = static_cast<LogicMTask*>(follow.top());
            if (pathExistsFromInternal(nextp, top, nullptr, generation)) return true;
        }
        return false;
    }

    // True if there's a path from 'fromp' to 'top' excluding
    // 'excludedEdgep', false otherwise.
    //
    // 'excludedEdgep' may be nullptr in which case no edge is excluded.  If
    // 'excludedEdgep' is non-nullptr it must connect fromp and top.
    //
    // TODO: consider changing this API to the 'isTransitiveEdge' API
    // used by GraphPathChecker
public:
    static bool pathExistsFrom(LogicMTask* fromp, LogicMTask* top,
                               const V3GraphEdge* excludedEdgep) {
        return pathExistsFromInternal(fromp, top, excludedEdgep, incGeneration());
    }

    static void dumpCpFilePrefixed(const V3Graph& graph, const string& nameComment) {
        const string filename = v3Global.debugFilename(nameComment) + ".txt";
        UINFO(1, "Writing " << filename << endl);
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
        std::ostream* const osp = &(*ofp);  // &* needed to deref unique_ptr
        if (osp->fail()) v3fatalStatic("Can't write " << filename);

        // Find start vertex with longest CP
        const LogicMTask* startp = nullptr;
        for (const V3GraphVertex& vtx : graph.vertices()) {
            const LogicMTask& mtask = static_cast<const LogicMTask&>(vtx);
            if (!startp) {
                startp = &mtask;
                continue;
            }
            if (mtask.cost() + mtask.critPathCost(GraphWay::REVERSE)
                > startp->cost() + startp->critPathCost(GraphWay::REVERSE)) {
                startp = &mtask;
            }
        }

        // Follow the entire critical path
        std::vector<const LogicMTask*> path;
        uint32_t totalCost = 0;
        for (const LogicMTask* nextp = startp; nextp;) {
            path.push_back(nextp);
            totalCost += nextp->cost();

            if (EdgeHeap::Node* const maxp = nextp->m_edgeHeap[GraphWay::FORWARD].max()) {
                nextp = MTaskEdge::toMTaskEdge(GraphWay::FORWARD, maxp)->toMTaskp();
            } else {
                nextp = nullptr;
            }
        }

        *osp << "totalCost = " << totalCost
             << " (should match the computed critical path cost (CP) for the graph)\n";

        // Dump
        for (const LogicMTask* mtaskp : path) {
            *osp << "begin mtask with cost " << mtaskp->cost() << '\n';
            for (const OrderMoveVertex& mVtx : mtaskp->vertexList()) {
                const OrderLogicVertex* const logicp = mVtx.logicp();
                if (!logicp) continue;
                // Show nodes with hierarchical costs
                V3InstrCount::count(logicp->nodep(), false, osp);
            }
        }
    }

private:
    VL_UNCOPYABLE(LogicMTask);
};

// Start at 1, so that 0 indicates no mtask.
uint32_t LogicMTask::s_nextId = 1;

// Instead of dynamic cast
SiblingMC* MergeCandidate::toSiblingMC() {
    return isSiblingMC() ? static_cast<SiblingMC*>(this) : nullptr;
}

MTaskEdge* MergeCandidate::toMTaskEdge() {
    return isSiblingMC() ? nullptr : static_cast<MTaskEdge*>(this);
}

// Normally this would be a virtual function, but we save space by not having a vtable,
// and we know we only have 2 possible subclasses.
bool MergeCandidate::mergeWouldCreateCycle() const {
    return isSiblingMC() ? static_cast<const SiblingMC*>(this)->mergeWouldCreateCycle()
                         : static_cast<const MTaskEdge*>(this)->mergeWouldCreateCycle();
}

static uint32_t siblingScore(const SiblingMC* sibsp) {
    const LogicMTask* const ap = sibsp->ap();
    const LogicMTask* const bp = sibsp->bp();
    const uint32_t mergedCpCostFwd
        = std::max(ap->critPathCost(GraphWay::FORWARD), bp->critPathCost(GraphWay::FORWARD));
    const uint32_t mergedCpCostRev
        = std::max(ap->critPathCost(GraphWay::REVERSE), bp->critPathCost(GraphWay::REVERSE));
    return mergedCpCostRev + mergedCpCostFwd + LogicMTask::stepCost(ap->cost() + bp->cost());
}

static uint32_t edgeScore(const MTaskEdge* edgep) {
    // Score this edge. Lower is better. The score is the new local CP
    // length if we merge these mTaskGraphp.  ("Local" means the longest
    // critical path running through the merged node.)
    const LogicMTask* const top = edgep->toMTaskp();
    const LogicMTask* const fromp = edgep->fromMTaskp();
    const uint32_t mergedCpCostFwd = std::max(fromp->critPathCost(GraphWay::FORWARD),
                                              top->critPathCostWithout<GraphWay::FORWARD>(edgep));
    const uint32_t mergedCpCostRev = std::max(fromp->critPathCostWithout<GraphWay::REVERSE>(edgep),
                                              top->critPathCost(GraphWay::REVERSE));
    return mergedCpCostRev + mergedCpCostFwd + LogicMTask::stepCost(fromp->cost() + top->cost());
}

void MergeCandidate::rescore() {
    if (const SiblingMC* const sibp = toSiblingMC()) {
        m_key.m_score = siblingScore(sibp);
    } else {
        // The '1 +' favors merging a SiblingMC over an otherwise-
        // equal-scoring MTaskEdge. The comment on selfTest() talks
        // about why.
        m_key.m_score = 1 + edgeScore(static_cast<const MTaskEdge*>(this));
    }
}

SiblingMC::SiblingMC(LogicMTask* ap, LogicMTask* bp)
    : MergeCandidate{/* isSiblingMC: */ true}
    , m_ap{ap}
    , m_bp{bp} {
    // Storage management depends on this
    UASSERT(ap->id() > bp->id(), "Should be ordered");
    UDEBUGONLY(UASSERT(ap->siblings().count(bp), "Should be in sibling map"););
    m_ap->aSiblingMCs().linkBack(this);
    m_bp->bSiblingMCs().linkBack(this);
}

void SiblingMC::unlinkA() {
    VL_ATTR_UNUSED const size_t removed = m_ap->siblings().erase(m_bp);
    UDEBUGONLY(UASSERT(removed == 1, "Should have been in sibling set"););
    m_ap->aSiblingMCs().unlink(this);
}

void SiblingMC::unlinkB() { m_bp->bSiblingMCs().unlink(this); }

bool SiblingMC::mergeWouldCreateCycle() const {
    return (LogicMTask::pathExistsFrom(m_ap, m_bp, nullptr)
            || LogicMTask::pathExistsFrom(m_bp, m_ap, nullptr));
}

MTaskEdge::MTaskEdge(V3Graph* graphp, LogicMTask* fromp, LogicMTask* top, int weight)
    : V3GraphEdge{graphp, fromp, top, weight}
    , MergeCandidate{/* isSiblingMC: */ false} {
    fromp->addRelativeMTask(top);
    fromp->addRelativeEdge<GraphWay::FORWARD>(this);
    top->addRelativeEdge<GraphWay::REVERSE>(this);
}

template <GraphWay::en T_Way>
LogicMTask* MTaskEdge::furtherMTaskp() const {
    return static_cast<LogicMTask*>(this->furtherp<T_Way>());
}
LogicMTask* MTaskEdge::fromMTaskp() const { return static_cast<LogicMTask*>(fromp()); }
LogicMTask* MTaskEdge::toMTaskp() const { return static_cast<LogicMTask*>(top()); }

bool MTaskEdge::mergeWouldCreateCycle() const {
    return LogicMTask::pathExistsFrom(fromMTaskp(), toMTaskp(), this);
}
// Following initial assignment of critical paths, clear this MTaskEdge
// out of the edge-map for each node and reinsert at a new location
// with updated critical path.
void MTaskEdge::resetCriticalPaths() {
    LogicMTask* const fromp = fromMTaskp();
    LogicMTask* const top = toMTaskp();
    fromp->removeRelativeEdge<GraphWay::FORWARD>(this);
    top->removeRelativeEdge<GraphWay::REVERSE>(this);
    fromp->addRelativeEdge<GraphWay::FORWARD>(this);
    top->addRelativeEdge<GraphWay::REVERSE>(this);
}

//######################################################################

// Look at vertex costs (in one way) to form critical paths for each
// vertex.
template <GraphWay::en T_Way>
static void partInitHalfCriticalPaths(V3Graph& mTaskGraph, bool checkOnly) {
    constexpr GraphWay way{T_Way};
    constexpr GraphWay rev = way.invert();
    GraphStreamUnordered order{&mTaskGraph, way};
    for (const V3GraphVertex* vertexp; (vertexp = order.nextp());) {
        const LogicMTask* const mtaskcp = static_cast<const LogicMTask*>(vertexp);
        LogicMTask* const mtaskp = const_cast<LogicMTask*>(mtaskcp);
        uint32_t cpCost = 0;
#if VL_DEBUG
        std::unordered_set<V3GraphVertex*> relatives;
#endif
        for (const V3GraphEdge& edge : vertexp->edges<rev>()) {
#if VL_DEBUG
            // Run a few asserts on the initial mtask graph,
            // while we're iterating through...
            UASSERT_OBJ(edge.weight() != 0, mtaskp, "Should be no cut edges in mTaskGraphp graph");
            UASSERT_OBJ(relatives.find(edge.furtherp<rev>()) == relatives.end(), mtaskp,
                        "Should be no redundant edges in mTaskGraphp graph");
            relatives.insert(edge.furtherp<rev>());
#endif
            const LogicMTask* const relativep = static_cast<LogicMTask*>(edge.furtherp<rev>());
            cpCost = std::max(cpCost, (relativep->critPathCost(way)
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
static void partInitCriticalPaths(V3Graph& mTaskGraph) {
    partInitHalfCriticalPaths<GraphWay::FORWARD>(mTaskGraph, false);
    partInitHalfCriticalPaths<GraphWay::REVERSE>(mTaskGraph, false);

    // Reset all MTaskEdges so that 'm_edges' will show correct CP numbers.
    // They would have been all zeroes on initial creation of the MTaskEdges.
    for (V3GraphVertex& vtx : mTaskGraph.vertices()) {
        for (V3GraphEdge& edge : vtx.outEdges()) edge.as<MTaskEdge>()->resetCriticalPaths();
    }
}

// Do an EXPENSIVE check to make sure that all incremental CP updates have
// gone correctly.
static void partCheckCriticalPaths(V3Graph& mTaskGraph) {
    partInitHalfCriticalPaths<GraphWay::FORWARD>(mTaskGraph, true);
    partInitHalfCriticalPaths<GraphWay::REVERSE>(mTaskGraph, true);
    for (const V3GraphVertex& vtx : mTaskGraph.vertices()) {
        const LogicMTask& mtask = static_cast<const LogicMTask&>(vtx);
        mtask.checkRelativesCp<GraphWay::FORWARD>();
        mtask.checkRelativesCp<GraphWay::REVERSE>();
    }
}

// ######################################################################
//  PropagateCp

template <GraphWay::en T_Way>
class PropagateCp final {
    // Propagate increasing critical path (CP) costs through a graph.
    //
    // Usage:
    //  * Client increases the cost and/or CP at a node or small set of nodes
    //    (often a pair in practice, eg. edge contraction.)
    //  * Client calls PropagateCp::cpHasIncreased() one or more times.
    //    Each call indicates that the inclusive CP of some "seed" vertex
    //    has increased to a given value.
    //    * NOTE: PropagateCp will neither read nor modify the cost
    //      or CPs at the seed vertices, it only accesses and modifies
    //      vertices wayward from the seeds.
    //  * Client calls PropagateCp::go(). Internally, this iteratively
    //    propagates the new CPs wayward through the graph.
    //

    // TYPES

    // We keep pending vertices in a heap during critical path propagation
    struct PendingKey final {
        LogicMTask* m_mtaskp;  // The vertex in the heap
        uint32_t m_score;  // The score of this entry
        void increase(uint32_t score) {
            UDEBUGONLY(UASSERT(score >= m_score, "Must increase"););
            m_score = score;
        }
        bool operator<(const PendingKey& other) const {
            if (m_score != other.m_score) return m_score < other.m_score;
            return LogicMTask::CmpLogicMTask{}(m_mtaskp, other.m_mtaskp);
        }
    };

    using PendingHeap = PairingHeap<PendingKey>;
    using PendingHeapNode = typename PendingHeap::Node;

    // MEMBERS
    PendingHeap m_pendingHeap;  // Heap of pending rescores

    // We allocate this many heap nodes at once
    static constexpr size_t ALLOC_CHUNK_SIZE = 128;
    PendingHeapNode* m_freep = nullptr;  // List of free heap nodes
    std::vector<std::unique_ptr<PendingHeapNode[]>> m_allocated;  // Allocated heap nodes

    const bool m_slowAsserts;  // Enable nontrivial asserts
    // Used only with slow asserts to check mTaskGraphp visited only once
    std::set<LogicMTask*> m_seen;

public:
    // CONSTRUCTORS
    explicit PropagateCp(bool slowAsserts)
        : m_slowAsserts{slowAsserts} {}

    // METHODS
private:
    // Allocate a HeapNode for the given element
    PendingHeapNode* allocNode() {
        // If no free nodes available, then make some
        if (!m_freep) {
            // Allocate in chunks for efficiency
            m_allocated.emplace_back(new PendingHeapNode[ALLOC_CHUNK_SIZE]);
            // Set up free list pointer
            m_freep = m_allocated.back().get();
            // Set up free list chain
            for (size_t i = 1; i < ALLOC_CHUNK_SIZE; ++i) {
                m_freep[i - 1].m_next.m_ptr = &m_freep[i];
            }
            // Clear the next pointer of the last entry
            m_freep[ALLOC_CHUNK_SIZE - 1].m_next.m_ptr = nullptr;
        }
        // Free nodes are available, pick up the first one
        PendingHeapNode* const resultp = m_freep;
        m_freep = resultp->m_next.m_ptr;
        resultp->m_next.m_ptr = nullptr;
        return resultp;
    }

    // Release a heap node (make it available for future allocation)
    void freeNode(PendingHeapNode* nodep) {
        // Re-use the existing link pointers and simply prepend it to the free list
        nodep->m_next.m_ptr = m_freep;
        m_freep = nodep;
    }

public:
    void cpHasIncreased(V3GraphVertex* vxp, uint32_t newInclusiveCp) {
        constexpr GraphWay way{T_Way};
        constexpr GraphWay inv{way.invert()};

        // For *vxp, whose CP-inclusive has just increased to
        // newInclusiveCp, iterate to all wayward nodes, update the edges
        // of each, and add each to m_pending if its overall CP has grown.
        for (V3GraphEdge& graphEdge : vxp->edges<way>()) {
            MTaskEdge& edge = static_cast<MTaskEdge&>(graphEdge);

            LogicMTask* const relativep = edge.furtherMTaskp<T_Way>();
            EdgeHeap::Node& edgeHeapNode = edge.m_edgeHeapNode[inv];
            if (newInclusiveCp > edgeHeapNode.key().m_score) {
                relativep->m_edgeHeap[inv].increaseKey(&edgeHeapNode, newInclusiveCp);
            }

            const uint32_t critPathCost = relativep->critPathCost(way);

            if (critPathCost >= newInclusiveCp) continue;

            // relativep's critPathCost() is out of step with its longest !wayward edge.
            // Schedule that to be resolved.
            const uint32_t newVal = newInclusiveCp - critPathCost;

            if (PendingHeapNode* const nodep = static_cast<PendingHeapNode*>(relativep->userp())) {
                // Already in heap. Increase score if needed.
                if (newVal > nodep->key().m_score) m_pendingHeap.increaseKey(nodep, newVal);
                continue;
            }

            // Add to heap
            PendingHeapNode* const nodep = allocNode();
            relativep->userp(nodep);
            m_pendingHeap.insert(nodep, {relativep, newVal});
        }
    }

    void go() {
        constexpr GraphWay way{T_Way};
        constexpr GraphWay inv{way.invert()};

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
        while (!m_pendingHeap.empty()) {
            // Pop max element from heap
            PendingHeapNode* const maxp = m_pendingHeap.max();
            m_pendingHeap.remove(maxp);
            // Pick up values
            LogicMTask* const mtaskp = maxp->key().m_mtaskp;
            const uint32_t cpGrowBy = maxp->key().m_score;
            // Free the heap node, we are done with it
            freeNode(maxp);
            mtaskp->userp(nullptr);
            // Update the critPathCost of mtaskp, that was out-of-date with respect to its edges
            const uint32_t startCp = mtaskp->critPathCost(way);
            const uint32_t newCp = startCp + cpGrowBy;
            if (VL_UNLIKELY(m_slowAsserts)) {
                // Check that CP matches that of the longest edge wayward of vxp.
                const uint32_t edgeCp = mtaskp->m_edgeHeap[inv].max()->key().m_score;
                UASSERT_OBJ(edgeCp == newCp, mtaskp, "CP doesn't match longest wayward edge");
                // Confirm that we only set each node's CP once.  That's an
                // important property of PropagateCp which allows it to be far
                // faster than a recursive algorithm on some graphs.
                const bool first = m_seen.insert(mtaskp).second;
                UASSERT_OBJ(first, mtaskp, "Set CP on node twice");
            }
            mtaskp->setCritPathCost(way, newCp);
            cpHasIncreased(mtaskp, newCp + mtaskp->stepCost());
        }

        if (VL_UNLIKELY(m_slowAsserts)) m_seen.clear();
    }

private:
    VL_UNCOPYABLE(PropagateCp);

public:
    static void selfTest() {
        V3Graph graph;  // A graph
        std::array<LogicMTask*, 50> vx;  // All vertices within the graph

        // Generate a pseudo-random graph
        std::array<uint64_t, 2> rngState
            = {{0x12345678ULL, 0x9abcdef0ULL}};  // GCC 3.8.0 wants {{}}
        // Create 50 vertices
        for (auto& i : vx) {
            i = new LogicMTask{&graph, nullptr};
            i->setCost(1);
        }
        // Create 250 edges at random. Edges must go from
        // lower-to-higher index vertices, so we get a DAG.
        for (unsigned i = 0; i < 250; ++i) {
            const unsigned idx1 = V3Os::rand64(rngState) % 50;
            const unsigned idx2 = V3Os::rand64(rngState) % 50;
            if (idx1 > idx2) {
                if (!vx[idx2]->hasRelativeMTask(vx[idx1])) {
                    new MTaskEdge{&graph, vx[idx2], vx[idx1], 1};
                }
            } else if (idx2 > idx1) {
                if (!vx[idx1]->hasRelativeMTask(vx[idx2])) {
                    new MTaskEdge{&graph, vx[idx1], vx[idx2], 1};
                }
            }
        }

        partInitCriticalPaths(graph);

        PropagateCp<T_Way> prop{true};

        // Seed the propagator with every input node;
        // This should result in the complete graph getting all CP's assigned.
        for (const auto& i : vx) {
            if (i->inEmpty()) prop.cpHasIncreased(i, 1 /* inclusive CP starts at 1 */);
        }

        // Run the propagator.
        prop.go();

        // Finally, confirm that the entire graph appears to have correct CPs.
        partCheckCriticalPaths(graph);
    }
};

// Merge edges from a LogicMtask.
static void partRedirectEdgesFrom(V3Graph& graph, LogicMTask* recipientp, LogicMTask* donorp,
                                  MergeCandidateScoreboard* sbp) {
    // This code removes adjacent edges. When this occurs, mark it in need
    // of a rescore, in case its score has fallen and we need to move it up
    // toward the front of the scoreboard.
    //
    // Wait, what? Shouldn't the scores only increase as we merge nodes? Well
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

    // Process outgoing edges
    while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->outEdges().frontp())) {
        LogicMTask* const relativep = edgep->toMTaskp();

        relativep->removeRelativeEdge<GraphWay::REVERSE>(edgep);

        if (recipientp->hasRelativeMTask(relativep)) {
            // An edge already exists between recipient and relative of donor.
            // Mark it in need of a rescore
            if (sbp) {
                if (sbp->contains(edgep)) sbp->remove(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep<GraphWay::FORWARD>(relativep));
                UDEBUGONLY(UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge"););
                if (sbp->contains(existMTaskEdgep)) sbp->hintScoreChanged(existMTaskEdgep);
            }
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        } else {
            // No existing edge between recipient and relative of donor.
            // Redirect the edge from donor<->relative to recipient<->relative.
            edgep->relinkFromp(recipientp);
            recipientp->addRelativeMTask(relativep);
            recipientp->stealRelativeEdge<GraphWay::FORWARD>(edgep);
            relativep->addRelativeEdge<GraphWay::REVERSE>(edgep);
            if (sbp) {
                if (!sbp->contains(edgep)) {
                    sbp->add(edgep);
                } else {
                    sbp->hintScoreChanged(edgep);
                }
            }
        }
    }

    // Process incoming edges
    while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->inEdges().frontp())) {
        LogicMTask* const relativep = edgep->fromMTaskp();

        relativep->removeRelativeMTask(donorp);
        relativep->removeRelativeEdge<GraphWay::FORWARD>(edgep);

        if (relativep->hasRelativeMTask(recipientp)) {
            // An edge already exists between recipient and relative of donor.
            // Mark it in need of a rescore
            if (sbp) {
                if (sbp->contains(edgep)) sbp->remove(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep<GraphWay::REVERSE>(relativep));
                UDEBUGONLY(UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge"););
                if (sbp->contains(existMTaskEdgep)) sbp->hintScoreChanged(existMTaskEdgep);
            }
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        } else {
            // No existing edge between recipient and relative of donor.
            // Redirect the edge from donor<->relative to recipient<->relative.
            edgep->relinkTop(recipientp);
            relativep->addRelativeMTask(recipientp);
            relativep->addRelativeEdge<GraphWay::FORWARD>(edgep);
            recipientp->stealRelativeEdge<GraphWay::REVERSE>(edgep);
            if (sbp) {
                if (!sbp->contains(edgep)) {
                    sbp->add(edgep);
                } else {
                    sbp->hintScoreChanged(edgep);
                }
            }
        }
    }

    // Remove donorp from the graph
    VL_DO_DANGLING(donorp->unlinkDelete(&graph), donorp);
}

//######################################################################
// Contraction

// Perform edge or sibling contraction on the partition graph
class Contraction final {
    // TYPES
    // New CP information for mtaskp reflecting an upcoming merge
    struct NewCp final {
        uint32_t cp;
        uint32_t propagateCp;
        bool propagate;
    };

    // MEMBERS
    V3Graph& m_mTaskGraph;  // The Mtask graph
    uint32_t m_scoreLimit;  // Sloppy score allowed when picking merges
    uint32_t m_scoreLimitBeforeRescore = 0xffffffff;  // Next score rescore at
    unsigned m_mergesSinceRescore = 0;  // Merges since last rescore
    const bool m_slowAsserts;  // Take extra time to validate algorithm
    MergeCandidateScoreboard m_sb;  // Scoreboard

    PropagateCp<GraphWay::FORWARD> m_forwardPropagator{m_slowAsserts};  // Forward propagator
    PropagateCp<GraphWay::REVERSE> m_reversePropagator{m_slowAsserts};  // Reverse propagator

    LogicMTask* const m_entryMTaskp;  // Singular source vertex of the dependency graph
    LogicMTask* const m_exitMTaskp;  // Singular sink vertex of the dependency graph

public:
    // CONSTRUCTORS
    Contraction(V3Graph& mTaskGraph, uint32_t scoreLimit, LogicMTask* entryMTaskp,
                LogicMTask* exitMTaskp, bool slowAsserts)
        : m_mTaskGraph{mTaskGraph}
        , m_scoreLimit{scoreLimit}
        , m_slowAsserts{slowAsserts}
        , m_entryMTaskp{entryMTaskp}
        , m_exitMTaskp{exitMTaskp} {
        if (m_slowAsserts) {
            // Check there are no redundant edges
            for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) {
                std::unordered_set<const V3GraphVertex*> neighbors;
                for (V3GraphEdge& edge : vtx.outEdges()) {
                    const bool first = neighbors.insert(edge.top()).second;
                    UASSERT_OBJ(first, &vtx, "Redundant edge found in input to Contraction()");
                }
            }
        }

        unsigned maxMTasks = v3Global.opt.threadsMaxMTasks();
        if (maxMTasks == 0) {  // Unspecified so estimate
            if (v3Global.opt.threads() > 1) {
                maxMTasks = (PART_DEFAULT_MAX_MTASKS_PER_THREAD * v3Global.opt.threads());
            } else {
                // Running Contraction with --threads <= 1 means self-test
                maxMTasks = 500;
            }
        }

        // OPTIMIZATION PASS: Edge contraction and sibling contraction.
        //  - Score each pair of mTaskGraphp which is a candidate to merge.
        //    * Each edge defines such a candidate pair
        //    * Two mTaskGraphp that are prereqs or postreqs of a common third
        //      vertex are "siblings", these are also a candidate pair.
        //  - Build a list of MergeCandidates, sorted by score.
        //  - Merge the best pair.
        //  - Incrementally recompute critical paths near the merged mtask.

        for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) {
            vtx.userp(nullptr);  // Reset user value while we are here. Used by PropagateCp.
            for (V3GraphEdge& edge : vtx.outEdges()) m_sb.add(static_cast<MTaskEdge*>(&edge));
            siblingPairFromRelatives<GraphWay::REVERSE, true>(&vtx);
            siblingPairFromRelatives<GraphWay::FORWARD, true>(&vtx);
        }

        doRescore();  // Set initial scores in scoreboard

        while (true) {
            // This is the best edge to merge, with the lowest
            // score (shortest local critical path)
            MergeCandidate* const mergeCanp = m_sb.best();
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
            const uint32_t cachedScore = mergeCanp->score();
            mergeCanp->rescore();
            const uint32_t actualScore = mergeCanp->score();

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

                    // Except, if we have too many mTaskGraphp, raise the score
                    // limit and keep going...
                    const unsigned mtaskCount = m_mTaskGraph.vertices().size();
                    if (mtaskCount > maxMTasks) {
                        const uint32_t oldLimit = m_scoreLimit;
                        m_scoreLimit = (m_scoreLimit * 120) / 100;
                        v3Global.rootp()->fileline()->v3warn(
                            UNOPTTHREADS, "Thread scheduler is unable to provide requested "
                                          "parallelism; suggest asking for fewer threads.");
                        UINFO(1, "Critical path limit was=" << oldLimit << " now=" << m_scoreLimit
                                                            << endl);
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

            // Avoid merging the entry/exit nodes. This would create serialization, by forcing the
            // merged MTask to run before/after everything else. Empirically this helps
            // performance in a modest way by allowing other MTasks to start earlier.
            if (MTaskEdge* const edgep = mergeCanp->toMTaskEdge()) {
                if (edgep->fromp() == m_entryMTaskp || edgep->top() == m_exitMTaskp) {
                    m_sb.remove(mergeCanp);
                    continue;
                }
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
                // Remove this candidate from scoreboard so we don't keep
                // reconsidering it on every loop.
                m_sb.remove(mergeCanp);
                if (SiblingMC* const smcp = mergeCanp->toSiblingMC()) {
                    smcp->unlinkA();
                    smcp->unlinkB();
                    VL_DO_DANGLING(delete smcp, smcp);
                }
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
                UINFO(6, "New scoreLimitBeforeRescore: " << m_scoreLimitBeforeRescore << endl);
            }

            // Finally merge this candidate.
            contract(mergeCanp);
        }

        // Free remaining SiblingMCs
        while (MergeCandidate* const mergeCanp = m_sb.best()) {
            m_sb.remove(mergeCanp);
            if (SiblingMC* const smcp = mergeCanp->toSiblingMC()) {
                smcp->unlinkA();
                smcp->unlinkB();
                VL_DO_DANGLING(delete smcp, smcp);
            }
        }
    }

private:
    template <GraphWay::en T_Way>
    NewCp newCp(LogicMTask* mtaskp, LogicMTask* otherp, MTaskEdge* mergeEdgep) {
        constexpr GraphWay way{T_Way};
        // Return new wayward-CP for mtaskp reflecting its upcoming merge
        // with otherp. Set 'result.propagate' if mtaskp's wayward
        // relatives will see a new wayward CP from this merge.
        uint32_t newCp;
        if (mergeEdgep) {
            if (mtaskp == mergeEdgep->furtherp<way>()) {
                newCp = std::max(otherp->critPathCost(way),
                                 mtaskp->critPathCostWithout<way>(mergeEdgep));
            } else {
                newCp = std::max(mtaskp->critPathCost(way),
                                 otherp->critPathCostWithout<way>(mergeEdgep));
            }
        } else {
            newCp = std::max(otherp->critPathCost(way), mtaskp->critPathCost(way));
        }

        const uint32_t origRelativesCp = mtaskp->critPathCost(way) + mtaskp->stepCost();
        const uint32_t newRelativesCp
            = newCp + LogicMTask::stepCost(mtaskp->cost() + otherp->cost());

        NewCp result;
        result.cp = newCp;
        result.propagate = (newRelativesCp > origRelativesCp);
        result.propagateCp = newRelativesCp;
        return result;
    }

    void removeSiblingMCsWith(LogicMTask* mtaskp) {
        while (SiblingMC* const smcp = mtaskp->aSiblingMCs().unlinkFront()) {
            m_sb.remove(smcp);
            smcp->unlinkB();
            VL_DO_DANGLING(delete smcp, smcp);
        }
        while (SiblingMC* const smcp = mtaskp->bSiblingMCs().unlinkFront()) {
            m_sb.remove(smcp);
            smcp->unlinkA();
            VL_DO_DANGLING(delete smcp, smcp);
        }
    }

    void removeSiblingMCs(LogicMTask* recipientp, LogicMTask* donorp) {
        // The lists here should be disjoint (there should be only one SiblingMC involving these
        // two MTasks, and we removed that elsewhere), so no need for unlinking from the lists we
        // are clearing.
        removeSiblingMCsWith(recipientp);
        removeSiblingMCsWith(donorp);

        // Clear the sibling map of the recipient. The donor will be deleted anyway, so we can
        // leave that in a corrupt for efficiency.
        recipientp->siblings().clear();
    }

    void contract(MergeCandidate* mergeCanp) {
        LogicMTask* top = nullptr;
        LogicMTask* fromp = nullptr;
        MTaskEdge* const mergeEdgep = mergeCanp->toMTaskEdge();
        SiblingMC* const mergeSibsp = mergeCanp->toSiblingMC();
        if (mergeEdgep) {
            top = mergeEdgep->toMTaskp();
            fromp = mergeEdgep->fromMTaskp();
        } else {
            top = mergeSibsp->ap();
            fromp = mergeSibsp->bp();
        }

        // Merge the smaller mtask into the larger mtask.  If one of them
        // is much larger, this will save time in partRedirectEdgesFrom().
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
        VL_DANGLING(fromp);
        VL_DANGLING(top);  // Use donorp and recipientp now instead

        // Recursively update forward and reverse CP numbers.
        //
        // Doing this before merging the mTaskGraphp lets us often avoid
        // recursing through either incoming or outgoing edges on one or
        // both mTaskGraphp.
        //
        // These 'NewCp' objects carry a bit indicating whether we must
        // propagate CP for each of the four cases:
        const NewCp recipientNewCpFwd = newCp<GraphWay::FORWARD>(recipientp, donorp, mergeEdgep);
        const NewCp donorNewCpFwd = newCp<GraphWay::FORWARD>(donorp, recipientp, mergeEdgep);
        const NewCp recipientNewCpRev = newCp<GraphWay::REVERSE>(recipientp, donorp, mergeEdgep);
        const NewCp donorNewCpRev = newCp<GraphWay::REVERSE>(donorp, recipientp, mergeEdgep);

        m_sb.remove(mergeCanp);

        if (mergeEdgep) {
            // Remove and free the connecting edge. Must do this before propagating CP's below.
            mergeEdgep->fromMTaskp()->removeRelativeMTask(mergeEdgep->toMTaskp());
            mergeEdgep->fromMTaskp()->removeRelativeEdge<GraphWay::FORWARD>(mergeEdgep);
            mergeEdgep->toMTaskp()->removeRelativeEdge<GraphWay::REVERSE>(mergeEdgep);
            VL_DO_DANGLING(mergeEdgep->unlinkDelete(), mergeEdgep);
        } else {
            // Remove the siblingMC
            mergeSibsp->unlinkA();
            mergeSibsp->unlinkB();
            VL_DO_DANGLING(delete mergeSibsp, mergeSibsp);
        }

        // This also updates cost and stepCost on recipientp
        recipientp->moveAllVerticesFrom(donorp);

        UINFO(9, "recipient = " << recipientp->id() << ", donor = " << donorp->id()
                                << ", mergeEdgep = " << mergeEdgep << "\n"
                                << "recipientNewCpFwd = " << recipientNewCpFwd.cp
                                << (recipientNewCpFwd.propagate ? " true " : " false ")
                                << recipientNewCpFwd.propagateCp << "\n"
                                << "donorNewCpFwd = " << donorNewCpFwd.cp
                                << (donorNewCpFwd.propagate ? " true " : " false ")
                                << donorNewCpFwd.propagateCp << endl);

        recipientp->setCritPathCost(GraphWay::FORWARD, recipientNewCpFwd.cp);
        if (recipientNewCpFwd.propagate) {
            m_forwardPropagator.cpHasIncreased(recipientp, recipientNewCpFwd.propagateCp);
        }
        recipientp->setCritPathCost(GraphWay::REVERSE, recipientNewCpRev.cp);
        if (recipientNewCpRev.propagate) {
            m_reversePropagator.cpHasIncreased(recipientp, recipientNewCpRev.propagateCp);
        }
        if (donorNewCpFwd.propagate) {
            m_forwardPropagator.cpHasIncreased(donorp, donorNewCpFwd.propagateCp);
        }
        if (donorNewCpRev.propagate) {
            m_reversePropagator.cpHasIncreased(donorp, donorNewCpRev.propagateCp);
        }
        m_forwardPropagator.go();
        m_reversePropagator.go();

        // Remove all other SiblingMCs that include recipientp or donorp. We remove all siblingMCs
        // of recipientp so we do not get huge numbers of SiblingMCs. We'll recreate them below, up
        // to a bounded number.
        removeSiblingMCs(recipientp, donorp);

        // Redirect all edges, delete donorp
        partRedirectEdgesFrom(m_mTaskGraph, recipientp, donorp, &m_sb);

        ++m_mergesSinceRescore;

        // Do an expensive check, confirm we haven't botched the CP
        // updates.
        if (m_slowAsserts) partCheckCriticalPaths(m_mTaskGraph);

        // Finally, make new sibling pairs as needed:
        //  - prereqs and postreqs of recipientp
        //  - prereqs of recipientp's postreqs
        //  - postreqs of recipientp's prereqs
        // Note that this depends on the updated critical paths (above).
        siblingPairFromRelatives<GraphWay::REVERSE, true>(recipientp);
        siblingPairFromRelatives<GraphWay::FORWARD, true>(recipientp);
        unsigned edges = 0;
        for (V3GraphEdge& edge : recipientp->outEdges()) {
            LogicMTask* const postreqp = static_cast<LogicMTask*>(edge.top());
            siblingPairFromRelatives<GraphWay::REVERSE, false>(postreqp);
            ++edges;
            if (edges >= PART_SIBLING_EDGE_LIMIT) break;
        }
        edges = 0;
        for (V3GraphEdge& edge : recipientp->inEdges()) {
            LogicMTask* const prereqp = static_cast<LogicMTask*>(edge.fromp());
            siblingPairFromRelatives<GraphWay::FORWARD, false>(prereqp);
            ++edges;
            if (edges >= PART_SIBLING_EDGE_LIMIT) break;
        }
    }

    void doRescore() {
        // During rescore, we know that graph isn't changing, so allow
        // the critPathCost*Without() routines to cache some data in
        // each LogicMTask. This is just an optimization, things should
        // behave identically without the caching (just slower)

        m_sb.rescore();
        UINFO(6, "Did rescore. Merges since previous = " << m_mergesSinceRescore << endl);

        m_mergesSinceRescore = 0;
        m_scoreLimitBeforeRescore = 0xffffffff;
    }

    void makeSiblingMC(LogicMTask* ap, LogicMTask* bp) {
        if (ap->id() < bp->id()) std::swap(ap, bp);
        // The higher id vertex owns the association set
        const auto first = ap->siblings().insert(bp).second;
        if (first) {
            m_sb.add(new SiblingMC{ap, bp});
        } else if (VL_UNLIKELY(m_slowAsserts)) {
            // It's fine if we already have this SiblingMC, we may have
            // created it earlier. Just confirm that we have associated data.
            bool found = false;
            for (const SiblingMC& smc : ap->aSiblingMCs()) {
                UASSERT_OBJ(smc.ap() == ap, ap, "Inconsistent SiblingMC");
                UASSERT_OBJ(m_sb.contains(&smc), ap, "Must be on the scoreboard");
                if (smc.bp() == bp) found = true;
            }
            UASSERT_OBJ(found, ap, "Sibling not found");
        }
    }

    template <GraphWay::en T_Way, bool Exhaustive>
    void siblingPairFromRelatives(V3GraphVertex* mtaskp) {
        constexpr GraphWay way{T_Way};
        // Need at least 2 edges
        auto& edges = mtaskp->edges<way>();
        if (!edges.hasMultipleElements()) return;

        std::array<LogicMTask*, PART_SIBLING_EDGE_LIMIT> neighbors;

        // This is a hot method, so we want so sort as efficiently as possible. We pre-load
        // all data (critical path cost and id) required for determining ordering into an aligned
        // structure. There is not enough space next to these to keep a whole pointer within 16
        // bytes, so we store an index into the neighbors buffer instead. We can then compare
        // and swap these sorting records very efficiently. With this the standard library sorting
        // functions are efficient enough and using more optimized methods (e.g.: sorting networks)
        // has no measurable benefit.
        struct alignas(16) SortingRecord final {
            uint64_t m_id;
            uint32_t m_cp;
            uint8_t m_idx;
            static_assert(PART_SIBLING_EDGE_LIMIT <= std::numeric_limits<uint8_t>::max(),
                          "m_idx must fit all indices into 'neighbors'");
            bool operator<(const SortingRecord& that) const {
                return m_cp < that.m_cp || (m_cp == that.m_cp && m_id < that.m_id);
            }
        };
        static_assert(sizeof(SortingRecord) <= 16, "How could this be padded to more than 16?");

        std::array<SortingRecord, PART_SIBLING_EDGE_LIMIT> sortRecs;
        size_t n = 0;

        // Populate the buffers
        for (V3GraphEdge& edge : mtaskp->edges<way>()) {
            LogicMTask* const otherp = static_cast<LogicMTask*>(edge.furtherp<way>());
            neighbors[n] = otherp;
            sortRecs[n].m_id = otherp->id();
            sortRecs[n].m_cp = otherp->critPathCost(way) + otherp->cost();
            sortRecs[n].m_idx = n;
            ++n;
            // Prevent nodes with huge numbers of edges from massively slowing down us down
            if (n >= PART_SIBLING_EDGE_LIMIT) break;
        }

        // Don't make all possible pairs of siblings when not requested (non-exhaustive).
        // Just make a few pairs.
        constexpr size_t MAX_NONEXHAUSTIVE_PAIRS = 3;

        if (Exhaustive || n <= 2 * MAX_NONEXHAUSTIVE_PAIRS) {
            const size_t end = n & ~static_cast<size_t>(1);  // Round down to even, (we want pairs)
            std::sort(sortRecs.begin(), sortRecs.begin() + n);
            for (size_t i = 0; i < end; i += 2) {
                makeSiblingMC(neighbors[sortRecs[i].m_idx], neighbors[sortRecs[i + 1].m_idx]);
            }
        } else {
            constexpr size_t end = 2 * MAX_NONEXHAUSTIVE_PAIRS;
            std::partial_sort(sortRecs.begin(), sortRecs.begin() + end, sortRecs.begin() + n);
            for (size_t i = 0; i < end; i += 2) {
                makeSiblingMC(neighbors[sortRecs[i].m_idx], neighbors[sortRecs[i + 1].m_idx]);
            }
        }
    }

    // SELF TESTS

    // This is a performance test, its intent is to demonstrate that the
    // partitioner doesn't run on this chain in N^2 time or worse. Overall
    // runtime should be N*log(N) for a chain-shaped graph.
    //
    static void selfTestChain() {
        const uint64_t usecsSmall = partitionChainUsecs(5);
        const uint64_t usecsLarge = partitionChainUsecs(500);
        // Large input is 50x bigger than small input.
        // Its runtime should be about 10x longer -- not about 2500x longer
        // or worse which would suggest N^2 scaling or worse.
        UASSERT(usecsLarge < (usecsSmall * 1500),
                "selfTestChain() took longer than expected. Small input runtime = "
                    << usecsSmall << ", large input runtime = " << usecsLarge);
    }

    static uint64_t partitionChainUsecs(unsigned chain_len) {
        // NOTE: To get a dot file run with --debugi-Partitioner 4 or more.
        const uint64_t startUsecs = V3Os::timeUsecs();
        V3Graph mTaskGraph;
        LogicMTask* lastp = nullptr;
        for (unsigned i = 0; i < chain_len; ++i) {
            LogicMTask* const mtp = new LogicMTask{&mTaskGraph, nullptr};
            mtp->setCost(1);
            if (lastp) new MTaskEdge{&mTaskGraph, lastp, mtp, 1};
            lastp = mtp;
        }
        partInitCriticalPaths(mTaskGraph);

        // Since slowAsserts mode is *expected* to cause N^2 runtime, and the
        // intent of this test is to demonstrate better-than-N^2 runtime, disable
        // slowAsserts.
        Contraction::apply(mTaskGraph,
                           // Any CP limit >chain_len should work:
                           chain_len * 2, nullptr, nullptr, /* slowAsserts: */ false);

        // All vertices should merge into one
        UASSERT_SELFTEST(bool, mTaskGraph.vertices().hasSingleElement(), true);

        const uint64_t endUsecs = V3Os::timeUsecs();
        const uint64_t elapsedUsecs = endUsecs - startUsecs;

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
        // NOTE: To get a dot file run with --debugi-Partitioner 4 or more.
        V3Graph mTaskGraph;
        LogicMTask* const centerp = new LogicMTask{&mTaskGraph, nullptr};
        centerp->setCost(1);
        unsigned i;
        for (i = 0; i < 50; ++i) {
            LogicMTask* const mtp = new LogicMTask{&mTaskGraph, nullptr};
            mtp->setCost(1);
            // Edge from every input -> centerp
            new MTaskEdge{&mTaskGraph, mtp, centerp, 1};
        }
        for (i = 0; i < 50; ++i) {
            LogicMTask* const mtp = new LogicMTask{&mTaskGraph, nullptr};
            mtp->setCost(1);
            // Edge from centerp -> every output
            new MTaskEdge{&mTaskGraph, centerp, mtp, 1};
        }

        partInitCriticalPaths(mTaskGraph);
        Contraction::apply(mTaskGraph, 20, nullptr, nullptr, true);

        const auto report = mTaskGraph.parallelismReport(
            [](const V3GraphVertex* vtxp) { return vtxp->as<const LogicMTask>()->cost(); });

        // Checking exact values here is maybe overly precise.  What we're
        // mostly looking for is a healthy reduction in the number of mTaskGraphp.
        UASSERT_SELFTEST(uint64_t, report.criticalPathCost(), 19);
        UASSERT_SELFTEST(uint64_t, report.totalGraphCost(), 101);
        UASSERT_SELFTEST(uint64_t, report.vertexCount(), 14);
        UASSERT_SELFTEST(uint64_t, report.edgeCount(), 13);
    }

public:
    static void selfTest() {
        selfTestX();
        selfTestChain();
    }

    static void apply(V3Graph& mTaskGraph, uint32_t scoreLimit, LogicMTask* entryMTaskp,
                      LogicMTask* exitMTaskp, bool slowAsserts) {
        Contraction{mTaskGraph, scoreLimit, entryMTaskp, exitMTaskp, slowAsserts};
    }
};

//######################################################################
// DpiImportCallVisitor

// Scan node, indicate whether it contains a call to a DPI imported
// routine.
class DpiImportCallVisitor final : public VNVisitor {
    bool m_hasDpiHazard = false;  // Found a DPI import call.
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    // METHODS
    void visit(AstCFunc* nodep) override {
        if (!m_tracingCall) return;
        m_tracingCall = false;
        if (nodep->dpiImportWrapper()) {
            if (nodep->dpiPure() ? !v3Global.opt.threadsDpiPure()
                                 : !v3Global.opt.threadsDpiUnpure()) {
                m_hasDpiHazard = true;
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        // Enter the function and trace it
        m_tracingCall = true;
        iterate(nodep->funcp());
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DpiImportCallVisitor(AstNode* nodep) { iterate(nodep); }
    bool hasDpiHazard() const { return m_hasDpiHazard; }
    ~DpiImportCallVisitor() override = default;

private:
    VL_UNCOPYABLE(DpiImportCallVisitor);
};

//######################################################################
// FixDataHazards

class FixDataHazards final {
    //
    // Fix data hazards in the MTask graph.
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
    //   If we don't put unordered write-read pairs into some order at Verilation
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

    // TYPES
    // Sort LogicMTask objects into deterministic order by calling id()
    // which is a unique and stable serial number.
    struct MTaskIdLessThan final {
        bool operator()(const LogicMTask* lhsp, const LogicMTask* rhsp) const {
            return lhsp->id() < rhsp->id();
        }
    };
    using TasksByRank = std::map<uint32_t /*rank*/, std::set<LogicMTask*, MTaskIdLessThan>>;

    // MEMBERS
    V3Graph& m_mTaskGraph;  // The Mtask graph

    // CONSTRUCTORs
    FixDataHazards(const OrderGraph& orderGraph, V3Graph& mTaskGraph)
        : m_mTaskGraph{mTaskGraph} {
        // Rank the graph. DGS is faster than V3GraphAlg's recursive rank, and also allows us to
        // set up the OrderLogicVertex -> LogicMTask map at the same time.
        {
            GraphStreamUnordered serialize{&m_mTaskGraph};
            while (LogicMTask* const mtaskp
                   = const_cast<LogicMTask*>(static_cast<const LogicMTask*>(serialize.nextp()))) {
                // Compute and assign rank
                uint32_t rank = 0;
                for (V3GraphEdge& edge : mtaskp->inEdges()) {
                    rank = std::max(edge.fromp()->rank() + 1, rank);
                }
                mtaskp->rank(rank);

                // Set up the OrderLogicVertex -> LogicMTask map
                // Entry and exit MTasks have no MTaskMoveVertices under them, so move on
                if (mtaskp->vertexList().empty()) continue;
                // Otherwise there should be only one OrderMoveVertex in each MTask at this stage
                const OrderMoveVertex::List& vertexList = mtaskp->vertexList();
                UASSERT_OBJ(vertexList.hasSingleElement(), mtaskp, "Multiple OrderMoveVertex");
                const OrderMoveVertex* const mVtxp = vertexList.frontp();
                // Set up mapping back to the MTask from the OrderLogicVertex
                if (OrderLogicVertex* const lvtxp = mVtxp->logicp()) lvtxp->userp(mtaskp);
            }
        }

        // Gather all variables. SystemC vars will be handled slightly specially, so keep separate.
        std::vector<const OrderVarStdVertex*> regularVars;
        std::vector<const OrderVarStdVertex*> systemCVars;
        for (const V3GraphVertex& vtx : orderGraph.vertices()) {
            // Only consider OrderVarStdVertex which reflects
            // an actual lvalue assignment; the others do not.
            if (const OrderVarStdVertex* const vvtxp = vtx.cast<const OrderVarStdVertex>()) {
                if (vvtxp->vscp()->varp()->isSc()) {
                    systemCVars.push_back(vvtxp);
                } else {
                    regularVars.push_back(vvtxp);
                }
            }
        }

        // For each OrderVarVertex, look at its writer and reader mTaskGraphp.
        //
        // If there's a set of writers and readers at the same rank, we
        // know these are unordered with respect to one another, so merge
        // those mTaskGraphp all together.
        //
        // At this point, we have at most one merged mtask per rank (for a
        // given OVV.) Create edges across these remaining mTaskGraphp to ensure
        // they run in serial order (going along with the existing ranks.)
        //
        // NOTE: we don't update the CP's stored in the LogicMTasks to
        // reflect the changes we make to the graph. That's OK, as we
        // haven't yet initialized CPs when we call this routine.
        for (const OrderVarStdVertex* const varVtxp : regularVars) {
            // Build a set of mTaskGraphp, per rank, which access this var.
            // Within a rank, sort by MTaskID to avoid nondeterminism.
            TasksByRank tasksByRank;

            // Find all reader and writer tasks for this variable, add to
            // tasksByRank.
            findAdjacentTasks(varVtxp, tasksByRank);

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
            mergeSameRankTasks(tasksByRank);
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
            for (const OrderVarStdVertex* const varVtxp : systemCVars) {
                findAdjacentTasks(varVtxp, tasksByRank);
            }
            mergeSameRankTasks(tasksByRank);
        }

        // Handle nodes containing DPI calls, we want to serialize those
        // by default unless user gave --threads-dpi-concurrent.
        // Same basic strategy as above to serialize access to SC vars.
        if (!v3Global.opt.threadsDpiPure() || !v3Global.opt.threadsDpiUnpure()) {
            TasksByRank tasksByRank;
            for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) {
                LogicMTask& mtask = static_cast<LogicMTask&>(vtx);
                if (hasDpiHazard(&mtask)) tasksByRank[mtask.rank()].insert(&mtask);
            }
            mergeSameRankTasks(tasksByRank);
        }
    }

    // METHODS
    void findAdjacentTasks(const OrderVarStdVertex* varVtxp, TasksByRank& tasksByRank) {
        // Find all writer tasks for this variable, group by rank.
        for (const V3GraphEdge& edge : varVtxp->inEdges()) {
            if (const auto* const logicVtxp = edge.fromp()->cast<OrderLogicVertex>()) {
                LogicMTask* const writerMtaskp = static_cast<LogicMTask*>(logicVtxp->userp());
                tasksByRank[writerMtaskp->rank()].insert(writerMtaskp);
            }
        }
        // Not: Find all reader tasks for this variable, group by rank.
        // There was "broken" code here to find readers, but fixing it to
        // work properly harmed performance on some tests, see issue #3360.
    }
    void mergeSameRankTasks(const TasksByRank& tasksByRank) {
        LogicMTask* lastRecipientp = nullptr;
        for (const auto& pair : tasksByRank) {
            // Find the largest node at this rank, merge into it.  (If we
            // happen to find a huge node, this saves time in
            // partRedirectEdgesFrom() versus merging into an arbitrary node.)
            LogicMTask* recipientp = nullptr;
            for (LogicMTask* const mtaskp : pair.second) {
                if (!recipientp || (recipientp->cost() < mtaskp->cost())) recipientp = mtaskp;
            }
            UASSERT_OBJ(!lastRecipientp || (lastRecipientp->rank() < recipientp->rank()),
                        recipientp, "Merging must be on lower rank");

            for (LogicMTask* const donorp : pair.second) {
                // Merge donor into recipient.
                if (donorp == recipientp) continue;
                // Fix up the map, so donor's OLVs map to recipientp
                for (const OrderMoveVertex& vtx : donorp->vertexList()) {
                    vtx.logicp()->userp(recipientp);
                }
                // Move all vertices from donorp to recipientp
                recipientp->moveAllVerticesFrom(donorp);
                // Redirect edges from donorp to recipientp, delete donorp
                partRedirectEdgesFrom(m_mTaskGraph, recipientp, donorp, nullptr);
            }

            if (lastRecipientp && !lastRecipientp->hasRelativeMTask(recipientp)) {
                new MTaskEdge{&m_mTaskGraph, lastRecipientp, recipientp, 1};
            }
            lastRecipientp = recipientp;
        }
    }
    bool hasDpiHazard(LogicMTask* mtaskp) {
        for (const OrderMoveVertex& mVtx : mtaskp->vertexList()) {
            if (OrderLogicVertex* const lvtxp = mVtx.logicp()) {
                // NOTE: We don't handle DPI exports. If testbench code calls a
                // DPI-exported function at any time during eval() we may have
                // a data hazard. (Likewise in non-threaded mode if an export
                // messes with an ordered variable we're broken.)

                // Find all calls to DPI-imported functions, we can put those
                // into a serial order at least. That should solve the most
                // likely DPI-related data hazards.
                if (DpiImportCallVisitor{lvtxp->nodep()}.hasDpiHazard()) return true;
            }
        }
        return false;
    }

    VL_UNCOPYABLE(FixDataHazards);

public:
    static void apply(const OrderGraph& orderGraph, V3Graph& mTaskGraph) {
        FixDataHazards(orderGraph, mTaskGraph);
    }
};

//######################################################################
// Partitioner implementation

// Print debug stats about graphp whose nodes must be LogicMTask's.
static void debugMTaskGraphStats(V3Graph& graph, const string& stage) {
    if (!debug() && !dumpLevel() && !dumpGraphLevel()) return;

    UINFO(4, "\n");
    UINFO(4, " Stats for " << stage << endl);
    uint32_t mtaskCount = 0;
    uint32_t totalCost = 0;
    std::array<uint32_t, 32> mtaskCostHist;
    mtaskCostHist.fill(0);
    for (const V3GraphVertex& mtask : graph.vertices()) {
        ++mtaskCount;
        uint32_t mtaskCost = mtask.as<const LogicMTask>()->cost();
        totalCost += mtaskCost;

        unsigned log2Cost = 0;
        while (mtaskCost >>= 1) ++log2Cost;
        UASSERT(log2Cost < 32, "log2Cost overflow in debugMTaskGraphStats");
        ++mtaskCostHist[log2Cost];
    }
    UINFO(4, "  Total mtask cost = " << totalCost << "\n");
    UINFO(4, "  Mtask count = " << mtaskCount << "\n");
    UINFO(4, "  Avg cost / mtask = "
                 << ((mtaskCount > 0) ? cvtToStr(totalCost / mtaskCount) : "INF!") << "\n");
    UINFO(4, "  Histogram of mtask costs:\n");
    for (unsigned i = 0; i < 32; ++i) {
        if (mtaskCostHist[i]) {
            UINFO(4, "    2^" << i << ": " << mtaskCostHist[i] << endl);
            V3Stats::addStat("MTask graph, " + stage + ", mtask cost 2^" + (i < 10 ? " " : "")
                                 + cvtToStr(i),
                             mtaskCostHist[i]);
        }
    }

    if (mtaskCount < 1000) {
        string filePrefix("ordermv_");
        filePrefix += stage;
        if (dumpGraphLevel() >= 4) graph.dumpDotFilePrefixedAlways(filePrefix);
    }

    // Look only at the cost of each mtask, neglect communication cost.
    // This will show us how much parallelism we expect, assuming cache-miss
    // costs are minor and the cost of running logic is the dominant cost.
    const auto report = graph.parallelismReport(
        [](const V3GraphVertex* vtxp) { return vtxp->as<const LogicMTask>()->cost(); });
    V3Stats::addStat("MTask graph, " + stage + ", critical path cost", report.criticalPathCost());
    V3Stats::addStat("MTask graph, " + stage + ", total graph cost", report.totalGraphCost());
    V3Stats::addStat("MTask graph, " + stage + ", mtask count", report.vertexCount());
    V3Stats::addStat("MTask graph, " + stage + ", edge count", report.edgeCount());
    V3Stats::addStat("MTask graph, " + stage + ", parallelism factor", report.parallelismFactor());
    if (debug() >= 4) {
        UINFO(0, "\n");
        UINFO(0, "    MTask Parallelism estimate based costs at stage" << stage << ":\n");
        UINFO(0, "    Critical path cost = " << report.criticalPathCost() << "\n");
        UINFO(0, "    Total graph cost = " << report.totalGraphCost() << "\n");
        UINFO(0, "    MTask vertex count = " << report.vertexCount() << "\n");
        UINFO(0, "    Edge count = " << report.edgeCount() << "\n");
        UINFO(0, "    Parallelism factor = " << report.parallelismFactor() << "\n");
    }
}

// Print a hash of the shape of graphp.  If you are battling
// nondeterminism, this can help to pinpoint where in the pipeline it's
// creeping in.
static void hashGraphDebug(const V3Graph& graph, const char* debugName) {
    // Disabled when there are no nondeterminism issues in flight.
    if (!v3Global.opt.debugNondeterminism()) return;

    std::unordered_map<const V3GraphVertex*, uint32_t> vx2Id;
    unsigned id = 0;
    for (const V3GraphVertex& vtx : graph.vertices()) vx2Id[&vtx] = id++;
    unsigned hash = 0;
    for (const V3GraphVertex& vtx : graph.vertices()) {
        for (const V3GraphEdge& edge : vtx.outEdges()) {
            hash = vx2Id[edge.top()] + 31U * hash;  // The K&R hash function
        }
    }
    UINFO(0, "Hash of shape (not contents) of " << debugName << " = " << cvtToStr(hash) << endl);
}

//*************************************************************************
// Partitioner takes the fine-grained logic graph from V3Order and
// collapses it into a coarse-grained graph of LogicMTask's, each
// of which contains of set of the logic nodes from the fine-grained
// graph.

class Partitioner final {
    // MEMBERS
    OrderMoveGraph& m_moveGraph;  // Fine-grained dependency graph
    std::unique_ptr<V3Graph> m_mTaskGraphp{new V3Graph{}};  // The resulting MTask graph

    LogicMTask* m_entryMTaskp = nullptr;  // Singular source vertex of the dependency graph
    LogicMTask* m_exitMTaskp = nullptr;  // Singular sink vertex of the dependency graph

    // METHODS

    // Predicate function to determine what OrderMoveVertex to bypass when constructing the MTask
    // graph. The fine-grained dependency graph of OrderMoveVertex vertices is a bipartite graph
    // of:
    // - 1. OrderMoveVertex instances containing logic via OrderLogicVertex
    //      (OrderMoveVertex::logicp() != nullptr)
    // - 2. OrderMoveVertex instances containing an (OrderVarVertex, domain) pair
    // Our goal is to order the logic vertices. The second type of variable/domain vertices only
    // carry dependencies and are eventually discarded. In order to reduce the working set size of
    // Contraction, we 'bypass' and not create LogicMTask vertices for the variable vertices,
    // and instead add the transitive dependencies directly, but only if adding the transitive
    // edges directly does not require more dependency edges than keeping the intermediate vertex.
    // That is, we bypass a variable vertex if fanIn * fanOut <= fanIn + fanOut. This can only be
    // true if fanIn or fanOut are 1, or if they are both 2. This can cause significant reduction
    // in working set size.
    static bool bypassOk(OrderMoveVertex* mvtxp) {
        // Need to keep all logic vertices
        if (mvtxp->logicp()) return false;
        // Count fan-in, up to 3
        unsigned fanIn = 0;
        auto& inEdges = mvtxp->inEdges();
        for (auto it = inEdges.begin(); it != inEdges.end(); ++it) {
            if (++fanIn == 3) break;
        }
        UDEBUGONLY(UASSERT_OBJ(fanIn <= 3, mvtxp, "Should have stopped counting fanIn"););
        // If fanInn no more than one, bypass
        if (fanIn <= 1) return true;
        // Count fan-out, up to 3
        unsigned fanOut = 0;
        auto& outEdges = mvtxp->outEdges();
        for (auto it = outEdges.begin(); it != outEdges.end(); ++it) {
            if (++fanOut == 3) break;
        }
        UDEBUGONLY(UASSERT_OBJ(fanOut <= 3, mvtxp, "Should have stopped counting fanOut"););
        // If fan-out no more than one, bypass
        if (fanOut <= 1) return true;
        // They can only be (2, 2), (2, 3), (3, 2), (3, 3) at this point, bypass if (2, 2)
        return fanIn + fanOut == 4;
    }

    uint32_t setupMTaskDeps() VL_MT_DISABLED {
        uint32_t totalGraphCost = 0;

        // Artificial single entry point vertex in the MTask graph to allow sibling merges.
        // This is required as otherwise disjoint sub-graphs could not be merged, but the
        // coarsening algorithm assumes that the graph is connected.
        m_entryMTaskp = new LogicMTask{m_mTaskGraphp.get(), nullptr};

        // The V3InstrCount within LogicMTask will set user1 on each AST
        // node, to assert that we never count any node twice.
        const VNUser1InUse user1inUse;

        // Create the LogicMTasks for each OrderMoveVertex
        for (V3GraphVertex& vtx : m_moveGraph.vertices()) {
            OrderMoveVertex& mVtx = static_cast<OrderMoveVertex&>(vtx);
            if (bypassOk(&mVtx)) {
                mVtx.userp(nullptr);  // Set to nullptr to mark as bypassed
            } else {
                LogicMTask* const mtaskp = new LogicMTask{m_mTaskGraphp.get(), &mVtx};
                mVtx.userp(mtaskp);
                totalGraphCost += mtaskp->cost();
            }
        }

        // Artificial single exit point vertex in the MTask graph to allow sibling merges.
        // this enables merging MTasks with no downstream dependents if that is the ideal merge.
        m_exitMTaskp = new LogicMTask{m_mTaskGraphp.get(), nullptr};

        // Create the mtask->mtask dependency edges based on the dependencies between
        // OrderMoveVertex vertices.
        for (V3GraphVertex& vtx : m_mTaskGraphp->vertices()) {
            LogicMTask& mtask = static_cast<LogicMTask&>(vtx);

            // Entry and exit vertices handled separately
            if (VL_UNLIKELY((&mtask == m_entryMTaskp) || (&mtask == m_exitMTaskp))) continue;

            OrderMoveVertex::List& vertexList = mtask.vertexList();
            // At this point, there should only be one OrderMoveVertex per LogicMTask
            UASSERT_OBJ(vertexList.hasSingleElement(), &mtask, "Multiple OrderMoveVertex");
            OrderMoveVertex* const mVtxp = vertexList.frontp();
            UASSERT_OBJ(mVtxp->userp(), &mtask, "Bypassed OrderMoveVertex should not have MTask");

            // Function to add a edge to a dependent from 'mtaskp'
            const auto addEdge = [this, &mtask](LogicMTask* otherp) {
                UASSERT_OBJ(otherp != &mtask, &mtask, "Would create a cycle edge");
                if (mtask.hasRelativeMTask(otherp)) return;  // Don't create redundant edges.
                new MTaskEdge{m_mTaskGraphp.get(), &mtask, otherp, 1};
            };

            // Iterate downstream direct dependents
            for (V3GraphEdge& dEdge : mVtxp->outEdges()) {
                V3GraphVertex* const top = dEdge.top();
                if (LogicMTask* const otherp = static_cast<LogicMTask*>(top->userp())) {
                    // The opposite end of the edge is not a bypassed vertex, add as direct
                    // dependent
                    addEdge(otherp);
                } else {
                    // The opposite end of the edge is a bypassed vertex, add transitive dependents
                    for (V3GraphEdge& tEdge : top->outEdges()) {
                        LogicMTask* const transp = static_cast<LogicMTask*>(tEdge.top()->userp());
                        // The Move graph is bipartite (logic <-> var), and logic is never
                        // bypassed, hence 'transp' must be non nullptr.
                        UASSERT_OBJ(transp, mVtxp, "This cannot be a bypassed vertex");
                        addEdge(transp);
                    }
                }
            }
        }

        // Create Dependencies to/from the entry/exit vertices.
        for (V3GraphVertex& vtx : m_mTaskGraphp->vertices()) {
            LogicMTask& mtask = static_cast<LogicMTask&>(vtx);

            if (VL_UNLIKELY((&mtask == m_entryMTaskp) || (&mtask == m_exitMTaskp))) continue;

            // Add the entry/exit edges
            if (mtask.inEmpty()) new MTaskEdge{m_mTaskGraphp.get(), m_entryMTaskp, &mtask, 1};
            if (mtask.outEmpty()) new MTaskEdge{m_mTaskGraphp.get(), &mtask, m_exitMTaskp, 1};
        }

        return totalGraphCost;
    }

    // CONSTRUCTORS
    Partitioner(const OrderGraph& orderGraph, OrderMoveGraph& moveGraph)
        : m_moveGraph{moveGraph} {
        // Fill in the m_mTaskGraphp with LogicMTask's and their interdependencies.

        // Called by V3Order
        hashGraphDebug(m_moveGraph, "v3partition initial fine-grained deps");

        // Create the first MTasks. Initially, each MTask just wraps one
        // OrderMoveVertex. Over time, we'll merge MTasks together and
        // eventually each MTask will wrap a large number of MTaskMoveVertices
        // (and the logic nodes therein.)
        const uint32_t totalGraphCost = setupMTaskDeps();

        debugMTaskGraphStats(*m_mTaskGraphp, "initial");

        // For debug: print out the longest critical path.  This allows us to
        // verify that the costs look reasonable, that we aren't combining
        // nodes that should probably be split, etc.
        if (dumpLevel() >= 3) LogicMTask::dumpCpFilePrefixed(*m_mTaskGraphp, "cp");

        // Merge nodes that could present data hazards; see comment within.
        FixDataHazards::apply(orderGraph, *m_mTaskGraphp);
        debugMTaskGraphStats(*m_mTaskGraphp, "hazards");
        hashGraphDebug(*m_mTaskGraphp, "mTaskGraphpp after fixDataHazards()");

        // Setup the critical path into and out of each node.
        partInitCriticalPaths(*m_mTaskGraphp);
        hashGraphDebug(*m_mTaskGraphp, "after partInitCriticalPaths()");

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
        m_mTaskGraphp->orderPreRanked();

        // Merge MTask nodes together, repeatedly, until the CP budget is
        // reached.  Coarsens the graph, usually by several orders of
        // magnitude.
        //
        // Some tests disable this, hence the test on threadsCoarsen().
        // Coarsening is always enabled in production.
        if (v3Global.opt.threadsCoarsen()) {
            const int targetParFactor = v3Global.opt.threads();
            UASSERT(targetParFactor >= 2, "Should not reach Partitioner when --threads <= 1");

            // Set cpLimit to roughly totalGraphCost / nThreads
            //
            // Actually set it a bit lower, by a hardcoded fudge factor. This
            // results in more smaller mTaskGraphp, which helps reduce fragmentation
            // when scheduling them.
            const unsigned fudgeNumerator = 3;
            const unsigned fudgeDenominator = 5;
            const uint32_t cpLimit
                = ((totalGraphCost * fudgeNumerator) / (targetParFactor * fudgeDenominator));
            UINFO(4, "Partitioner set cpLimit = " << cpLimit << endl);

            Contraction::apply(*m_mTaskGraphp, cpLimit, m_entryMTaskp, m_exitMTaskp,
                               // --debugPartition is used by tests
                               // to enable slow assertions.
                               v3Global.opt.debugPartition());
            debugMTaskGraphStats(*m_mTaskGraphp, "contraction");
        }

        m_mTaskGraphp->removeTransitiveEdges();
        debugMTaskGraphStats(*m_mTaskGraphp, "transitive1");

        // Remove MTasks that have no logic in it rerouting the edges. Set user to indicate the
        // mtask on every underlying OrderMoveVertex. Clear vertex lists (used later).
        m_moveGraph.userClearVertices();
        for (V3GraphVertex* const vtxp : m_mTaskGraphp->vertices().unlinkable()) {
            LogicMTask* const mtaskp = vtxp->as<LogicMTask>();
            OrderMoveVertex::List& vertexList = mtaskp->vertexList();
            // Check if MTask is empty
            bool empty = true;
            for (OrderMoveVertex& mVtx : vertexList) {
                if (mVtx.logicp()) {
                    empty = false;
                    break;
                }
            }
            // If empty remove it now
            if (empty) {
                mtaskp->rerouteEdges(m_mTaskGraphp.get());
                VL_DO_DANGLING(mtaskp->unlinkDelete(m_mTaskGraphp.get()), mtaskp);
                continue;
            }
            // Annotate the underlying OrderMoveVertex vertices and unlink them
            while (OrderMoveVertex* const mVtxp = vertexList.unlinkFront()) mVtxp->userp(mtaskp);
        }
        m_mTaskGraphp->removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
    }
    ~Partitioner() = default;
    VL_UNCOPYABLE(Partitioner);
    VL_UNMOVABLE(Partitioner);

public:
    static std::unique_ptr<V3Graph> apply(const OrderGraph& orderGraph,
                                          OrderMoveGraph& moveGraph) {
        return std::move(Partitioner{orderGraph, moveGraph}.m_mTaskGraphp);
    }
};

// Sort LogicMTask vertices by their serial IDs.
struct MTaskVxIdLessThan final {
    bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        return lhsp->as<LogicMTask>()->id() < rhsp->as<LogicMTask>()->id();
    }
};

AstExecGraph* V3Order::createParallel(OrderGraph& orderGraph, const std::string& tag,
                                      const TrigToSenMap& trigToSen, bool slow) {
    UINFO(2, "  Constructing parallel code for '" + tag + "'");

    // For nondeterminism debug:
    hashGraphDebug(orderGraph, "V3OrderParallel's input OrderGraph");

    // Build the move graph
    OrderMoveDomScope::clear();
    const std::unique_ptr<OrderMoveGraph> moveGraphp
        = OrderMoveGraph::build(orderGraph, trigToSen);
    if (dumpGraphLevel() >= 9) moveGraphp->dumpDotFilePrefixed(tag + "_ordermv");

    // Partition moveGraphp into LogicMTask's. The partitioner will set userp() on each logic
    // vertex in the moveGraphp to the MTask it belongs to.
    const std::unique_ptr<V3Graph> mTaskGraphp = Partitioner::apply(orderGraph, *moveGraphp);
    if (dumpGraphLevel() >= 9) moveGraphp->dumpDotFilePrefixed(tag + "_ordermv_mtasks");

    // Some variable OrderMoveVertices are not assigned to an MTask. Reroute and delete these.
    for (V3GraphVertex* const vtxp : moveGraphp->vertices().unlinkable()) {
        OrderMoveVertex* const mVtxp = vtxp->as<OrderMoveVertex>();
        if (!mVtxp->userp()) {
            UASSERT_OBJ(!mVtxp->logicp(), mVtxp, "Logic OrderMoveVertex not assigned to mtask");
            mVtxp->rerouteEdges(moveGraphp.get());
            VL_DO_DANGLING(mVtxp->unlinkDelete(moveGraphp.get()), mVtxp);
        }
    }

    // Remove all edges from the move graph that cross between MTasks. Add logic to MTask lists.
    for (V3GraphVertex& vtx : moveGraphp->vertices()) {
        OrderMoveVertex* const mVtxp = vtx.as<OrderMoveVertex>();
        LogicMTask* const mtaskp = static_cast<LogicMTask*>(mVtxp->userp());
        // Add to list in MTask, in MoveGraph order. This should not be necessary, but see #4993.
        mtaskp->vertexList().linkBack(mVtxp);
        // Remove edges crossing between MTasks
        for (V3GraphEdge* const edgep : mVtxp->outEdges().unlinkable()) {
            const OrderMoveVertex* const toMVtxp = edgep->top()->as<OrderMoveVertex>();
            if (mtaskp != toMVtxp->userp()) VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }
    if (dumpGraphLevel() >= 9) moveGraphp->dumpDotFilePrefixed(tag + "_ordermv_pruned");

    // Create the AstExecGraph node which represents the execution of the MTask graph.
    FileLine* const rootFlp = v3Global.rootp()->fileline();
    AstExecGraph* const execGraphp = new AstExecGraph{rootFlp, tag};
    V3Graph* const depGraphp = execGraphp->depGraphp();

    // Translate the LogicMTask graph into the corresponding ExecMTask graph,
    // which will outlive ordering.
    std::unordered_map<const LogicMTask*, ExecMTask*> logicMTaskToExecMTask;
    OrderMoveGraphSerializer serializer{*moveGraphp};
    V3OrderCFuncEmitter emitter{tag, slow};
    GraphStream<MTaskVxIdLessThan> mtaskStream{mTaskGraphp.get()};
    while (const V3GraphVertex* const vtxp = mtaskStream.nextp()) {
        const LogicMTask* const cMTaskp = vtxp->as<LogicMTask>();
        LogicMTask* const mTaskp = const_cast<LogicMTask*>(cMTaskp);

        // Add initially ready vertices within this MTask to the serializer as seeds,
        // and unlink them from the vertex list in the MTask as we go. (The serializer
        // uses the list links in the vertex, so must unlink it here.)
        while (OrderMoveVertex* const mVtxp = mTaskp->vertexList().unlinkFront()) {
            if (mVtxp->inEmpty()) serializer.addSeed(mVtxp);
        }

        // Emit all logic within the MTask as they become ready
        OrderMoveDomScope* prevDomScopep = nullptr;
        while (OrderMoveVertex* const mVtxp = serializer.getNext()) {
            // We only really care about logic vertices
            if (OrderLogicVertex* const logicp = mVtxp->logicp()) {
                // Force a new function if the domain or scope changed, for better combining.
                OrderMoveDomScope* const domScopep = &mVtxp->domScope();
                if (domScopep != prevDomScopep) emitter.forceNewFunction();
                prevDomScopep = domScopep;
                // Emit the logic under this vertex
                emitter.emitLogic(logicp);
            }
            // Can delete the vertex now
            VL_DO_DANGLING(mVtxp->unlinkDelete(moveGraphp.get()), mVtxp);
        }

        // We have 2 objects, because AstMTaskBody is an AstNode, and ExecMTask is a GraphVertex.
        // To combine them would involve multiple inheritance.

        // Construct the actual MTaskBody
        AstMTaskBody* const bodyp = new AstMTaskBody{rootFlp};
        execGraphp->addMTaskBodiesp(bodyp);
        for (AstActive* const activep : emitter.getAndClearActiveps()) bodyp->addStmtsp(activep);
        UASSERT_OBJ(bodyp->stmtsp(), bodyp, "Should not try to create empty MTask");

        // Create the ExecMTask
        ExecMTask* const execMTaskp = new ExecMTask{depGraphp, bodyp};
        const bool newEntry = logicMTaskToExecMTask.emplace(mTaskp, execMTaskp).second;
        UASSERT_OBJ(newEntry, mTaskp, "LogicMTasks should be processed in dependencyorder");
        UINFO(3, "Final '" << tag << "' LogicMTask " << mTaskp->id() << " maps to ExecMTask"
                           << execMTaskp->id() << std::endl);

        // Add the dependency edges between ExecMTasks
        for (const V3GraphEdge& edge : mTaskp->inEdges()) {
            const V3GraphVertex* fromVxp = edge.fromp();
            const LogicMTask* const fromp = fromVxp->as<const LogicMTask>();
            new V3GraphEdge{depGraphp, logicMTaskToExecMTask.at(fromp), execMTaskp, 1};
        }
    }

    // Delete the remaining variable vertices
    for (V3GraphVertex* const vtxp : moveGraphp->vertices().unlinkable()) {
        if (!vtxp->as<OrderMoveVertex>()->logicp()) {
            VL_DO_DANGLING(vtxp->unlinkDelete(moveGraphp.get()), vtxp);
        }
    }

    UASSERT(moveGraphp->empty(), "Waiting vertices remain, but none are ready");
    OrderMoveDomScope::clear();

    return execGraphp;
}

void V3Order::selfTestParallel() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    PropagateCp<GraphWay::FORWARD>::selfTest();
    PropagateCp<GraphWay::REVERSE>::selfTest();
    Contraction::selfTest();
}
