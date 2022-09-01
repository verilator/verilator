// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's logic to mtask partitioner
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Partition.h"

#include "V3Config.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3GraphStream.h"
#include "V3InstrCount.h"
#include "V3List.h"
#include "V3Os.h"
#include "V3PairingHeap.h"
#include "V3PartitionGraph.h"
#include "V3Scoreboard.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <array>
#include <list>
#include <memory>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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
// and we probably don't want a huge number of mtasks in practice anyway
// (50 to 100 is typical.)
//
// If the user doesn't give one with '--threads-max-mtasks', we'll set the
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

struct EdgeKey {
    // Node: Structure layout chosen to minimize padding in PairingHeao<*>::Node
    uint64_t m_id;  // Unique ID part of edge score
    uint32_t m_score;  // Score part of ID
    void increase(uint32_t score) {
#if VL_DEBUG
        UASSERT(score >= m_score, "Must increase");
#endif
        m_score = score;
    }
    bool operator<(const EdgeKey& other) const {
        // First by Score then by ID
        return m_score < other.m_score || (m_score == other.m_score && m_id < other.m_id);
    }
};

using EdgeHeap = PairingHeap<EdgeKey>;

//=============================================================================
// LogicMTask

class LogicMTask final : public AbstractLogicMTask {
    template <GraphWay::en T_Way>
    friend class PartPropagateCp;

public:
    // TYPES
    using VxList = std::list<MTaskMoveVertex*>;

    struct CmpLogicMTask {
        bool operator()(const LogicMTask* ap, const LogicMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

private:
    // MEMBERS

    // Set of MTaskMoveVertex's assigned to this mtask. LogicMTask does not
    // own the MTaskMoveVertex objects, we merely keep pointers to them
    // here.
    VxList m_vertices;

    // Cost estimate for this LogicMTask, derived from V3InstrCount.
    // In abstract time units.
    uint32_t m_cost = 0;

    // Cost of critical paths going FORWARD from graph-start to the start
    // of this vertex, and also going REVERSE from the end of the graph to
    // the end of the vertex. Same units as m_cost.
    std::array<uint32_t, GraphWay::NUM_WAYS> m_critPathCost;

    uint32_t m_serialId;  // Unique MTask ID number

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
    V3List<SiblingMC*> m_aSiblingMCs;
    // List of SiblingMCs for which this is the lower ID MTask (m_bp in SiblingMC)
    V3List<SiblingMC*> m_bSiblingMCs;

public:
    // CONSTRUCTORS
    LogicMTask(V3Graph* graphp, MTaskMoveVertex* mtmvVxp)
        : AbstractLogicMTask{graphp} {
        for (uint32_t& item : m_critPathCost) item = 0;
        if (mtmvVxp) {  // Else null for test
            m_vertices.push_back(mtmvVxp);
            if (const OrderLogicVertex* const olvp = mtmvVxp->logicp()) {
                m_cost += V3InstrCount::count(olvp->nodep(), true);
            }
        }
        // Start at 1, so that 0 indicates no mtask ID.
        static uint32_t s_nextId = 1;
        m_serialId = s_nextId++;
        UASSERT(s_nextId < 0xFFFFFFFFUL, "Too many mtasks");
    }

    // METHODS
    std::set<LogicMTask*>& siblings() { return m_siblings; };
    V3List<SiblingMC*>& aSiblingMCs() { return m_aSiblingMCs; };
    V3List<SiblingMC*>& bSiblingMCs() { return m_bSiblingMCs; };

    void moveAllVerticesFrom(LogicMTask* otherp) {
        // splice() is constant time
        m_vertices.splice(m_vertices.end(), otherp->m_vertices);
        m_cost += otherp->m_cost;
    }
    virtual const VxList* vertexListp() const override { return &m_vertices; }
    static uint64_t incGeneration() {
        static uint64_t s_generation = 0;
        ++s_generation;
        return s_generation;
    }

    // Use this instead of pointer-compares to compare LogicMTasks. Avoids
    // nondeterministic output.  Also name mtasks based on this number in
    // the final C++ output.
    virtual uint32_t id() const override { return m_serialId; }
    void id(uint32_t id) { m_serialId = id; }
    // Abstract cost of every logic mtask
    virtual uint32_t cost() const override { return m_cost; }
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
#if VL_DEBUG
        UASSERT_STATIC(stepCost >= cost, "stepped cost error exceeded");
        UASSERT_STATIC(stepCost <= ((cost * 11 / 10)), "stepped cost error exceeded");
#endif
        return stepCost;
#else
        return cost;
#endif
    }

    template <GraphWay::en T_Way>
    void addRelativeEdge(MTaskEdge* edgep);
    template <GraphWay::en T_Way>
    void stealRelativeEdge(MTaskEdge* edgep);
    template <GraphWay::en T_Way>
    void removeRelativeEdge(MTaskEdge* edgep);

    void addRelativeMTask(LogicMTask* relativep) {
        // Add the relative to connecting edge map
        VL_ATTR_UNUSED const bool exits = !m_edgeSet.emplace(relativep).second;
#if VL_DEBUG
        UASSERT(!exits, "Adding existing relative");
#endif
    }
    void removeRelativeMTask(LogicMTask* relativep) {
        VL_ATTR_UNUSED const size_t removed = m_edgeSet.erase(relativep);
#if VL_DEBUG
        UASSERT(removed, "Relative should have been in set");
#endif
    }
    bool hasRelativeMTask(LogicMTask* relativep) const { return m_edgeSet.count(relativep); }

    void checkRelativesCp(GraphWay way) const;

    virtual string name() const override {
        // Display forward and reverse critical path costs. This gives a quick
        // read on whether graph partitioning looks reasonable or bad.
        std::ostringstream out;
        out << "mt" << m_serialId << "." << this << " [b" << m_critPathCost[GraphWay::FORWARD]
            << " a" << m_critPathCost[GraphWay::REVERSE] << " c" << cost();
        return out.str();
    }

    void setCritPathCost(GraphWay way, uint32_t cost) { m_critPathCost[way] = cost; }
    uint32_t critPathCost(GraphWay way) const { return m_critPathCost[way]; }
    uint32_t critPathCostWithout(GraphWay way, const V3GraphEdge* withoutp) const;

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
        for (const V3GraphEdge* followp = fromp->outBeginp(); followp;
             followp = followp->outNextp()) {
            if (followp == excludedEdgep) continue;
            LogicMTask* const nextp = static_cast<LogicMTask*>(followp->top());
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

    static void dumpCpFilePrefixed(const V3Graph* graphp, const string& nameComment);

private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(LogicMTask);
};

//######################################################################
// MTask utility classes

// Sort AbstractMTask objects into deterministic order by calling id()
// which is a unique and stable serial number.
class MTaskIdLessThan final {
public:
    MTaskIdLessThan() = default;
    virtual ~MTaskIdLessThan() = default;
    virtual bool operator()(const AbstractMTask* lhsp, const AbstractMTask* rhsp) const {
        return lhsp->id() < rhsp->id();
    }
};

struct MergeCandidateKey {
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
private:
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
    SiblingMC* toSiblingMC();  // Instead of dynamic_cast
    const SiblingMC* toSiblingMC() const;  // Instead of dynamic_cast
    MTaskEdge* toMTaskEdge();  // Instead of dynamic_cast
    const MTaskEdge* toMTaskEdge() const;  // Instead of dynamic_cast
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

    V3ListEnt<SiblingMC*> m_aEnt;  // List entry for m_ap->aSiblingMCs()
    V3ListEnt<SiblingMC*> m_bEnt;  // List entry for m_bp->bSiblingMCs()

public:
    // CONSTRUCTORS
    SiblingMC() = delete;
    SiblingMC(LogicMTask* ap, LogicMTask* bp)
        : MergeCandidate{/* isSiblingMC: */ true}
        , m_ap{ap}
        , m_bp{bp} {
        // Storage management depends on this
        UASSERT(ap->id() > bp->id(), "Should be ordered");
        UDEBUGONLY(UASSERT(ap->siblings().count(bp), "Should be in sibling map"););
        m_aEnt.pushBack(m_ap->aSiblingMCs(), this);
        m_bEnt.pushBack(m_bp->bSiblingMCs(), this);
    }
    ~SiblingMC() = default;

    // METHODS
    SiblingMC* aNextp() const { return m_aEnt.nextp(); }
    SiblingMC* bNextp() const { return m_bEnt.nextp(); }
    void unlinkA() {
        VL_ATTR_UNUSED const size_t removed = m_ap->siblings().erase(m_bp);
        UDEBUGONLY(UASSERT(removed == 1, "Should have been in sibling set"););
        m_aEnt.unlink(m_ap->aSiblingMCs(), this);
    }
    void unlinkB() { m_bEnt.unlink(m_bp->bSiblingMCs(), this); }

    LogicMTask* ap() const { return m_ap; }
    LogicMTask* bp() const { return m_bp; }
    bool mergeWouldCreateCycle() const {
        return (LogicMTask::pathExistsFrom(m_ap, m_bp, nullptr)
                || LogicMTask::pathExistsFrom(m_bp, m_ap, nullptr));
    }
};

static_assert(!std::is_polymorphic<SiblingMC>::value, "Should not have a vtable");

// GraphEdge for the MTask graph
class MTaskEdge final : public V3GraphEdge, public MergeCandidate {
    friend class LogicMTask;
    template <GraphWay::en T_Way>
    friend class PartPropagateCp;

    // MEMBERS
    // This edge can be in 2 EdgeHeaps, one forward and one reverse. We allocate the heap nodes
    // directly within the edge as they are always required and this makes association cheap.
    EdgeHeap::Node m_edgeHeapNode[GraphWay::NUM_WAYS];

public:
    // CONSTRUCTORS
    MTaskEdge(V3Graph* graphp, LogicMTask* fromp, LogicMTask* top, int weight)
        : V3GraphEdge{graphp, fromp, top, weight}
        , MergeCandidate{/* isSiblingMC: */ false} {
        fromp->addRelativeMTask(top);
        fromp->addRelativeEdge<GraphWay::FORWARD>(this);
        top->addRelativeEdge<GraphWay::REVERSE>(this);
    }
    // METHODS
    LogicMTask* furtherMTaskp(GraphWay way) const {
        return static_cast<LogicMTask*>(this->furtherp(way));
    }
    LogicMTask* fromMTaskp() const { return static_cast<LogicMTask*>(fromp()); }
    LogicMTask* toMTaskp() const { return static_cast<LogicMTask*>(top()); }
    bool mergeWouldCreateCycle() const {
        return LogicMTask::pathExistsFrom(fromMTaskp(), toMTaskp(), this);
    }
    // Following initial assignment of critical paths, clear this MTaskEdge
    // out of the edge-map for each node and reinsert at a new location
    // with updated critical path.
    void resetCriticalPaths() {
        LogicMTask* const fromp = fromMTaskp();
        LogicMTask* const top = toMTaskp();
        fromp->removeRelativeEdge<GraphWay::FORWARD>(this);
        top->removeRelativeEdge<GraphWay::REVERSE>(this);
        fromp->addRelativeEdge<GraphWay::FORWARD>(this);
        top->addRelativeEdge<GraphWay::REVERSE>(this);
    }

    uint32_t cachedCp(GraphWay way) const { return m_edgeHeapNode[way].key().m_score; }

    // Convert from the address of the m_edgeHeapNode[way] in an MTaskEdge back to the MTaskEdge
    static const MTaskEdge* toMTaskEdge(GraphWay way, const EdgeHeap::Node* nodep) {
        const size_t offset = VL_OFFSETOF(MTaskEdge, m_edgeHeapNode[way]);
        return reinterpret_cast<const MTaskEdge*>(reinterpret_cast<uintptr_t>(nodep) - offset);
    }

private:
    VL_UNCOPYABLE(MTaskEdge);
};

template <GraphWay::en T_Way>
void LogicMTask::addRelativeEdge(MTaskEdge* edgep) {
    constexpr GraphWay way{T_Way};
    constexpr GraphWay inv = way.invert();
    // Add to the edge heap
    LogicMTask* const relativep = edgep->furtherMTaskp(way);
    // Value is !way cp to this edge
    const uint32_t cp = relativep->stepCost() + relativep->critPathCost(inv);
    //
    m_edgeHeap[way].insert(&edgep->m_edgeHeapNode[way], {relativep->id(), cp});
}

template <GraphWay::en T_Way>
void LogicMTask::stealRelativeEdge(MTaskEdge* edgep) {
    constexpr GraphWay way{T_Way};
    // Make heap node insertable, ruining the heap it is currently in.
    edgep->m_edgeHeapNode[way].yank();
    // Add the edge as new
    addRelativeEdge<T_Way>(edgep);
}

template <GraphWay::en T_Way>
void LogicMTask::removeRelativeEdge(MTaskEdge* edgep) {
    constexpr GraphWay way{T_Way};
    // Remove from the edge heap
    m_edgeHeap[way].remove(&edgep->m_edgeHeapNode[way]);
}

void LogicMTask::checkRelativesCp(GraphWay way) const {
    for (V3GraphEdge* edgep = beginp(way); edgep; edgep = edgep->nextp(way)) {
        const LogicMTask* const relativep = static_cast<const LogicMTask*>(edgep->furtherp(way));
        const uint32_t cachedCp = static_cast<MTaskEdge*>(edgep)->cachedCp(way);
        const uint32_t cp = relativep->critPathCost(way.invert()) + relativep->stepCost();
        partCheckCachedScoreVsActual(cachedCp, cp);
    }
}

uint32_t LogicMTask::critPathCostWithout(GraphWay way, const V3GraphEdge* withoutp) const {
    // Compute the critical path cost wayward to this node, without considering edge 'withoutp'.
    // We need to look at two edges at most, the critical path if that is not via 'withoutp',
    // or the second-worst path, if the critical path is via 'withoutp'.
#if VL_DEBUG
    UASSERT(withoutp->furtherp(way) == this,
            "In critPathCostWithout(), edge 'withoutp' must further to 'this'");
#endif
    const GraphWay inv = way.invert();
    const EdgeHeap& edgeHeap = m_edgeHeap[inv];
    const EdgeHeap::Node* const maxp = edgeHeap.max();
    if (!maxp) return 0;
    if (MTaskEdge::toMTaskEdge(inv, maxp) != withoutp) return maxp->key().m_score;
    const EdgeHeap::Node* const secp = edgeHeap.secondMax();
    if (!secp) return 0;
    return secp->key().m_score;
}

void LogicMTask::dumpCpFilePrefixed(const V3Graph* graphp, const string& nameComment) {
    const string filename = v3Global.debugFilename(nameComment) + ".txt";
    UINFO(1, "Writing " << filename << endl);
    const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
    std::ostream* const osp = &(*ofp);  // &* needed to deref unique_ptr
    if (osp->fail()) v3fatalStatic("Can't write " << filename);

    // Find start vertex with longest CP
    LogicMTask* startp = nullptr;
    for (V3GraphVertex* vxp = graphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        LogicMTask* const mtaskp = static_cast<LogicMTask*>(vxp);
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
    for (LogicMTask* nextp = startp; nextp;) {
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
        for (VxList::const_iterator lit = mtaskp->vertexListp()->begin();
             lit != mtaskp->vertexListp()->end(); ++lit) {
            const OrderLogicVertex* const logicp = (*lit)->logicp();
            if (!logicp) continue;
            if (false) {
                // Show nodes only
                *osp << "> ";
                logicp->nodep()->dumpTree(*osp);
            } else {
                // Show nodes with hierarchical costs
                V3InstrCount::count(logicp->nodep(), false, osp);
            }
        }
    }
}

// Instead of dynamic cast
SiblingMC* MergeCandidate::toSiblingMC() {
    return isSiblingMC() ? static_cast<SiblingMC*>(this) : nullptr;
}

MTaskEdge* MergeCandidate::toMTaskEdge() {
    return isSiblingMC() ? nullptr : static_cast<MTaskEdge*>(this);
}

const SiblingMC* MergeCandidate::toSiblingMC() const {
    return isSiblingMC() ? static_cast<const SiblingMC*>(this) : nullptr;
}

const MTaskEdge* MergeCandidate::toMTaskEdge() const {
    return isSiblingMC() ? nullptr : static_cast<const MTaskEdge*>(this);
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
    // length if we merge these mtasks.  ("Local" means the longest
    // critical path running through the merged node.)
    const LogicMTask* const top = static_cast<LogicMTask*>(edgep->top());
    const LogicMTask* const fromp = static_cast<LogicMTask*>(edgep->fromp());
    const uint32_t mergedCpCostFwd = std::max(fromp->critPathCost(GraphWay::FORWARD),
                                              top->critPathCostWithout(GraphWay::FORWARD, edgep));
    const uint32_t mergedCpCostRev = std::max(fromp->critPathCostWithout(GraphWay::REVERSE, edgep),
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

// ######################################################################
//  Vertex utility classes

class OrderByPtrId final {
    PartPtrIdMap m_ids;

public:
    virtual bool operator()(const OrderVarStdVertex* lhsp, const OrderVarStdVertex* rhsp) const {
        const uint64_t l_id = m_ids.findId(lhsp);
        const uint64_t r_id = m_ids.findId(rhsp);
        return l_id < r_id;
    }
};

//######################################################################
// PartParallelismEst - Estimate parallelism of graph

class PartParallelismEst final {
    // MEMBERS
    const V3Graph* const m_graphp;  // Mtask-containing graph

    // Total cost of evaluating the whole graph.
    // The ratio of m_totalGraphCost to longestCpCost gives us an estimate
    // of the parallelizability of this graph which is only as good as the
    // guess returned by LogicMTask::cost().
    uint32_t m_totalGraphCost = 0;

    // Cost of the longest critical path, in abstract units (the same units
    // returned by the vertexCost)
    uint32_t m_longestCpCost = 0;

    size_t m_vertexCount = 0;  // Number of vertexes calculated
    size_t m_edgeCount = 0;  // Number of edges calculated

public:
    // CONSTRUCTORS
    explicit PartParallelismEst(const V3Graph* graphp)
        : m_graphp{graphp} {}

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
        std::unordered_map<const V3GraphVertex*, uint32_t> critPaths;
        GraphStreamUnordered serialize(m_graphp);
        for (const V3GraphVertex* vertexp; (vertexp = serialize.nextp());) {
            ++m_vertexCount;
            uint32_t cpCostToHere = 0;
            for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
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
    void statsReport(const string& stage) const {
        V3Stats::addStat("MTask graph, " + stage + ", critical path cost", m_longestCpCost);
        V3Stats::addStat("MTask graph, " + stage + ", total graph cost", m_totalGraphCost);
        V3Stats::addStat("MTask graph, " + stage + ", mtask count", m_vertexCount);
        V3Stats::addStat("MTask graph, " + stage + ", edge count", m_edgeCount);
        V3Stats::addStat("MTask graph, " + stage + ", parallelism factor", parallelismFactor());
    }
    void debugReport() const {
        UINFO(0, "    Critical path cost = " << m_longestCpCost << endl);
        UINFO(0, "    Total graph cost = " << m_totalGraphCost << endl);
        UINFO(0, "    MTask vertex count = " << m_vertexCount << endl);
        UINFO(0, "    Edge count = " << m_edgeCount << endl);
        UINFO(0, "    Parallelism factor = " << parallelismFactor() << endl);
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
    const GraphWay rev = way.invert();
    for (const V3GraphVertex* vertexp; (vertexp = order.nextp());) {
        const LogicMTask* const mtaskcp = static_cast<const LogicMTask*>(vertexp);
        LogicMTask* const mtaskp = const_cast<LogicMTask*>(mtaskcp);
        uint32_t cpCost = 0;
#if VL_DEBUG
        std::unordered_set<V3GraphVertex*> relatives;
#endif
        for (V3GraphEdge* edgep = vertexp->beginp(rev); edgep; edgep = edgep->nextp(rev)) {
#if VL_DEBUG
            // Run a few asserts on the initial mtask graph,
            // while we're iterating through...
            UASSERT_OBJ(edgep->weight() != 0, mtaskp, "Should be no cut edges in mtasks graph");
            UASSERT_OBJ(relatives.find(edgep->furtherp(rev)) == relatives.end(), mtaskp,
                        "Should be no redundant edges in mtasks graph");
            relatives.insert(edgep->furtherp(rev));
#endif
            const LogicMTask* const relativep = static_cast<LogicMTask*>(edgep->furtherp(rev));
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
static void partInitCriticalPaths(V3Graph* mtasksp) {
    partInitHalfCriticalPaths(GraphWay::FORWARD, mtasksp, false);
    partInitHalfCriticalPaths(GraphWay::REVERSE, mtasksp, false);

    // Reset all MTaskEdges so that 'm_edges' will show correct CP numbers.
    // They would have been all zeroes on initial creation of the MTaskEdges.
    for (V3GraphVertex* vxp = mtasksp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            MTaskEdge* const mtedgep = dynamic_cast<MTaskEdge*>(edgep);
            mtedgep->resetCriticalPaths();
        }
    }
}

// Do an EXPENSIVE check to make sure that all incremental CP updates have
// gone correctly.
static void partCheckCriticalPaths(V3Graph* mtasksp) {
    partInitHalfCriticalPaths(GraphWay::FORWARD, mtasksp, true);
    partInitHalfCriticalPaths(GraphWay::REVERSE, mtasksp, true);
    for (V3GraphVertex* vxp = mtasksp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        const LogicMTask* const mtaskp = static_cast<LogicMTask*>(vxp);
        mtaskp->checkRelativesCp(GraphWay::FORWARD);
        mtaskp->checkRelativesCp(GraphWay::REVERSE);
    }
}

// ######################################################################
//  PartPropagateCp

// Propagate increasing critical path (CP) costs through a graph.
//
// Usage:
//  * Client increases the cost and/or CP at a node or small set of nodes
//    (often a pair in practice, eg. edge contraction.)
//  * Client calls PartPropagateCp::cpHasIncreased() one or more times.
//    Each call indicates that the inclusive CP of some "seed" vertex
//    has increased to a given value.
//    * NOTE: PartPropagateCp will neither read nor modify the cost
//      or CPs at the seed vertices, it only accesses and modifies
//      vertices wayward from the seeds.
//  * Client calls PartPropagateCp::go(). Internally, this iteratively
//    propagates the new CPs wayward through the graph.
//
template <GraphWay::en T_Way>
class PartPropagateCp final {
    // TYPES

    // We keep pending vertices in a heap during critical path propagation
    struct PendingKey {
        LogicMTask* m_mtaskp;  // The vertex in the heap
        uint32_t m_score;  // The score of this entry
        void increase(uint32_t score) {
#if VL_DEBUG
            UASSERT(score >= m_score, "Must increase");
#endif
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
    std::set<LogicMTask*> m_seen;  // Used only with slow asserts to check mtasks visited only once

public:
    // CONSTRUCTORS
    PartPropagateCp(bool slowAsserts)
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
        for (MTaskEdge *edgep = static_cast<MTaskEdge*>(vxp->beginp(way)), *nextp; edgep;
             edgep = nextp) {
            // Fetch early as likely cache miss
            nextp = static_cast<MTaskEdge*>(edgep->nextp(way));

            LogicMTask* const relativep = edgep->furtherMTaskp(way);
            EdgeHeap::Node& edgeHeapNode = edgep->m_edgeHeapNode[inv];
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
                // important property of PartPropagateCp which allows it to be far
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
    VL_DEBUG_FUNC;
    VL_UNCOPYABLE(PartPropagateCp);
};

class PartPropagateCpSelfTest final {
private:
    // MEMBERS
    V3Graph m_graph;  // A graph
    LogicMTask* m_vx[50];  // All vertices within the graph

    // CONSTRUCTORS
    PartPropagateCpSelfTest() = default;
    ~PartPropagateCpSelfTest() = default;

    void go() {
        // Generate a pseudo-random graph
        std::array<uint64_t, 2> rngState
            = {{0x12345678ULL, 0x9abcdef0ULL}};  // GCC 3.8.0 wants {{}}
        // Create 50 vertices
        for (auto& i : m_vx) {
            i = new LogicMTask{&m_graph, nullptr};
            i->setCost(1);
        }
        // Create 250 edges at random. Edges must go from
        // lower-to-higher index vertices, so we get a DAG.
        for (unsigned i = 0; i < 250; ++i) {
            const unsigned idx1 = V3Os::rand64(rngState) % 50;
            const unsigned idx2 = V3Os::rand64(rngState) % 50;
            if (idx1 > idx2) {
                if (!m_vx[idx2]->hasRelativeMTask(m_vx[idx1])) {
                    new MTaskEdge{&m_graph, m_vx[idx2], m_vx[idx1], 1};
                }
            } else if (idx2 > idx1) {
                if (!m_vx[idx1]->hasRelativeMTask(m_vx[idx2])) {
                    new MTaskEdge{&m_graph, m_vx[idx1], m_vx[idx2], 1};
                }
            }
        }

        partInitCriticalPaths(&m_graph);

        // This SelfTest class is also the T_CostAccessor
        PartPropagateCp<GraphWay::FORWARD> prop(true);

        // Seed the propagator with every input node;
        // This should result in the complete graph getting all CP's assigned.
        for (const auto& i : m_vx) {
            if (!i->inBeginp()) prop.cpHasIncreased(i, 1 /* inclusive CP starts at 1 */);
        }

        // Run the propagator.
        prop.go();

        // Finally, confirm that the entire graph appears to have correct CPs.
        partCheckCriticalPaths(&m_graph);
    }

public:
    static void selfTest() { PartPropagateCpSelfTest().go(); }
};

// Merge edges from a LogicMtask.
//
// This code removes adjacent edges. When this occurs, mark it in need
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
static void partRedirectEdgesFrom(V3Graph* graphp, LogicMTask* recipientp, LogicMTask* donorp,
                                  MergeCandidateScoreboard* sbp) {

    // Process outgoing edges
    MTaskEdge* outNextp = static_cast<MTaskEdge*>(donorp->outBeginp());
    while (outNextp) {
        MTaskEdge* const edgep = outNextp;
        LogicMTask* const relativep = outNextp->toMTaskp();
        outNextp = static_cast<MTaskEdge*>(outNextp->outNextp());

        relativep->removeRelativeEdge<GraphWay::REVERSE>(edgep);

        if (recipientp->hasRelativeMTask(relativep)) {
            // An edge already exists between recipient and relative of donor.
            // Mark it in need of a rescore
            if (sbp) {
                if (sbp->contains(edgep)) sbp->remove(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep(GraphWay::FORWARD, relativep));
#if VL_DEBUG
                UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge");
#endif
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
    MTaskEdge* inNextp = static_cast<MTaskEdge*>(donorp->inBeginp());
    while (inNextp) {
        MTaskEdge* const edgep = inNextp;
        LogicMTask* const relativep = inNextp->fromMTaskp();
        inNextp = static_cast<MTaskEdge*>(inNextp->inNextp());

        relativep->removeRelativeMTask(donorp);
        relativep->removeRelativeEdge<GraphWay::FORWARD>(edgep);

        if (relativep->hasRelativeMTask(recipientp)) {
            // An edge already exists between recipient and relative of donor.
            // Mark it in need of a rescore
            if (sbp) {
                if (sbp->contains(edgep)) sbp->remove(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep(GraphWay::REVERSE, relativep));
#if VL_DEBUG
                UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge");
#endif
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
    VL_DO_DANGLING(donorp->unlinkDelete(graphp), donorp);
}

//######################################################################
// PartContraction

// Perform edge or sibling contraction on the partition graph
class PartContraction final {
private:
    // TYPES
    // New CP information for mtaskp reflecting an upcoming merge
    struct NewCp {
        uint32_t cp;
        uint32_t propagateCp;
        bool propagate;
    };

    // MEMBERS
    V3Graph* const m_mtasksp;  // Mtask graph
    uint32_t m_scoreLimit;  // Sloppy score allowed when picking merges
    uint32_t m_scoreLimitBeforeRescore = 0xffffffff;  // Next score rescore at
    unsigned m_mergesSinceRescore = 0;  // Merges since last rescore
    const bool m_slowAsserts;  // Take extra time to validate algorithm
    MergeCandidateScoreboard m_sb;  // Scoreboard

    PartPropagateCp<GraphWay::FORWARD> m_forwardPropagator{m_slowAsserts};  // Forward propagator
    PartPropagateCp<GraphWay::REVERSE> m_reversePropagator{m_slowAsserts};  // Reverse propagator

public:
    // CONSTRUCTORS
    PartContraction(V3Graph* mtasksp, uint32_t scoreLimit, bool slowAsserts)
        : m_mtasksp{mtasksp}
        , m_scoreLimit{scoreLimit}
        , m_slowAsserts{slowAsserts} {}

    // METHODS
    void go() {
        unsigned maxMTasks = v3Global.opt.threadsMaxMTasks();
        if (maxMTasks == 0) {  // Unspecified so estimate
            if (v3Global.opt.threads() > 1) {
                maxMTasks = (PART_DEFAULT_MAX_MTASKS_PER_THREAD * v3Global.opt.threads());
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

        for (V3GraphVertex* itp = m_mtasksp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            itp->userp(nullptr);  // Reset user value. Used by PartPropagateCp.
            std::unordered_set<const V3GraphVertex*> neighbors;
            for (V3GraphEdge* edgep = itp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                m_sb.add(static_cast<MTaskEdge*>(edgep));
                if (m_slowAsserts) {
                    UASSERT_OBJ(neighbors.find(edgep->top()) == neighbors.end(), itp,
                                "Redundant edge found in input to PartContraction()");
                }
                neighbors.insert(edgep->top());
            }
            siblingPairFromRelatives<GraphWay::REVERSE, true>(itp);
            siblingPairFromRelatives<GraphWay::FORWARD, true>(itp);
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

                    // Except, if we have too many mtasks, raise the score
                    // limit and keep going...
                    unsigned mtaskCount = 0;
                    for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp(); vxp;
                         vxp = vxp->verticesNextp()) {
                        ++mtaskCount;
                    }
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
                    delete smcp;
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
        for (SiblingMC *smcp = mtaskp->aSiblingMCs().begin(), *nextp;  // lintok-begin-on-ref
             smcp; smcp = nextp) {
            nextp = smcp->aNextp();
            m_sb.remove(smcp);
            smcp->unlinkB();
            delete smcp;
        }
        for (SiblingMC *smcp = mtaskp->bSiblingMCs().begin(), *nextp;  // lintok-begin-on-ref
             smcp; smcp = nextp) {
            nextp = smcp->bNextp();
            m_sb.remove(smcp);
            smcp->unlinkA();
            delete smcp;
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
        recipientp->aSiblingMCs().reset();
        recipientp->bSiblingMCs().reset();
    }

    void contract(MergeCandidate* mergeCanp) {
        LogicMTask* top = nullptr;
        LogicMTask* fromp = nullptr;
        MTaskEdge* const mergeEdgep = mergeCanp->toMTaskEdge();
        SiblingMC* const mergeSibsp = mergeCanp->toSiblingMC();
        if (mergeEdgep) {
            top = static_cast<LogicMTask*>(mergeEdgep->top());
            fromp = static_cast<LogicMTask*>(mergeEdgep->fromp());
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
        // Doing this before merging the mtasks lets us often avoid
        // recursing through either incoming or outgoing edges on one or
        // both mtasks.
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
            VL_DO_DANGLING(delete mergeEdgep, mergeEdgep);
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
        partRedirectEdgesFrom(m_mtasksp, recipientp, donorp, &m_sb);

        ++m_mergesSinceRescore;

        // Do an expensive check, confirm we haven't botched the CP
        // updates.
        if (m_slowAsserts) partCheckCriticalPaths(m_mtasksp);

        // Finally, make new sibling pairs as needed:
        //  - prereqs and postreqs of recipientp
        //  - prereqs of recipientp's postreqs
        //  - postreqs of recipientp's prereqs
        // Note that this depends on the updated critical paths (above).
        siblingPairFromRelatives<GraphWay::REVERSE, true>(recipientp);
        siblingPairFromRelatives<GraphWay::FORWARD, true>(recipientp);
        unsigned edges = 0;
        for (V3GraphEdge* edgep = recipientp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            LogicMTask* const postreqp = static_cast<LogicMTask*>(edgep->top());
            siblingPairFromRelatives<GraphWay::REVERSE, false>(postreqp);
            ++edges;
            if (edges >= PART_SIBLING_EDGE_LIMIT) break;
        }
        edges = 0;
        for (V3GraphEdge* edgep = recipientp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            LogicMTask* const prereqp = static_cast<LogicMTask*>(edgep->fromp());
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
            for (const SiblingMC* smcp = ap->aSiblingMCs().begin();  // lintok-begin-on-ref
                 smcp; smcp = smcp->aNextp()) {
                UASSERT_OBJ(smcp->ap() == ap, ap, "Inconsistent SiblingMC");
                UASSERT_OBJ(m_sb.contains(smcp), ap, "Must be on the scoreboard");
                if (smcp->bp() == bp) found = true;
            }
            UASSERT_OBJ(found, ap, "Sibling not found");
        }
    }

    template <GraphWay::en T_Way, bool Exhaustive>
    void siblingPairFromRelatives(V3GraphVertex* mtaskp) {
        constexpr GraphWay way{T_Way};
        // Need at least 2 edges
        if (!mtaskp->beginp(way) || !mtaskp->beginp(way)->nextp(way)) return;

        std::array<LogicMTask*, PART_SIBLING_EDGE_LIMIT> neighbours;

        // This is a hot method, so we want so sort as efficiently as possible. We pre-load
        // all data (critical path cost and id) required for determining ordering into an aligned
        // structure. There is not enough space next to these to keep a whole pointer within 16
        // bytes, so we store an index into the neighbours buffer instead. We can then compare
        // and swap these sorting records very efficiently. With this the standard library sorting
        // functions are efficient enough and using more optimized methods (e.g.: sorting networks)
        // has no measurable benefit.
        struct alignas(16) SortingRecord {
            uint64_t m_id;
            uint32_t m_cp;
            uint8_t m_idx;
            static_assert(PART_SIBLING_EDGE_LIMIT <= std::numeric_limits<uint8_t>::max(),
                          "m_idx must fit all indices into 'neighbours'");
            bool operator<(const SortingRecord& that) const {
                return m_cp < that.m_cp || (m_cp == that.m_cp && m_id < that.m_id);
            }
        };
        static_assert(sizeof(SortingRecord) <= 16, "How could this be padded to more than 16?");

        std::array<SortingRecord, PART_SIBLING_EDGE_LIMIT> sortRecs;
        size_t n = 0;

        // Populate the buffers
        for (V3GraphEdge *edgep = mtaskp->beginp(way), *nextp; edgep; edgep = nextp) {
            nextp = edgep->nextp(way);  // Fetch next first as likely cache miss
            LogicMTask* const otherp = static_cast<LogicMTask*>(edgep->furtherp(way));
            neighbours[n] = otherp;
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
                makeSiblingMC(neighbours[sortRecs[i].m_idx], neighbours[sortRecs[i + 1].m_idx]);
            }
        } else {
            constexpr size_t end = 2 * MAX_NONEXHAUSTIVE_PAIRS;
            std::partial_sort(sortRecs.begin(), sortRecs.begin() + end, sortRecs.begin() + n);
            for (size_t i = 0; i < end; i += 2) {
                makeSiblingMC(neighbours[sortRecs[i].m_idx], neighbours[sortRecs[i + 1].m_idx]);
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
        // NOTE: To get a dot file run with --debugi-V3Partition 4 or more.
        const uint64_t startUsecs = V3Os::timeUsecs();
        V3Graph mtasks;
        LogicMTask* lastp = nullptr;
        for (unsigned i = 0; i < chain_len; ++i) {
            LogicMTask* const mtp = new LogicMTask(&mtasks, nullptr);
            mtp->setCost(1);
            if (lastp) new MTaskEdge(&mtasks, lastp, mtp, 1);
            lastp = mtp;
        }
        partInitCriticalPaths(&mtasks);

        // Since slowAsserts mode is *expected* to cause N^2 runtime, and the
        // intent of this test is to demonstrate better-than-N^2 runtime, disable
        // slowAsserts.
        PartContraction ec(&mtasks,
                           // Any CP limit >chain_len should work:
                           chain_len * 2, false /* slowAsserts */);
        ec.go();

        PartParallelismEst check(&mtasks);
        check.traverse();

        const uint64_t endUsecs = V3Os::timeUsecs();
        const uint64_t elapsedUsecs = endUsecs - startUsecs;

        if (debug() >= 6) {
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
        LogicMTask* const centerp = new LogicMTask(&mtasks, nullptr);
        centerp->setCost(1);
        unsigned i;
        for (i = 0; i < 50; ++i) {
            LogicMTask* const mtp = new LogicMTask(&mtasks, nullptr);
            mtp->setCost(1);
            // Edge from every input -> centerp
            new MTaskEdge(&mtasks, mtp, centerp, 1);
        }
        for (i = 0; i < 50; ++i) {
            LogicMTask* const mtp = new LogicMTask(&mtasks, nullptr);
            mtp->setCost(1);
            // Edge from centerp -> every output
            new MTaskEdge(&mtasks, centerp, mtp, 1);
        }

        partInitCriticalPaths(&mtasks);
        PartContraction(&mtasks, 20, true).go();

        PartParallelismEst check(&mtasks);
        check.traverse();

        // Checking exact values here is maybe overly precise.  What we're
        // mostly looking for is a healthy reduction in the number of
        // mtasks.
        if (debug() >= 5) {
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

//######################################################################
// DpiImportCallVisitor

// Scan node, indicate whether it contains a call to a DPI imported
// routine.
class DpiImportCallVisitor final : public VNVisitor {
private:
    bool m_hasDpiHazard = false;  // Found a DPI import call.
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    // METHODS
    VL_DEBUG_FUNC;

    virtual void visit(AstCFunc* nodep) override {
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
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        // Enter the function and trace it
        m_tracingCall = true;
        iterate(nodep->funcp());
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DpiImportCallVisitor(AstNode* nodep) { iterate(nodep); }
    bool hasDpiHazard() const { return m_hasDpiHazard; }
    virtual ~DpiImportCallVisitor() override = default;

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
class PartFixDataHazards final {
private:
    // TYPES
    using LogicMTaskSet = std::set<LogicMTask*, MTaskIdLessThan>;
    using TasksByRank = std::map<uint32_t /*rank*/, LogicMTaskSet>;
    using OvvSet = std::set<const OrderVarStdVertex*, OrderByPtrId&>;
    using Olv2MTaskMap = std::unordered_map<const OrderLogicVertex*, LogicMTask*>;

    // MEMBERS
    V3Graph* const m_mtasksp;  // Mtask graph
    Olv2MTaskMap m_olv2mtask;  // Map OrderLogicVertex to LogicMTask who wraps it
    unsigned m_mergesDone = 0;  // Number of MTasks merged. For stats only.
public:
    // CONSTRUCTORs
    explicit PartFixDataHazards(V3Graph* mtasksp)
        : m_mtasksp{mtasksp} {}
    // METHODS
private:
    void findAdjacentTasks(OvvSet::iterator ovvIt, TasksByRank* tasksByRankp) {
        // Find all writer tasks for this variable, group by rank.
        for (V3GraphEdge* edgep = (*ovvIt)->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const OrderLogicVertex* const logicp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            if (!logicp) continue;
            if (logicp->domainp()->hasInitial() || logicp->domainp()->hasSettle()) continue;
            LogicMTask* const writerMtaskp = m_olv2mtask.at(logicp);
            (*tasksByRankp)[writerMtaskp->rank()].insert(writerMtaskp);
        }
        // Find all reader tasks for this variable, group by rank.
        for (V3GraphEdge* edgep = (*ovvIt)->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const OrderLogicVertex* const logicp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
            if (!logicp) continue;
            if (logicp->domainp()->hasInitial() || logicp->domainp()->hasSettle()) continue;
            LogicMTask* const readerMtaskp = m_olv2mtask.at(logicp);
            (*tasksByRankp)[readerMtaskp->rank()].insert(readerMtaskp);
        }
    }
    void mergeSameRankTasks(TasksByRank* tasksByRankp) {
        LogicMTask* lastMergedp = nullptr;
        for (TasksByRank::iterator rankIt = tasksByRankp->begin(); rankIt != tasksByRankp->end();
             ++rankIt) {
            // Find the largest node at this rank, merge into it.  (If we
            // happen to find a huge node, this saves time in
            // partRedirectEdgesFrom() versus merging into an arbitrary node.)
            LogicMTask* mergedp = nullptr;
            for (LogicMTaskSet::iterator it = rankIt->second.begin(); it != rankIt->second.end();
                 ++it) {
                LogicMTask* const mtaskp = *it;
                if (mergedp) {
                    if (mergedp->cost() < mtaskp->cost()) mergedp = mtaskp;
                } else {
                    mergedp = mtaskp;
                }
            }
            rankIt->second.erase(mergedp);

            while (!rankIt->second.empty()) {
                const auto begin = rankIt->second.cbegin();
                LogicMTask* const donorp = *begin;
                UASSERT_OBJ(donorp != mergedp, donorp, "Donor can't be merged edge");
                rankIt->second.erase(begin);
                // Merge donorp into mergedp.
                // Fix up the map, so donor's OLVs map to mergedp
                for (LogicMTask::VxList::const_iterator tmvit = donorp->vertexListp()->begin();
                     tmvit != donorp->vertexListp()->end(); ++tmvit) {
                    const MTaskMoveVertex* const tmvp = *tmvit;
                    const OrderLogicVertex* const logicp = tmvp->logicp();
                    if (logicp) m_olv2mtask[logicp] = mergedp;
                }
                // Move all vertices from donorp to mergedp
                mergedp->moveAllVerticesFrom(donorp);
                // Redirect edges from donorp to recipientp, delete donorp
                partRedirectEdgesFrom(m_mtasksp, mergedp, donorp, nullptr);
                ++m_mergesDone;
            }

            if (lastMergedp) {
                UASSERT_OBJ(lastMergedp->rank() < mergedp->rank(), mergedp,
                            "Merging must be on lower rank");
                if (!lastMergedp->hasRelativeMTask(mergedp)) {
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
            AstNode* const nodep = (*it)->logicp()->nodep();
            // NOTE: We don't handle DPI exports. If testbench code calls a
            // DPI-exported function at any time during eval() we may have
            // a data hazard. (Likewise in non-threaded mode if an export
            // messes with an ordered variable we're broken.)

            // Find all calls to DPI-imported functions, we can put those
            // into a serial order at least. That should solve the most
            // likely DPI-related data hazards.
            if (DpiImportCallVisitor(nodep).hasDpiHazard()) {  //
                return true;
            }
        }
        return false;
    }

public:
    void go() {
        uint64_t startUsecs = 0;
        if (debug() >= 3) startUsecs = V3Os::timeUsecs();

        // Build an OLV->mtask map and a set of OVVs
        OrderByPtrId ovvOrder;
        OvvSet ovvSet(ovvOrder);
        // OVV's which wrap systemC vars will be handled slightly specially
        OvvSet ovvSetSystemC(ovvOrder);

        for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            LogicMTask* const mtaskp = static_cast<LogicMTask*>(vxp);
            // Should be only one MTaskMoveVertex in each mtask at this
            // stage, but whatever, write it as a loop:
            for (LogicMTask::VxList::const_iterator it = mtaskp->vertexListp()->begin();
                 it != mtaskp->vertexListp()->end(); ++it) {
                const MTaskMoveVertex* const tmvp = *it;
                if (const OrderLogicVertex* const logicp = tmvp->logicp()) {
                    m_olv2mtask[logicp] = mtaskp;
                    // Look at downstream vars.
                    for (V3GraphEdge* edgep = logicp->outBeginp(); edgep;
                         edgep = edgep->outNextp()) {
                        // Only consider OrderVarStdVertex which reflects
                        // an actual lvalue assignment; the others do not.
                        const OrderVarStdVertex* const ovvp
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
                for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
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
        for (OvvSet::iterator ovvit = ovvSet.begin(); ovvit != ovvSet.end(); ++ovvit) {
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
            for (OvvSet::iterator ovvit = ovvSetSystemC.begin(); ovvit != ovvSetSystemC.end();
                 ++ovvit) {
                findAdjacentTasks(ovvit, &tasksByRank);
            }
            mergeSameRankTasks(&tasksByRank);
        }

        // Handle nodes containing DPI calls, we want to serialize those
        // by default unless user gave --threads-dpi-concurrent.
        // Same basic strategy as above to serialize access to SC vars.
        if (!v3Global.opt.threadsDpiPure() || !v3Global.opt.threadsDpiUnpure()) {
            TasksByRank tasksByRank;
            for (V3GraphVertex* vxp = m_mtasksp->verticesBeginp(); vxp;
                 vxp = vxp->verticesNextp()) {
                LogicMTask* const mtaskp = static_cast<LogicMTask*>(vxp);
                if (hasDpiHazard(mtaskp)) tasksByRank[vxp->rank()].insert(mtaskp);
            }
            mergeSameRankTasks(&tasksByRank);
        }

        UINFO(4, "PartFixDataHazards() merged " << m_mergesDone << " pairs of nodes in "
                                                << (V3Os::timeUsecs() - startUsecs)
                                                << " usecs.\n");
    }

private:
    VL_UNCOPYABLE(PartFixDataHazards);
    VL_DEBUG_FUNC;
};

//######################################################################
// ThreadSchedule

class PartPackMTasks;

// The thread schedule, containing all information needed later. Note that this is a simple
// aggregate data type and the only way to get hold of an instance of it is via
// PartPackMTasks::pack, which is moved from there and is const, which means we can only acquire a
// const reference to is so no further modifications are allowed, so all members are public
// (attributes).
class ThreadSchedule final {
public:
    // CONSTANTS
    static constexpr uint32_t UNASSIGNED = 0xffffffff;

    // TYPES
    struct MTaskState {
        uint32_t completionTime = 0;  // Estimated time this mtask will complete
        uint32_t threadId = UNASSIGNED;  // Thread id this MTask is assigned to
        const ExecMTask* nextp = nullptr;  // Next MTask on same thread after this
    };

    // MEMBERS
    // Allocation of sequence of MTasks to threads. Can be considered a map from thread ID to
    // the sequence of MTasks to be executed by that thread.
    std::vector<std::vector<const ExecMTask*>> threads;

    // State for each mtask.
    std::unordered_map<const ExecMTask*, MTaskState> mtaskState;

    uint32_t threadId(const ExecMTask* mtaskp) const {
        const auto& it = mtaskState.find(mtaskp);
        if (it != mtaskState.end()) {
            return it->second.threadId;
        } else {
            return UNASSIGNED;
        }
    }

private:
    friend class PartPackMTasks;

    explicit ThreadSchedule(uint32_t nThreads)
        : threads{nThreads} {}
    VL_UNCOPYABLE(ThreadSchedule);  // But movable
    ThreadSchedule(ThreadSchedule&&) = default;
    ThreadSchedule& operator=(ThreadSchedule&&) = default;

    // Debugging
    void dumpDotFile(const V3Graph& graph, const string& filename) const;
    void dumpDotFilePrefixedAlways(const V3Graph& graph, const string& nameComment) const;

public:
    // Returns the number of cross-thread dependencies of the given MTask. If > 0, the MTask must
    // test whether its dependencies are ready before starting, and therefore may need to block.
    uint32_t crossThreadDependencies(const ExecMTask* mtaskp) const {
        const uint32_t thisThreadId = threadId(mtaskp);
        uint32_t result = 0;
        for (V3GraphEdge* edgep = mtaskp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const ExecMTask* const prevp = dynamic_cast<ExecMTask*>(edgep->fromp());
            if (threadId(prevp) != thisThreadId) ++result;
        }
        return result;
    }

    uint32_t startTime(const ExecMTask* mtaskp) const {
        return mtaskState.at(mtaskp).completionTime - mtaskp->cost();
    }
    uint32_t endTime(const ExecMTask* mtaskp) const {
        return mtaskState.at(mtaskp).completionTime;
    }
};

//! Variant of dumpDotFilePrefixed without --dump option check
void ThreadSchedule::dumpDotFilePrefixedAlways(const V3Graph& graph,
                                               const string& nameComment) const {
    dumpDotFile(graph, v3Global.debugFilename(nameComment) + ".dot");
}

void ThreadSchedule::dumpDotFile(const V3Graph& graph, const string& filename) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
    if (logp->fail()) v3fatal("Can't write " << filename);

    // Header
    *logp << "digraph v3graph {\n";
    *logp << "  graph[layout=\"neato\" labelloc=t labeljust=l label=\"" << filename << "\"]\n";
    *logp << "  node[shape=\"rect\" ratio=\"fill\" fixedsize=true]\n";

    // Thread labels
    *logp << "\n  // Threads\n";
    const int threadBoxWidth = 2;
    for (int i = 0; i < v3Global.opt.threads(); i++) {
        *logp << "  t" << i << " [label=\"Thread " << i << "\" width=" << threadBoxWidth
              << " pos=\"" << (-threadBoxWidth / 2) << "," << -i
              << "!\" style=\"filled\" fillcolor=\"grey\"] \n";
    }

    // MTask nodes
    *logp << "\n  // MTasks\n";

    // Find minimum cost MTask for scaling MTask node widths
    uint32_t minCost = UINT32_MAX;
    for (const V3GraphVertex* vxp = graph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        if (const ExecMTask* const mtaskp = dynamic_cast<const ExecMTask*>(vxp)) {
            minCost = minCost > mtaskp->cost() ? mtaskp->cost() : minCost;
        }
    }
    const double minWidth = 2.0;
    const auto mtaskXPos = [&](const ExecMTask* mtaskp, const double nodeWidth) {
        const double startPosX = (minWidth * startTime(mtaskp)) / minCost;
        return nodeWidth / minWidth + startPosX;
    };

    const auto emitMTask = [&](const ExecMTask* mtaskp) {
        const int thread = threadId(mtaskp);
        const double nodeWidth = minWidth * (static_cast<double>(mtaskp->cost()) / minCost);
        const double x = mtaskXPos(mtaskp, nodeWidth);
        const int y = -thread;
        const string label = "label=\"" + mtaskp->name() + " (" + cvtToStr(startTime(mtaskp)) + ":"
                             + std::to_string(endTime(mtaskp)) + ")" + "\"";
        *logp << "  " << mtaskp->name() << " [" << label << " width=" << nodeWidth << " pos=\""
              << x << "," << y << "!\"]\n";
    };

    // Emit MTasks
    for (const V3GraphVertex* vxp = graph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        if (const ExecMTask* const mtaskp = dynamic_cast<const ExecMTask*>(vxp)) emitMTask(mtaskp);
    }

    // Emit MTask dependency edges
    *logp << "\n  // MTask dependencies\n";
    for (const V3GraphVertex* vxp = graph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        if (const ExecMTask* const mtaskp = dynamic_cast<const ExecMTask*>(vxp)) {
            for (V3GraphEdge* edgep = mtaskp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                const V3GraphVertex* const top = edgep->top();
                *logp << "  " << vxp->name() << " -> " << top->name() << "\n";
            }
        }
    }

    // Trailer
    *logp << "}\n";
    logp->close();
}

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
class PartPackMTasks final {
    // TYPES
    struct MTaskCmp {
        bool operator()(const ExecMTask* ap, const ExecMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

    // MEMBERS
    const uint32_t m_nThreads;  // Number of threads
    const uint32_t m_sandbagNumerator;  // Numerator padding for est runtime
    const uint32_t m_sandbagDenom;  // Denominator padding for est runtime

public:
    // CONSTRUCTORS
    explicit PartPackMTasks(uint32_t nThreads = v3Global.opt.threads(),
                            unsigned sandbagNumerator = 30, unsigned sandbagDenom = 100)
        : m_nThreads{nThreads}
        , m_sandbagNumerator{sandbagNumerator}
        , m_sandbagDenom{sandbagDenom} {}
    ~PartPackMTasks() = default;

private:
    // METHODS
    uint32_t completionTime(const ThreadSchedule& schedule, const ExecMTask* mtaskp,
                            uint32_t threadId) {
        const ThreadSchedule::MTaskState& state = schedule.mtaskState.at(mtaskp);
        UASSERT(state.threadId != ThreadSchedule::UNASSIGNED, "Mtask should have assigned thread");
        if (threadId == state.threadId) {
            // No overhead on same thread
            return state.completionTime;
        }

        // Add some padding to the estimated runtime when looking from
        // another thread
        uint32_t sandbaggedEndTime
            = state.completionTime + (m_sandbagNumerator * mtaskp->cost()) / m_sandbagDenom;

        // If task B is packed after task A on thread 0, don't let thread 1
        // think that A finishes earlier than thread 0 thinks that B
        // finishes, otherwise we get priority inversions and fail the self
        // test.
        if (state.nextp) {
            const uint32_t successorEndTime
                = completionTime(schedule, state.nextp, state.threadId);
            if ((sandbaggedEndTime >= successorEndTime) && (successorEndTime > 1)) {
                sandbaggedEndTime = successorEndTime - 1;
            }
        }

        UINFO(6, "Sandbagged end time for " << mtaskp->name() << " on th " << threadId << " = "
                                            << sandbaggedEndTime << endl);
        return sandbaggedEndTime;
    }

    bool isReady(ThreadSchedule& schedule, const ExecMTask* mtaskp) {
        for (V3GraphEdge* edgeInp = mtaskp->inBeginp(); edgeInp; edgeInp = edgeInp->inNextp()) {
            const ExecMTask* const prevp = dynamic_cast<ExecMTask*>(edgeInp->fromp());
            if (schedule.threadId(prevp) == ThreadSchedule::UNASSIGNED) {
                // This predecessor is not assigned yet
                return false;
            }
        }
        return true;
    }

public:
    // Pack an MTasks from given graph into m_nThreads threads, return the schedule.
    const ThreadSchedule pack(const V3Graph& mtaskGraph) {
        // The result
        ThreadSchedule schedule(m_nThreads);

        // Time each thread is occupied until
        std::vector<uint32_t> busyUntil(m_nThreads, 0);

        // MTasks ready to be assigned next. All their dependencies are already assigned.
        std::set<ExecMTask*, MTaskCmp> readyMTasks;

        // Build initial ready list
        for (V3GraphVertex* vxp = mtaskGraph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            ExecMTask* const mtaskp = dynamic_cast<ExecMTask*>(vxp);
            if (isReady(schedule, mtaskp)) readyMTasks.insert(mtaskp);
        }

        while (!readyMTasks.empty()) {
            // For each task in the ready set, compute when it might start
            // on each thread (in that thread's local time frame.)
            uint32_t bestTime = 0xffffffff;
            uint32_t bestThreadId = 0;
            ExecMTask* bestMtaskp = nullptr;  // Todo: const ExecMTask*
            for (uint32_t threadId = 0; threadId < m_nThreads; ++threadId) {
                for (ExecMTask* const mtaskp : readyMTasks) {
                    uint32_t timeBegin = busyUntil[threadId];
                    if (timeBegin > bestTime) {
                        UINFO(6, "th " << threadId << " busy until " << timeBegin
                                       << ", later than bestTime " << bestTime
                                       << ", skipping thread.\n");
                        break;
                    }
                    for (V3GraphEdge* edgep = mtaskp->inBeginp(); edgep;
                         edgep = edgep->inNextp()) {
                        const ExecMTask* const priorp = dynamic_cast<ExecMTask*>(edgep->fromp());
                        const uint32_t priorEndTime = completionTime(schedule, priorp, threadId);
                        if (priorEndTime > timeBegin) timeBegin = priorEndTime;
                    }
                    UINFO(6, "Task " << mtaskp->name() << " start at " << timeBegin
                                     << " on thread " << threadId << endl);
                    if ((timeBegin < bestTime)
                        || ((timeBegin == bestTime)
                            && bestMtaskp  // Redundant, but appeases static analysis tools
                            && (mtaskp->priority() > bestMtaskp->priority()))) {
                        bestTime = timeBegin;
                        bestThreadId = threadId;
                        bestMtaskp = mtaskp;
                    }
                }
            }

            UASSERT(bestMtaskp, "Should have found some task");
            UINFO(6, "Will schedule " << bestMtaskp->name() << " onto thread " << bestThreadId
                                      << endl);

            // Reference to thread in schedule we are assigning this MTask to.
            std::vector<const ExecMTask*>& bestThread = schedule.threads[bestThreadId];

            // Update algorithm state
            bestMtaskp->predictStart(bestTime);  // Only for gantt reporting
            const uint32_t bestEndTime = bestTime + bestMtaskp->cost();
            schedule.mtaskState[bestMtaskp].completionTime = bestEndTime;
            schedule.mtaskState[bestMtaskp].threadId = bestThreadId;
            if (!bestThread.empty()) schedule.mtaskState[bestThread.back()].nextp = bestMtaskp;
            busyUntil[bestThreadId] = bestEndTime;

            // Add the MTask to the schedule
            bestThread.push_back(bestMtaskp);

            // Update the ready list
            const size_t erased = readyMTasks.erase(bestMtaskp);
            UASSERT_OBJ(erased > 0, bestMtaskp, "Should have erased something?");
            for (V3GraphEdge* edgeOutp = bestMtaskp->outBeginp(); edgeOutp;
                 edgeOutp = edgeOutp->outNextp()) {
                ExecMTask* const nextp = dynamic_cast<ExecMTask*>(edgeOutp->top());
                // Dependent MTask should not yet be assigned to a thread
                UASSERT(schedule.threadId(nextp) == ThreadSchedule::UNASSIGNED,
                        "Tasks after one being assigned should not be assigned yet");
                // Dependent MTask should not be ready yet, since dependency is just being assigned
                UASSERT_OBJ(readyMTasks.find(nextp) == readyMTasks.end(), nextp,
                            "Tasks after one being assigned should not be ready");
                if (isReady(schedule, nextp)) {
                    readyMTasks.insert(nextp);
                    UINFO(6, "Inserted " << nextp->name() << " into ready\n");
                }
            }
        }

        if (debug() >= 4) schedule.dumpDotFilePrefixedAlways(mtaskGraph, "schedule");

        return schedule;
    }

    // SELF TEST
    static void selfTest() {
        V3Graph graph;
        ExecMTask* const t0 = new ExecMTask(&graph, nullptr, 0);
        t0->cost(1000);
        t0->priority(1100);
        ExecMTask* const t1 = new ExecMTask(&graph, nullptr, 1);
        t1->cost(100);
        t1->priority(100);
        ExecMTask* const t2 = new ExecMTask(&graph, nullptr, 2);
        t2->cost(100);
        t2->priority(100);

        new V3GraphEdge(&graph, t0, t1, 1);
        new V3GraphEdge(&graph, t0, t2, 1);

        PartPackMTasks packer(2,  // Threads
                              3,  // Sandbag numerator
                              10);  // Sandbag denom
        const ThreadSchedule& schedule = packer.pack(graph);

        UASSERT_SELFTEST(size_t, schedule.threads.size(), 2);

        UASSERT_SELFTEST(size_t, schedule.threads[0].size(), 2);
        UASSERT_SELFTEST(size_t, schedule.threads[1].size(), 1);

        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[0][0], t0);
        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[0][1], t1);
        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[1][0], t2);

        UASSERT_SELFTEST(size_t, schedule.mtaskState.size(), 3);

        UASSERT_SELFTEST(uint32_t, schedule.threadId(t0), 0);
        UASSERT_SELFTEST(uint32_t, schedule.threadId(t1), 0);
        UASSERT_SELFTEST(uint32_t, schedule.threadId(t2), 1);

        // On its native thread, we see the actual end time for t0:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t0, 0), 1000);
        // On the other thread, we see a sandbagged end time which does not
        // exceed the t1 end time:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t0, 1), 1099);

        // Actual end time on native thread:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t1, 0), 1100);
        // Sandbagged end time seen on thread 1.  Note it does not compound
        // with t0's sandbagged time; compounding caused trouble in
        // practice.
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t1, 1), 1130);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t2, 0), 1229);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t2, 1), 1199);
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
    UINFO(4, " Stats for " << stage << endl);
    uint32_t mtaskCount = 0;
    uint32_t totalCost = 0;
    std::array<uint32_t, 32> mtaskCostHist;
    mtaskCostHist.fill(0);

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
        if (debug() >= 4) graphp->dumpDotFilePrefixedAlways(filePrefix);
    }

    // Look only at the cost of each mtask, neglect communication cost.
    // This will show us how much parallelism we expect, assuming cache-miss
    // costs are minor and the cost of running logic is the dominant cost.
    PartParallelismEst vertexParEst(graphp);
    vertexParEst.traverse();
    vertexParEst.statsReport(stage);
    if (debug() >= 4) {
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

    std::unordered_map<const V3GraphVertex*, uint32_t> vx2Id;
    unsigned id = 0;
    for (const V3GraphVertex* vxp = graphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        vx2Id[vxp] = id++;
    }
    unsigned hash = 0;
    for (const V3GraphVertex* vxp = graphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        for (const V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const V3GraphVertex* const top = edgep->top();
            hash = vx2Id[top] + 31U * hash;  // The K&R hash function
        }
    }
    UINFO(0, "Hash of shape (not contents) of " << debugName << " = " << cvtToStr(hash) << endl);
}

void V3Partition::setupMTaskDeps(V3Graph* mtasksp, const Vx2MTaskMap* vx2mtaskp) {
    // Look at each mtask
    for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
        LogicMTask* const mtaskp = static_cast<LogicMTask*>(itp);
        const LogicMTask::VxList* vertexListp = mtaskp->vertexListp();

        // For each logic vertex in this mtask, create an mtask-to-mtask
        // edge based on the logic-to-logic edge.
        for (LogicMTask::VxList::const_iterator vit = vertexListp->begin();
             vit != vertexListp->end(); ++vit) {
            for (V3GraphEdge* outp = (*vit)->outBeginp(); outp; outp = outp->outNextp()) {
                UASSERT(outp->weight() > 0, "Mtask not assigned weight");
                const MTaskMoveVertex* const top = dynamic_cast<MTaskMoveVertex*>(outp->top());
                UASSERT(top, "MoveVertex not associated to mtask");
                const auto it = vlstd::as_const(vx2mtaskp)->find(top);
                UASSERT(it != vx2mtaskp->end(), "MTask map can't find id");
                LogicMTask* const otherMTaskp = it->second;
                UASSERT(otherMTaskp, "nullptr other Mtask");
                UASSERT_OBJ(otherMTaskp != mtaskp, mtaskp, "Would create a cycle edge");

                // Don't create redundant edges.
                if (mtaskp->hasRelativeMTask(otherMTaskp)) continue;

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
        const VNUser5InUse inUser5;
        Vx2MTaskMap vx2mtask;
        for (V3GraphVertex* vxp = m_fineDepsGraphp->verticesBeginp(); vxp;
             vxp = vxp->verticesNextp()) {
            MTaskMoveVertex* const mtmvVxp = dynamic_cast<MTaskMoveVertex*>(vxp);
            UASSERT_OBJ(mtmvVxp, vxp, "Every vertex here should be an MTaskMoveVertex");

            LogicMTask* const mtaskp = new LogicMTask(mtasksp, mtmvVxp);
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

    const int targetParFactor = v3Global.opt.threads();
    if (targetParFactor < 2) v3fatalSrc("We should not reach V3Partition when --threads <= 1");

    // Set cpLimit to roughly totalGraphCost / nThreads
    //
    // Actually set it a bit lower, by a hardcoded fudge factor. This
    // results in more smaller mtasks, which helps reduce fragmentation
    // when scheduling them.
    const unsigned fudgeNumerator = 3;
    const unsigned fudgeDenominator = 5;
    const uint32_t cpLimit
        = ((totalGraphCost * fudgeNumerator) / (targetParFactor * fudgeDenominator));
    UINFO(4, "V3Partition set cpLimit = " << cpLimit << endl);

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
                        v3Global.opt.debugPartition())
            .go();
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
        using SortedMTaskSet = std::set<LogicMTask*, LogicMTask::CmpLogicMTask>;
        SortedMTaskSet sorted;
        for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
            LogicMTask* const mtaskp = static_cast<LogicMTask*>(itp);
            sorted.insert(mtaskp);
        }
        for (auto it = sorted.begin(); it != sorted.end(); ++it) {
            // We shouldn't perturb the sort order of the set, despite
            // changing the IDs, they should all just remain in the same
            // relative order. Confirm that:
            const uint32_t nextId = v3Global.rootp()->allocNextMTaskID();
            UASSERT(nextId <= (*it)->id(), "Should only shrink MTaskIDs here");
            UINFO(4, "Reassigning MTask id " << (*it)->id() << " to id " << nextId << "\n");
            (*it)->id(nextId);
        }
    }

    // Set color to indicate an mtaskId on every underlying MTaskMoveVertex.
    for (V3GraphVertex* itp = mtasksp->verticesBeginp(); itp; itp = itp->verticesNextp()) {
        const LogicMTask* const mtaskp = static_cast<LogicMTask*>(itp);
        for (LogicMTask::VxList::const_iterator it = mtaskp->vertexListp()->begin();
             it != mtaskp->vertexListp()->end(); ++it) {
            MTaskMoveVertex* const mvertexp = *it;
            mvertexp->color(mtaskp->id());
        }
    }
}

void add(std::unordered_map<int, uint64_t>& cmap, int id, uint64_t cost) { cmap[id] += cost; }

using EstimateAndProfiled = std::pair<uint64_t, uint64_t>;  // cost est, cost profiled
using Costs = std::unordered_map<uint32_t, EstimateAndProfiled>;

static void normalizeCosts(Costs& costs) {
    const auto scaleCost = [](uint64_t value, double multiplier) {
        double scaled = static_cast<double>(value) * multiplier;
        if (value && scaled < 1) scaled = 1;
        return static_cast<uint64_t>(scaled);
    };

    // For all costs with a profile, compute sum
    uint64_t sumCostProfiled = 0;  // For data with estimate and profile
    uint64_t sumCostEstimate = 0;  // For data with estimate and profile
    for (const auto& est : costs) {
        if (est.second.second) {
            sumCostEstimate += est.second.first;
            sumCostProfiled += est.second.second;
        }
    }

    if (sumCostEstimate) {
        // For data where we don't have profiled data, compute how much to
        // scale up/down the estimate to make on same relative scale as
        // profiled data.  (Improves results if only a few profiles missing.)
        const double estToProfile
            = static_cast<double>(sumCostProfiled) / static_cast<double>(sumCostEstimate);
        UINFO(5, "Estimated data needs scaling by "
                     << estToProfile << ", sumCostProfiled=" << sumCostProfiled
                     << " sumCostEstimate=" << sumCostEstimate << endl);
        for (auto& est : costs) {
            uint64_t& costEstimate = est.second.first;
            costEstimate = scaleCost(costEstimate, estToProfile);
        }
    }

    // COSTS can overflow a uint32.  Using maximum value of costs, scale all down
    uint64_t maxCost = 0;
    for (auto& est : costs) {
        const uint64_t& costEstimate = est.second.first;
        const uint64_t& costProfiled = est.second.second;
        if (maxCost < costEstimate) maxCost = costEstimate;
        if (maxCost < costProfiled) maxCost = costProfiled;
        UINFO(9,
              "Post uint scale: ce = " << est.second.first << " cp=" << est.second.second << endl);
    }
    const uint64_t scaleDownTo = 10000000;  // Extra room for future algorithms to add costs
    if (maxCost > scaleDownTo) {
        const double scaleup = static_cast<double>(scaleDownTo) / static_cast<double>(maxCost);
        UINFO(5, "Scaling data to within 32-bits by multiply by=" << scaleup << ", maxCost="
                                                                  << maxCost << endl);
        for (auto& est : costs) {
            est.second.first = scaleCost(est.second.first, scaleup);
            est.second.second = scaleCost(est.second.second, scaleup);
        }
    }
}

void V3Partition::selfTestNormalizeCosts() {
    {  // Test that omitted profile data correctly scales estimates
        Costs costs({// id  est  prof
                     {1, {10, 1000}},
                     {2, {20, 0}},  // Note no profile
                     {3, {30, 3000}}});
        normalizeCosts(costs);
        UASSERT_SELFTEST(uint64_t, costs[1].first, 1000);
        UASSERT_SELFTEST(uint64_t, costs[1].second, 1000);
        UASSERT_SELFTEST(uint64_t, costs[2].first, 2000);
        UASSERT_SELFTEST(uint64_t, costs[2].second, 0);
        UASSERT_SELFTEST(uint64_t, costs[3].first, 3000);
        UASSERT_SELFTEST(uint64_t, costs[3].second, 3000);
    }
    {  // Test that very large profile data properly scales
        Costs costs({// id  est  prof
                     {1, {10, 100000000000}},
                     {2, {20, 200000000000}},
                     {3, {30, 1}}});  // Make sure doesn't underflow
        normalizeCosts(costs);
        UASSERT_SELFTEST(uint64_t, costs[1].first, 2500000);
        UASSERT_SELFTEST(uint64_t, costs[1].second, 5000000);
        UASSERT_SELFTEST(uint64_t, costs[2].first, 5000000);
        UASSERT_SELFTEST(uint64_t, costs[2].second, 10000000);
        UASSERT_SELFTEST(uint64_t, costs[3].first, 7500000);
        UASSERT_SELFTEST(uint64_t, costs[3].second, 1);
    }
}

static void fillinCosts(V3Graph* execMTaskGraphp) {
    V3UniqueNames m_uniqueNames;  // For generating unique mtask profile hash names

    // Pass 1: See what profiling data applies
    Costs costs;  // For each mtask, costs

    for (const V3GraphVertex* vxp = execMTaskGraphp->verticesBeginp(); vxp;
         vxp = vxp->verticesNextp()) {
        ExecMTask* const mtp = dynamic_cast<ExecMTask*>(const_cast<V3GraphVertex*>(vxp));
        // Compute name of mtask, for hash lookup
        mtp->hashName(m_uniqueNames.get(mtp->bodyp()));

        // This estimate is 64 bits, but the final mtask graph algorithm needs 32 bits
        const uint64_t costEstimate = V3InstrCount::count(mtp->bodyp(), false);
        const uint64_t costProfiled
            = V3Config::getProfileData(v3Global.opt.prefix(), mtp->hashName());
        if (costProfiled) {
            UINFO(5, "Profile data for mtask " << mtp->id() << " " << mtp->hashName()
                                               << " cost override " << costProfiled << endl);
        }
        costs[mtp->id()] = std::make_pair(costEstimate, costProfiled);
    }

    normalizeCosts(costs /*ref*/);

    int totalEstimates = 0;
    int missingProfiles = 0;
    for (const V3GraphVertex* vxp = execMTaskGraphp->verticesBeginp(); vxp;
         vxp = vxp->verticesNextp()) {
        ExecMTask* const mtp = dynamic_cast<ExecMTask*>(const_cast<V3GraphVertex*>(vxp));
        const uint32_t costEstimate = costs[mtp->id()].first;
        const uint64_t costProfiled = costs[mtp->id()].second;
        UINFO(9, "ce = " << costEstimate << " cp=" << costProfiled << endl);
        UASSERT(costEstimate <= (1UL << 31), "cost scaling math would overflow uint32");
        UASSERT(costProfiled <= (1UL << 31), "cost scaling math would overflow uint32");
        const uint64_t costProfiled32 = static_cast<uint32_t>(costProfiled);
        uint32_t costToUse = costProfiled32;
        if (!costProfiled32) {
            costToUse = costEstimate;
            if (costEstimate != 0) ++missingProfiles;
        }
        if (costEstimate != 0) ++totalEstimates;
        mtp->cost(costToUse);
        mtp->priority(costToUse);
    }

    if (missingProfiles) {
        if (FileLine* const fl = V3Config::getProfileDataFileLine()) {
            fl->v3warn(PROFOUTOFDATE, "Profile data for mtasks may be out of date. "
                                          << missingProfiles << " of " << totalEstimates
                                          << " mtasks had no data");
        }
    }
}

static void finalizeCosts(V3Graph* execMTaskGraphp) {
    GraphStreamUnordered ser(execMTaskGraphp, GraphWay::REVERSE);
    while (const V3GraphVertex* const vxp = ser.nextp()) {
        ExecMTask* const mtp = dynamic_cast<ExecMTask*>(const_cast<V3GraphVertex*>(vxp));
        // "Priority" is the critical path from the start of the mtask, to
        // the end of the graph reachable from this mtask.  Given the
        // choice among several ready mtasks, we'll want to start the
        // highest priority one first, so we're always working on the "long
        // pole"
        for (V3GraphEdge* edgep = mtp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const ExecMTask* const followp = dynamic_cast<ExecMTask*>(edgep->top());
            if ((followp->priority() + mtp->cost()) > mtp->priority()) {
                mtp->priority(followp->priority() + mtp->cost());
            }
        }
    }

    // Some MTasks may now have zero cost, eliminate those.
    // (It's common for tasks to shrink to nothing when V3LifePost
    // removes dly assignments.)
    for (V3GraphVertex* vxp = execMTaskGraphp->verticesBeginp(); vxp;) {
        ExecMTask* const mtp = dynamic_cast<ExecMTask*>(vxp);
        vxp = vxp->verticesNextp();  // Advance before delete

        // Don't rely on checking mtp->cost() == 0 to detect an empty task.
        // Our cost-estimating logic is just an estimate. Instead, check
        // the MTaskBody to see if it's empty. That's the source of truth.
        AstMTaskBody* const bodyp = mtp->bodyp();
        if (!bodyp->stmtsp()) {  // Kill this empty mtask
            UINFO(6, "Removing zero-cost " << mtp->name() << endl);
            for (V3GraphEdge* inp = mtp->inBeginp(); inp; inp = inp->inNextp()) {
                for (V3GraphEdge* outp = mtp->outBeginp(); outp; outp = outp->outNextp()) {
                    new V3GraphEdge(execMTaskGraphp, inp->fromp(), outp->top(), 1);
                }
            }
            VL_DO_DANGLING(mtp->unlinkDelete(execMTaskGraphp), mtp);
            // Also remove and delete the AstMTaskBody, otherwise it would
            // keep a dangling pointer to the ExecMTask.
            VL_DO_DANGLING(bodyp->unlinkFrBack()->deleteTree(), bodyp);
        }
    }

    // Assign profiler IDs
    for (V3GraphVertex* vxp = execMTaskGraphp->verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
        static_cast<ExecMTask*>(vxp)->profilerId(v3Global.rootp()->allocNextMTaskProfilingID());
    }

    // Removing tasks may cause edges that were formerly non-transitive to
    // become transitive. Also we just created new edges around the removed
    // tasks, which could be transitive. Prune out all transitive edges.
    {
        execMTaskGraphp->removeTransitiveEdges();
        V3Partition::debugMTaskGraphStats(execMTaskGraphp, "transitive2");
    }

    // Record summary stats for final m_tasks graph.
    // (More verbose stats are available with --debugi-V3Partition >= 3.)
    PartParallelismEst parEst(execMTaskGraphp);
    parEst.traverse();
    parEst.statsReport("final");
    if (debug() >= 3) {
        UINFO(0, "  Final mtask parallelism report:\n");
        parEst.debugReport();
    }
}

static void addMTaskToFunction(const ThreadSchedule& schedule, const uint32_t threadId,
                               AstCFunc* funcp, const ExecMTask* mtaskp) {
    AstNodeModule* const modp = v3Global.rootp()->topModulep();
    FileLine* const fl = modp->fileline();

    // Helper function to make the code a bit more legible
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        funcp->addStmtsp(new AstCStmt(fl, stmt));
    };

    if (const uint32_t nDependencies = schedule.crossThreadDependencies(mtaskp)) {
        // This mtask has dependencies executed on another thread, so it may block. Create the task
        // state variable and wait to be notified.
        const string name = "__Vm_mtaskstate_" + cvtToStr(mtaskp->id());
        AstBasicDType* const mtaskStateDtypep
            = v3Global.rootp()->typeTablep()->findBasicDType(fl, VBasicDTypeKwd::MTASKSTATE);
        AstVar* const varp = new AstVar(fl, VVarType::MODULETEMP, name, mtaskStateDtypep);
        varp->valuep(new AstConst(fl, nDependencies));
        varp->protect(false);  // Do not protect as we still have references in AstText
        modp->addStmtp(varp);
        // For now, reference is still via text bashing
        addStrStmt("vlSelf->" + name + +".waitUntilUpstreamDone(even_cycle);\n");
    }

    if (v3Global.opt.profExec()) {
        const string& id = cvtToStr(mtaskp->id());
        const string& predictStart = cvtToStr(mtaskp->predictStart());
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskBegin(" + id + ", " + predictStart
                   + ");\n");
    }
    if (v3Global.opt.profPgo()) {
        // No lock around startCounter, as counter numbers are unique per thread
        addStrStmt("vlSymsp->_vm_pgoProfiler.startCounter(" + cvtToStr(mtaskp->profilerId())
                   + ");\n");
    }

    //
    addStrStmt("Verilated::mtaskId(" + cvtToStr(mtaskp->id()) + ");\n");

    // Move the actual body of calls to leaf functions into this function
    funcp->addStmtsp(mtaskp->bodyp()->unlinkFrBack());

    // Flush message queue
    addStrStmt("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");

    if (v3Global.opt.profPgo()) {
        // No lock around stopCounter, as counter numbers are unique per thread
        addStrStmt("vlSymsp->_vm_pgoProfiler.stopCounter(" + cvtToStr(mtaskp->profilerId())
                   + ");\n");
    }
    if (v3Global.opt.profExec()) {
        const string& id = cvtToStr(mtaskp->id());
        const string& predictConst = cvtToStr(mtaskp->cost());
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskEnd(" + id + ", " + predictConst
                   + ");\n");
    }

    // For any dependent mtask that's on another thread, signal one dependency completion.
    for (V3GraphEdge* edgep = mtaskp->outBeginp(); edgep; edgep = edgep->outNextp()) {
        const ExecMTask* const nextp = dynamic_cast<ExecMTask*>(edgep->top());
        if (schedule.threadId(nextp) != threadId) {
            addStrStmt("vlSelf->__Vm_mtaskstate_" + cvtToStr(nextp->id())
                       + ".signalUpstreamDone(even_cycle);\n");
        }
    }
}

static const std::vector<AstCFunc*> createThreadFunctions(const ThreadSchedule& schedule,
                                                          const string& tag) {
    AstNodeModule* const modp = v3Global.rootp()->topModulep();
    FileLine* const fl = modp->fileline();

    std::vector<AstCFunc*> funcps;

    // For each thread, create a function representing its entry point
    for (const std::vector<const ExecMTask*>& thread : schedule.threads) {
        if (thread.empty()) continue;
        const uint32_t threadId = schedule.threadId(thread.front());
        const string name{"__Vthread__" + tag + "__" + cvtToStr(threadId)};
        AstCFunc* const funcp = new AstCFunc(fl, name, nullptr, "void");
        modp->addStmtp(funcp);
        funcps.push_back(funcp);
        funcp->isStatic(true);  // Uses void self pointer, so static and hand rolled
        funcp->isLoose(true);
        funcp->entryPoint(true);
        funcp->argTypes("void* voidSelf, bool even_cycle");

        // Setup vlSelf an vlSyms
        funcp->addStmtsp(new AstCStmt{fl, EmitCBaseVisitor::voidSelfAssign(modp)});
        funcp->addStmtsp(new AstCStmt{fl, EmitCBaseVisitor::symClassAssign()});

        // Invoke each mtask scheduled to this thread from the thread function
        for (const ExecMTask* const mtaskp : thread) {
            addMTaskToFunction(schedule, threadId, funcp, mtaskp);
        }

        // Unblock the fake "final" mtask when this thread is finished
        funcp->addStmtsp(
            new AstCStmt(fl, "vlSelf->__Vm_mtaskstate_final.signalUpstreamDone(even_cycle);\n"));
    }

    // Create the fake "final" mtask state variable
    AstBasicDType* const mtaskStateDtypep
        = v3Global.rootp()->typeTablep()->findBasicDType(fl, VBasicDTypeKwd::MTASKSTATE);
    AstVar* const varp
        = new AstVar(fl, VVarType::MODULETEMP, "__Vm_mtaskstate_final", mtaskStateDtypep);
    varp->valuep(new AstConst(fl, funcps.size()));
    varp->protect(false);  // Do not protect as we still have references in AstText
    modp->addStmtp(varp);

    return funcps;
}

static void addThreadStartToExecGraph(AstExecGraph* const execGraphp,
                                      const std::vector<AstCFunc*>& funcps) {
    // FileLine used for constructing nodes below
    FileLine* const fl = v3Global.rootp()->fileline();

    // Add thread function invocations to execGraph
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        execGraphp->addStmtsp(new AstCStmt(fl, stmt));
    };
    const auto addTextStmt = [=](const string& text) -> void {
        execGraphp->addStmtsp(new AstText(fl, text, /* tracking: */ true));
    };

    addStrStmt("vlSymsp->__Vm_even_cycle = !vlSymsp->__Vm_even_cycle;\n");

    const uint32_t last = funcps.size() - 1;
    for (uint32_t i = 0; i <= last; ++i) {
        AstCFunc* const funcp = funcps.at(i);
        if (i != last) {
            // The first N-1 will run on the thread pool.
            addTextStmt("vlSymsp->__Vm_threadPoolp->workerp(" + cvtToStr(i) + ")->addTask(");
            execGraphp->addStmtsp(new AstAddrOfCFunc(fl, funcp));
            addTextStmt(", vlSelf, vlSymsp->__Vm_even_cycle);\n");
        } else {
            // The last will run on the main thread.
            AstCCall* const callp = new AstCCall(fl, funcp);
            callp->argTypes("vlSelf, vlSymsp->__Vm_even_cycle");
            execGraphp->addStmtsp(callp);
            addStrStmt("Verilated::mtaskId(0);\n");
        }
    }

    addStrStmt("vlSelf->__Vm_mtaskstate_final.waitUntilUpstreamDone(vlSymsp->__Vm_even_cycle);\n");
}

static void implementExecGraph(AstExecGraph* const execGraphp) {
    // Nothing to be done if there are no MTasks in the graph at all.
    if (execGraphp->depGraphp()->empty()) return;

    // Schedule the mtasks: statically associate each mtask with a thread,
    // and determine the order in which each thread will runs its mtasks.
    const ThreadSchedule& schedule = PartPackMTasks().pack(*execGraphp->depGraphp());

    // Create a function to be run by each thread. Note this moves all AstMTaskBody nodes form the
    // AstExecGrap into the AstCFunc created
    const std::vector<AstCFunc*>& funcps = createThreadFunctions(schedule, execGraphp->name());
    UASSERT(!funcps.empty(), "Non-empty ExecGraph yields no threads?");

    // Start the thread functions at the point this AstExecGraph is located in the tree.
    addThreadStartToExecGraph(execGraphp, funcps);
}

void V3Partition::finalize(AstNetlist* netlistp) {
    // Called by Verilator top stage
    netlistp->topModulep()->foreach<AstExecGraph>([&](AstExecGraph* execGraphp) {
        // Back in V3Order, we partitioned mtasks using provisional cost
        // estimates. However, V3Order precedes some optimizations (notably
        // V3LifePost) that can change the cost of logic within each mtask.
        // Now that logic is final, recompute the cost and priority of each
        // ExecMTask.
        fillinCosts(execGraphp->depGraphp());
        finalizeCosts(execGraphp->depGraphp());

        // Replace the graph body with its multi-threaded implementation.
        implementExecGraph(execGraphp);
    });
}

void V3Partition::selfTest() {
    PartPropagateCpSelfTest::selfTest();
    PartPackMTasks::selfTest();
    PartContraction::selfTest();
}
