// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Multi-threaded MTask graph contraction (coarsening)
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
//  Coarsens the fine-grained MTask graph produced by the partitioner by
//  repeatedly contracting MTasks (merging along an edge, or merging two
//  "sibling" MTasks) until a critical-path score limit is reached. Driven by
//  the partitioner in V3OrderParallel.cpp via OrderMTaskGraph::contract,
//  declared in V3OrderMTaskGraph.h.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Global.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3OrderMTaskGraph.h"
#include "V3PairingHeap.h"

#include <algorithm>
#include <array>
#include <limits>
#include <memory>
#include <type_traits>
#include <unordered_set>
#include <utility>

VL_DEFINE_DEBUG_FUNCTIONS;

class MergeCandidate;
class SiblingMC;
class EdgeMC;

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

// Don't produce more than a certain maximum number of MTasks.  This helps
// the TSP variable sort not to blow up (a concern for some of the tests)
// and we probably don't want a huge number of MTasks in practice anyway
// (50 to 100 is typical.)
//
// If the user doesn't give one with '--threads-max-mtasks', we'll set the
// maximum # of MTasks to
//  (# of threads * PART_DEFAULT_MAX_MTASKS_PER_THREAD)
constexpr unsigned PART_DEFAULT_MAX_MTASKS_PER_THREAD = 50;

//   end tunables.

//######################################################################
// MTask utility classes

struct MergeCandidateKey final {
    // Note: Structure layout chosen to minimize padding in PairingHeap<*>::Node
    uint64_t m_id;  // Unique ID part of edge score
    uint64_t m_score;  // Score part of ID
    bool operator<(const MergeCandidateKey& other) const {
        // First by Score then by ID, but notice that we want minimums using a max-heap, so reverse
        return m_score > other.m_score || (m_score == other.m_score && m_id > other.m_id);
    }
};

// For efficiency, MergeCandidateScoreboard elements must derive from
// PairingHeap<MergeCandidateKey>::Node
using MergeCandidateHeapNode = PairingHeap<MergeCandidateKey>::Node;

// Information associated with scoreboarding a merge candidate
class MergeCandidate VL_NOT_FINAL : public MergeCandidateHeapNode {
    // Only the known subclasses can create or delete one of these
    friend class SiblingMC;
    friend class EdgeMC;

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
        static uint64_t s_serial = 0;
        s_serial += ID_INCREMENT;  // +ID_INCREMENT so doesn't set the special bottom bits
        m_key.m_id = s_serial | (isSiblingMC * IS_SIBLING_MASK);
    }
    ~MergeCandidate() = default;

public:
    // METHODS
    SiblingMC* toSiblingMC();  // Instead of cast<>/as<>
    EdgeMC* toEdgeMC();  // Instead of cast<>/as<>
    bool mergeWouldCreateCycle() const;  // Instead of virtual method

    inline void rescore();
    uint64_t score() const { return m_key.m_score; }

    static MergeCandidate* heapNodeToElem(MergeCandidateHeapNode* nodep) {
        return static_cast<MergeCandidate*>(nodep);
    }
};

static_assert(sizeof(MergeCandidate) == sizeof(MergeCandidateHeapNode),
              "Should not have a vtable");

// A pair of associated LogicMTask's that are merge candidates for sibling
// contraction
class SiblingMC final : public MergeCandidate {
    LogicMTask* const m_ap;  // The higher ID MTask
    LogicMTask* const m_bp;  // The lower ID MTask

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

// A merge candidate associated with an MTaskEdge (edge contraction candidate)
class EdgeMC final : public MergeCandidate {
    MTaskEdge* const m_edgep;  // The associated edge

public:
    // CONSTRUCTORS
    explicit EdgeMC(MTaskEdge* edgep)
        : MergeCandidate{/* isSiblingMC: */ false}
        , m_edgep{edgep} {}
    ~EdgeMC() = default;

    // METHODS
    MTaskEdge* edgep() const { return m_edgep; }
    bool mergeWouldCreateCycle() const;
};

static_assert(!std::is_polymorphic<EdgeMC>::value, "Should not have a vtable");

// Auxiliary data associated with each LogicMTask during Contraction, attached via
// LogicMTask::userp(). Kept out of LogicMTask itself so that LogicMTask does not depend on the
// MergeCandidate hierarchy (which the SiblingMC lists reference).
struct MTaskContractionData final {
    // MTasks for which a SiblingMC exists with the owning MTask as the higher ID MTask (m_ap)
    std::unordered_set<LogicMTask*> siblings;
    // SiblingMCs for which the owning MTask is the higher ID MTask (m_ap in SiblingMC)
    SiblingMC::AList aSiblingMCs;
    // SiblingMCs for which the owning MTask is the lower ID MTask (m_bp in SiblingMC)
    SiblingMC::BList bSiblingMCs;
};

// The MTaskContractionData attached to 'mtaskp' (see LogicMTask::userp)
static MTaskContractionData& mtaskData(const LogicMTask* mtaskp) {
    return *static_cast<MTaskContractionData*>(mtaskp->userp());
}

// The EdgeMC associated with 'edgep' while it is on the scoreboard, or nullptr otherwise. Held in
// the edge's user pointer (see MTaskEdge), kept here so MTaskEdge does not depend on EdgeMC.
static EdgeMC* edgeMC(const MTaskEdge* edgep) { return static_cast<EdgeMC*>(edgep->userp()); }

// Instead of dynamic cast
SiblingMC* MergeCandidate::toSiblingMC() {
    return isSiblingMC() ? static_cast<SiblingMC*>(this) : nullptr;
}

EdgeMC* MergeCandidate::toEdgeMC() { return isSiblingMC() ? nullptr : static_cast<EdgeMC*>(this); }

// Normally this would be a virtual function, but we save space by not having a vtable,
// and we know we only have 2 possible subclasses.
bool MergeCandidate::mergeWouldCreateCycle() const {
    return isSiblingMC() ? static_cast<const SiblingMC*>(this)->mergeWouldCreateCycle()
                         : static_cast<const EdgeMC*>(this)->mergeWouldCreateCycle();
}

static uint64_t siblingScore(const SiblingMC* sibsp) {
    const LogicMTask* const ap = sibsp->ap();
    const LogicMTask* const bp = sibsp->bp();
    const uint64_t mergedCpCostFwd
        = std::max(ap->critPathCost(GraphWay::FORWARD), bp->critPathCost(GraphWay::FORWARD));
    const uint64_t mergedCpCostRev
        = std::max(ap->critPathCost(GraphWay::REVERSE), bp->critPathCost(GraphWay::REVERSE));
    return mergedCpCostRev + mergedCpCostFwd + ap->cost() + bp->cost();
}

static uint64_t edgeScore(const MTaskEdge* edgep) {
    // Score this edge. Lower is better. The score is the new local CP
    // length if we merge these MTasks.  ("Local" means the longest
    // critical path running through the merged node.)
    const LogicMTask* const top = edgep->toMTaskp();
    const LogicMTask* const fromp = edgep->fromMTaskp();
    const uint64_t mergedCpCostFwd = std::max(fromp->critPathCost(GraphWay::FORWARD),
                                              top->critPathCostWithout<GraphWay::FORWARD>(edgep));
    const uint64_t mergedCpCostRev = std::max(fromp->critPathCostWithout<GraphWay::REVERSE>(edgep),
                                              top->critPathCost(GraphWay::REVERSE));
    return mergedCpCostRev + mergedCpCostFwd + fromp->cost() + top->cost();
}

void MergeCandidate::rescore() {
    if (const SiblingMC* const sibp = toSiblingMC()) {
        m_key.m_score = siblingScore(sibp);
    } else {
        // Give a slight preference to sibling merges by increasing the cost of edge merges.
        // This biases towards sibling merges in case they are equal score with edge merges.
        // This avoid a central node growing while many leaves remain due to edge merges.
        m_key.m_score = 1 + edgeScore(static_cast<const EdgeMC*>(this)->edgep());
    }
}

SiblingMC::SiblingMC(LogicMTask* ap, LogicMTask* bp)
    : MergeCandidate{/* isSiblingMC: */ true}
    , m_ap{ap}
    , m_bp{bp} {
    // Storage management depends on this
    UASSERT(ap->id() > bp->id(), "Should be ordered");
    UDEBUGONLY(UASSERT(mtaskData(ap).siblings.count(bp), "Should be in sibling map"););
    mtaskData(m_ap).aSiblingMCs.linkBack(this);
    mtaskData(m_bp).bSiblingMCs.linkBack(this);
}

void SiblingMC::unlinkA() {
    VL_ATTR_UNUSED const size_t removed = mtaskData(m_ap).siblings.erase(m_bp);
    UDEBUGONLY(UASSERT(removed == 1, "Should have been in sibling set"););
    mtaskData(m_ap).aSiblingMCs.unlink(this);
}

void SiblingMC::unlinkB() { mtaskData(m_bp).bSiblingMCs.unlink(this); }

// cppcheck-suppress duplInheritedMember
bool SiblingMC::mergeWouldCreateCycle() const {
    return (LogicMTask::pathExistsFrom(m_ap, m_bp, nullptr)
            || LogicMTask::pathExistsFrom(m_bp, m_ap, nullptr));
}

// cppcheck-suppress duplInheritedMember
bool EdgeMC::mergeWouldCreateCycle() const {
    return LogicMTask::pathExistsFrom(m_edgep->fromMTaskp(), m_edgep->toMTaskp(), m_edgep);
}

// Scoreboard of MTask merge candidates. Owns the lifetime of the merge candidate objects: callers
// add/remove candidates via the methods below and never allocate or free them directly. For edges
// this maintains the invariant that an MTaskEdge has an associated EdgeMC (held in its userp()),
// if and only if it is currently on the scoreboard.
//
// This is essentially a heap that can be hinted that some elements have changed keys, at which
// point those elements are deferred as 'unknown' until the next 'rescore' call. We use the
// generic PairingHeap, relying on its internal structure. For efficiency, the merge candidates are
// themselves the heap nodes (MergeCandidate derives from PairingHeap<MergeCandidateKey>::Node), so
// a candidate can be on at most one scoreboard.
class MergeCandidateScoreboard final {
    // TYPES
    using Heap = PairingHeap<MergeCandidateKey>;
    using Node = Heap::Node;
    using Link = Heap::Link;

    // MEMBERS
    Heap m_known;  // The heap of candidates with known scores
    Link m_unknown;  // List of candidates with unknown scores

    // METHODS
    void addUnknown(MergeCandidate* nodep) {
        // Just prepend it to the list of unknown entries
        nodep->m_next.link(m_unknown.unlink());
        m_unknown.linkNonNull(nodep);
        // We mark nodes on the unknown list by making their child pointer point to themselves
        nodep->m_kids.m_ptr = nodep;
    }

    // Add a freshly created candidate. Not returned by 'best' before the next 'rescore' call.
    void add(MergeCandidate* nodep) { addUnknown(nodep); }

    // Remove a candidate from the scoreboard.
    void remove(MergeCandidate* nodep) {
        if (nodep->m_kids.m_ptr == nodep) {
            // Node is on the unknown list, replace with next
            nodep->replaceWith(nodep->m_next.unlink());
            return;
        }
        // Node is in the known heap, remove it
        m_known.remove(nodep);
    }

public:
    // CONSTRUCTORS
    MergeCandidateScoreboard() = default;
    ~MergeCandidateScoreboard() = default;
    VL_UNCOPYABLE(MergeCandidateScoreboard);

    // The candidate with the best (lowest) known score, or nullptr if none have a known score.
    // This does not automatically 'rescore'; the caller must 'rescore' to reflect all candidates.
    MergeCandidate* best() const { return MergeCandidate::heapNodeToElem(m_known.max()); }

    // Tell the scoreboard a candidate's score may have changed. Its score becomes 'unknown' and it
    // will not be returned by 'best' until the next 'rescore'.
    void hintScoreChanged(MergeCandidate* nodep) {
        // If it's already in the unknown list, then nothing to do
        if (nodep->m_kids.m_ptr == nodep) return;
        // Otherwise it was in the heap, remove it
        m_known.remove(nodep);
        // Prepend it to the unknown list
        addUnknown(nodep);
    }

    // True if there are candidates with an unknown score
    bool needsRescore() const { return m_unknown; }
    // True if the given candidate's score is unknown
    static bool needsRescore(const MergeCandidate* nodep) { return nodep->m_kids.m_ptr == nodep; }

    // For each candidate whose score is unknown, recompute the score and add to the known heap
    void rescore() {
        for (Node *nodep = m_unknown.unlink(), *nextp; nodep; nodep = nextp) {
            // Pick up next
            nextp = nodep->m_next.ptr();
            // Reset pointers
            nodep->m_next.m_ptr = nullptr;
            nodep->m_kids.m_ptr = nullptr;
            nodep->m_ownerpp = nullptr;
            // Re-compute the score of the candidate
            MergeCandidate::heapNodeToElem(nodep)->rescore();
            // Re-insert into the heap
            m_known.insert(nodep);
        }
    }

    // Create the merge candidate for 'edgep' and add it to the scoreboard (out-of-line below)
    void addEdge(MTaskEdge* edgep) {
        UDEBUGONLY(UASSERT(!edgep->userp(), "Edge already has a merge candidate"););
        EdgeMC* const edgeMCp = new EdgeMC{edgep};
        edgep->userp(edgeMCp);
        add(edgeMCp);
    }
    // Remove 'edgep's merge candidate from the scoreboard and delete it (out-of-line below)
    void removeEdge(MTaskEdge* edgep) {
        EdgeMC* const edgeMCp = edgeMC(edgep);
        UDEBUGONLY(UASSERT(edgeMCp, "Edge has no merge candidate"););
        edgep->userp(nullptr);
        remove(edgeMCp);
        VL_DO_DANGLING(delete edgeMCp, edgeMCp);
    }

    // Create a sibling merge candidate for 'ap' and 'bp' and add it to the scoreboard
    void addSibling(LogicMTask* ap, LogicMTask* bp) { add(new SiblingMC{ap, bp}); }
    // Remove sibling merge candidate 'smcp' from the scoreboard and delete it
    void removeSibling(SiblingMC* smcp) {
        remove(smcp);
        smcp->unlinkA();
        smcp->unlinkB();
        VL_DO_DANGLING(delete smcp, smcp);
    }
};

//######################################################################

// Look at vertex costs (in one way) to form critical paths for each
// vertex.
template <GraphWay::en N_Way>
static void partInitHalfCriticalPaths(V3Graph& mTaskGraph, bool checkOnly) {
    constexpr GraphWay way{N_Way};
    constexpr GraphWay rev = way.invert();
    GraphStreamUnordered order{&mTaskGraph, way};
    for (const V3GraphVertex* vertexp; (vertexp = order.nextp());) {
        const LogicMTask* const mtaskcp = static_cast<const LogicMTask*>(vertexp);
        LogicMTask* const mtaskp = const_cast<LogicMTask*>(mtaskcp);
        uint64_t cpCost = 0;
#if VL_DEBUG
        std::unordered_set<V3GraphVertex*> relatives;
#endif
        for (const V3GraphEdge& edge : vertexp->edges<rev>()) {
#if VL_DEBUG
            // Run a few asserts on the initial mtask graph,
            // while we're iterating through...
            UASSERT_OBJ(edge.weight() != 0, mtaskp, "Should be no cut edges in MTask graph");
            UASSERT_OBJ(relatives.find(edge.furtherp<rev>()) == relatives.end(), mtaskp,
                        "Should be no redundant edges in MTask graph");
            relatives.insert(edge.furtherp<rev>());
#endif
            const LogicMTask* const relativep = static_cast<LogicMTask*>(edge.furtherp<rev>());
            cpCost = std::max(cpCost, (relativep->critPathCost(way) + relativep->cost()));
        }
        if (checkOnly) {
            UASSERT(mtaskp->critPathCost(way) == cpCost, "Calculation error in scoring");
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

//######################################################################
// Contraction

// Perform edge or sibling contraction on the partition graph
class Contraction final {
    // TYPES
    // New CP information for mtaskp reflecting an upcoming merge
    struct NewCp final {
        uint64_t cp;
        uint64_t propagateCp;
        bool propagate;
    };

    // MEMBERS
    OrderMTaskGraph& m_mTaskGraph;  // The Mtask graph
    uint64_t m_scoreLimit;  // Sloppy score allowed when picking merges
    // Next score rescore at
    uint64_t m_scoreLimitBeforeRescore = std::numeric_limits<uint64_t>::max();
    unsigned m_mergesSinceRescore = 0;  // Merges since last rescore
    const bool m_slowAsserts{v3Global.opt.debugPartition()};  // Take extra time to validate steps
    MergeCandidateScoreboard m_sb;  // Scoreboard
    // Auxiliary per-MTask data (the SiblingMC lists) attached to each MTask via its user pointer.
    // Owned here for the lifetime of this Contraction. A single array, as the number of MTasks is
    // fixed for that lifetime: merging only ever deletes vertices, never creates them.
    std::unique_ptr<MTaskContractionData[]> m_mtaskDatap;

    // Singular source vertex of the OrderMTaskGraph
    LogicMTask* const m_entryMTaskp = m_mTaskGraph.entryp();
    // Singular sink vertex of the dependency graph
    LogicMTask* const m_exitMTaskp = m_mTaskGraph.exitp();

    // Merge edges from a LogicMtask, keeping the merge candidate scoreboard in sync.
    static void partRedirectEdgesFrom(V3Graph& graph, LogicMTask* recipientp, LogicMTask* donorp,
                                      MergeCandidateScoreboard& sb) {
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
                // The donor edge is going away, so remove it from the scoreboard
                if (edgep->userp()) sb.removeEdge(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep<GraphWay::FORWARD>(relativep));
                UDEBUGONLY(UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge"););
                // The existing edge is no longer transitive, so may need a rescore
                if (EdgeMC* const existEdgeMCp = edgeMC(existMTaskEdgep)) {
                    sb.hintScoreChanged(existEdgeMCp);
                }
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            } else {
                // No existing edge between recipient and relative of donor.
                // Redirect the edge from donor<->relative to recipient<->relative.
                edgep->relinkFromp(recipientp);
                recipientp->addRelativeMTask(relativep);
                recipientp->stealRelativeEdge<GraphWay::FORWARD>(edgep);
                relativep->addRelativeEdge<GraphWay::REVERSE>(edgep);
                // The redirected edge is a merge candidate again
                if (EdgeMC* const edgeMCp = edgeMC(edgep)) {
                    sb.hintScoreChanged(edgeMCp);
                } else {
                    sb.addEdge(edgep);
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
                // The donor edge is going away, so remove it from the scoreboard
                if (edgep->userp()) sb.removeEdge(edgep);
                MTaskEdge* const existMTaskEdgep = static_cast<MTaskEdge*>(
                    recipientp->findConnectingEdgep<GraphWay::REVERSE>(relativep));
                UDEBUGONLY(UASSERT(existMTaskEdgep, "findConnectingEdge didn't find edge"););
                // The existing edge is no longer transitive, so may need a rescore
                if (EdgeMC* const existEdgeMCp = edgeMC(existMTaskEdgep)) {
                    sb.hintScoreChanged(existEdgeMCp);
                }
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
            } else {
                // No existing edge between recipient and relative of donor.
                // Redirect the edge from donor<->relative to recipient<->relative.
                edgep->relinkTop(recipientp);
                relativep->addRelativeMTask(recipientp);
                relativep->addRelativeEdge<GraphWay::FORWARD>(edgep);
                recipientp->stealRelativeEdge<GraphWay::REVERSE>(edgep);
                // The redirected edge is a merge candidate again
                if (EdgeMC* const edgeMCp = edgeMC(edgep)) {
                    sb.hintScoreChanged(edgeMCp);
                } else {
                    sb.addEdge(edgep);
                }
            }
        }

        // Remove donorp from the graph
        VL_DO_DANGLING(donorp->unlinkDelete(&graph), donorp);
    }

    template <GraphWay::en N_Way>
    NewCp newCp(const LogicMTask* mtaskp, const LogicMTask* otherp, const MTaskEdge* mergeEdgep) {
        constexpr GraphWay way{N_Way};
        // Return new wayward-CP for mtaskp reflecting its upcoming merge
        // with otherp. Set 'result.propagate' if mtaskp's wayward
        // relatives will see a new wayward CP from this merge.
        uint64_t newCp;
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

        const uint64_t oldRelativesCp = mtaskp->critPathCost(way) + mtaskp->cost();
        const uint64_t newRelativesCp = newCp + mtaskp->cost() + otherp->cost();

        NewCp result;
        result.cp = newCp;
        result.propagate = (newRelativesCp > oldRelativesCp);
        result.propagateCp = newRelativesCp;
        return result;
    }

    void removeSiblingMCsWith(LogicMTask* mtaskp) {
        // Note: 'removeSibling' unlinks the candidate from both of its MTasks' lists, so taking
        // the front element repeatedly does terminate. It also erases the candidate from the
        // owning (higher id) MTask's sibling set as it goes, so both the sets and the lists are
        // left consistent, whichever side of the candidate 'mtaskp' happens to be on.
        while (SiblingMC* const smcp = mtaskData(mtaskp).aSiblingMCs.frontp()) {
            m_sb.removeSibling(smcp);
        }
        while (SiblingMC* const smcp = mtaskData(mtaskp).bSiblingMCs.frontp()) {
            m_sb.removeSibling(smcp);
        }
    }

    void removeSiblingMCs(LogicMTask* recipientp, LogicMTask* donorp) {
        // These two can share a SiblingMC (an edge between them does not preclude one). That is
        // fine: 'removeSiblingMCsWith' unlinks each candidate from both sides, so the shared one
        // is gone by the time we get to the donor.
        //
        // This also leaves both sibling sets empty, so they need no separate clearing: each entry
        // in an MTask's sibling set is added by 'makeSiblingMC' together with a SiblingMC on that
        // same MTask's 'aSiblingMCs' list, and draining that list erases the matching entry (see
        // 'SiblingMC::unlinkA'). The slow assert in 'makeSiblingMC' catches it if that ever
        // diverges, as a stale set entry there suppresses creating the SiblingMC it stands for.
        removeSiblingMCsWith(recipientp);
        removeSiblingMCsWith(donorp);
    }

    void contract(MergeCandidate* mergeCanp) {
        LogicMTask* top = nullptr;
        LogicMTask* fromp = nullptr;
        EdgeMC* const mergeEdgeMCp = mergeCanp->toEdgeMC();
        MTaskEdge* const mergeEdgep = mergeEdgeMCp ? mergeEdgeMCp->edgep() : nullptr;
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
        // Doing this before merging the MTasks lets us often avoid
        // recursing through either incoming or outgoing edges on one or
        // both MTasks.
        //
        // These 'NewCp' objects carry a bit indicating whether we must
        // propagate CP for each of the four cases:
        const NewCp recipientNewCpFwd = newCp<GraphWay::FORWARD>(recipientp, donorp, mergeEdgep);
        const NewCp donorNewCpFwd = newCp<GraphWay::FORWARD>(donorp, recipientp, mergeEdgep);
        const NewCp recipientNewCpRev = newCp<GraphWay::REVERSE>(recipientp, donorp, mergeEdgep);
        const NewCp donorNewCpRev = newCp<GraphWay::REVERSE>(donorp, recipientp, mergeEdgep);

        if (mergeEdgep) {
            // Remove and free the connecting edge. Must do this before propagating CP's below.
            m_sb.removeEdge(mergeEdgep);
            mergeEdgep->fromMTaskp()->removeRelativeMTask(mergeEdgep->toMTaskp());
            mergeEdgep->fromMTaskp()->removeRelativeEdge<GraphWay::FORWARD>(mergeEdgep);
            mergeEdgep->toMTaskp()->removeRelativeEdge<GraphWay::REVERSE>(mergeEdgep);
            VL_DO_DANGLING(mergeEdgep->unlinkDelete(), mergeEdgep);
        } else {
            // Remove the siblingMC
            m_sb.removeSibling(mergeSibsp);
        }

        // This also updates cost on recipientp
        recipientp->moveAllVerticesFrom(donorp);

        UINFO(9, "recipient = " << recipientp->id() << ", donor = " << donorp->id()
                                << ", mergeEdgep = " << mergeEdgep << "\n"
                                << "recipientNewCpFwd = " << recipientNewCpFwd.cp
                                << (recipientNewCpFwd.propagate ? " true " : " false ")
                                << recipientNewCpFwd.propagateCp << "\n"
                                << "donorNewCpFwd = " << donorNewCpFwd.cp
                                << (donorNewCpFwd.propagate ? " true " : " false ")
                                << donorNewCpFwd.propagateCp);

        recipientp->setCritPathCost(GraphWay::FORWARD, recipientNewCpFwd.cp);
        if (recipientNewCpFwd.propagate) {
            m_mTaskGraph.forwardPropagator().cpHasIncreased(recipientp,
                                                            recipientNewCpFwd.propagateCp);
        }
        recipientp->setCritPathCost(GraphWay::REVERSE, recipientNewCpRev.cp);
        if (recipientNewCpRev.propagate) {
            m_mTaskGraph.reversePropagator().cpHasIncreased(recipientp,
                                                            recipientNewCpRev.propagateCp);
        }
        if (donorNewCpFwd.propagate) {
            m_mTaskGraph.forwardPropagator().cpHasIncreased(donorp, donorNewCpFwd.propagateCp);
        }
        if (donorNewCpRev.propagate) {
            m_mTaskGraph.reversePropagator().cpHasIncreased(donorp, donorNewCpRev.propagateCp);
        }
        m_mTaskGraph.forwardPropagator().go();
        m_mTaskGraph.reversePropagator().go();

        // Remove all other SiblingMCs that include recipientp or donorp. We remove all siblingMCs
        // of recipientp so we do not get huge numbers of SiblingMCs. We'll recreate them below, up
        // to a bounded number.
        removeSiblingMCs(recipientp, donorp);

        // Redirect all edges, delete donorp
        partRedirectEdgesFrom(m_mTaskGraph, recipientp, donorp, m_sb);

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
        UINFO(6, "Did rescore. Merges since previous = " << m_mergesSinceRescore);

        m_mergesSinceRescore = 0;
        m_scoreLimitBeforeRescore
            = std::numeric_limits<decltype(m_scoreLimitBeforeRescore)>::max();
    }

    void makeSiblingMC(LogicMTask* ap, LogicMTask* bp) {
        if (ap->id() < bp->id()) std::swap(ap, bp);
        // The higher id vertex owns the association set
        const auto first = mtaskData(ap).siblings.insert(bp).second;
        if (first) {
            m_sb.addSibling(ap, bp);
            return;
        }

        if (VL_UNLIKELY(m_slowAsserts)) {
            // It's fine if we already have this SiblingMC, we may have
            // created it earlier. Just confirm that we have associated data.
            bool found = false;
            for (const SiblingMC& smc : mtaskData(ap).aSiblingMCs) {
                UASSERT_OBJ(smc.ap() == ap, ap, "Inconsistent SiblingMC");
                if (smc.bp() == bp) found = true;
            }
            UASSERT_OBJ(found, ap, "Sibling not found");
        }
    }

    template <GraphWay::en N_Way, bool N_Exhaustive>
    void siblingPairFromRelatives(V3GraphVertex* mtaskp) {
        constexpr GraphWay way{N_Way};
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
            uint64_t m_cp;
            uint32_t m_id;
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

        if (N_Exhaustive || n <= 2 * MAX_NONEXHAUSTIVE_PAIRS) {
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

    // CONSTRUCTORS
    Contraction(OrderMTaskGraph& mTaskGraph, uint64_t scoreLimit)
        : m_mTaskGraph{mTaskGraph}
        , m_scoreLimit{scoreLimit} {

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

        // Set up the critical path into and out of each node, then coarsen the graph.
        partInitCriticalPaths(mTaskGraph);

        const uint32_t maxMTasks = []() -> uint32_t {
            // If specified, use the given value
            const int given = v3Global.opt.threadsMaxMTasks();
            if (given > 0) return given;
            // Unspecified so estimate
            return PART_DEFAULT_MAX_MTASKS_PER_THREAD * v3Global.opt.threads();
        }();

        // OPTIMIZATION PASS: Edge contraction and sibling contraction.
        //  - Score pairs of LogicMTask which are a candidate to merge.
        //    * Each edge defines such a candidate pair
        //    * Two LogicMTask that are prereqs or postreqs of a common third
        //      vertex are "siblings", these are also a candidate pair.
        //  - Build a list of MergeCandidates, sorted by score.
        //  - Merge the best pair.
        //  - Incrementally recompute critical paths near the merged mtask.

        // Allocate and assign the auxiliary data for every LogicMTask.
        {
            const size_t nMTasks = m_mTaskGraph.vertices().size();
            m_mtaskDatap.reset(new MTaskContractionData[nMTasks]);
            size_t i = 0;
            for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) vtx.userp(&m_mtaskDatap[i++]);
            UASSERT(i == nMTasks, "Inconsistent MTask count");
        }

        // Add initial candidates
        for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) {
            for (V3GraphEdge& edge : vtx.outEdges()) m_sb.addEdge(static_cast<MTaskEdge*>(&edge));
            siblingPairFromRelatives<GraphWay::REVERSE, true>(&vtx);
            siblingPairFromRelatives<GraphWay::FORWARD, true>(&vtx);
        }

        // Set initial scores in scoreboard
        doRescore();

        while (true) {
            // This is the best edge to merge, with the lowest score (shortest local critical path)
            MergeCandidate* const mergeCanp = m_sb.best();
            if (!mergeCanp) {
                if (!m_sb.needsRescore()) break;  // No more eligible candidates
                // Rescore the scoreboard and try again
                doRescore();
                continue;
            }

            UASSERT(!m_sb.needsRescore(mergeCanp),
                    "Need-rescore items should not be returned by bestp");

            const uint64_t cachedScore = mergeCanp->score();
            mergeCanp->rescore();
            const uint64_t actualScore = mergeCanp->score();

            // If cached score is out-of-date, mark this elem as in need of a rescore and continue.
            // cppcheck-suppress knownConditionTrueFalse // they are in fact different
            if (actualScore > cachedScore) {
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
                }

                // We've exhausted everything below m_scoreLimit; stop.

                // Except, if we have too many LogicMTasks, raise the score limit and keep going...
                const unsigned mtaskCount = m_mTaskGraph.vertices().size();
                if (mtaskCount > maxMTasks) {
                    const uint64_t oldLimit = m_scoreLimit;
                    m_scoreLimit = (m_scoreLimit * 120) / 100;
                    FileLine* const flp = v3Global.rootp()->fileline();
                    if (!flp->warnIsOff(V3ErrorCode::UNOPTTHREADS)) {
                        flp->v3warn(UNOPTTHREADS,
                                    "Thread scheduler is unable to provide requested "
                                    "parallelism; suggest asking for fewer threads.");
                        flp->modifyWarnOff(V3ErrorCode::UNOPTTHREADS, true);
                    }
                    UINFO(6, "Critical path limit was=" << oldLimit << " now=" << m_scoreLimit);
                    continue;
                }

                // Really stop
                break;
            }

            // If time to rescore, that will result in a higher scoreLimitBeforeRescore, and
            // possibly lower-scoring elements returned from bestp().
            if (actualScore > m_scoreLimitBeforeRescore) {
                doRescore();
                continue;
            }

            // Avoid merging the entry/exit nodes. This would create serialization, by forcing the
            // merged MTask to run before/after everything else. Empirically this helps performance
            // in a modest way by allowing other MTasks to start earlier.
            if (EdgeMC* const edgeMCp = mergeCanp->toEdgeMC()) {
                MTaskEdge* const edgep = edgeMCp->edgep();
                if (edgep->fromp() == m_entryMTaskp || edgep->top() == m_exitMTaskp) {
                    m_sb.removeEdge(edgep);
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
                if (SiblingMC* const smcp = mergeCanp->toSiblingMC()) {
                    m_sb.removeSibling(smcp);
                } else {
                    m_sb.removeEdge(mergeCanp->toEdgeMC()->edgep());
                }
                continue;
            }

            UASSERT(cachedScore == actualScore, "Calculation error in scoring");

            // Finally there's no cycle risk, no need to rescore, we're
            // within m_scoreLimit and m_scoreLimitBeforeRescore.
            // This is the edge to merge.

            // Bookkeeping: if this is the first edge we'll merge since
            // the last rescore, compute the new m_scoreLimitBeforeRescore
            // to be somewhat higher than this edge's score.
            if (!m_mergesSinceRescore) m_scoreLimitBeforeRescore = actualScore;

            // Finally merge this candidate.
            contract(mergeCanp);
        }

        // Free all remaining merge candidates. As an EdgeMC exists exactly while its edge is on
        // the scoreboard, draining the scoreboard here frees every remaining EdgeMC; edges removed
        // from the scoreboard earlier already had theirs freed. Note 'best' only ever returns
        // candidates with a known score, so this only drains the scoreboard completely if nothing
        // is left with an unknown score. Every 'break' out of the loop above is guarded on that,
        // but assert it here, as otherwise we would leak candidates.
        UASSERT(!m_sb.needsRescore(), "Should have no unknown score candidates at this point");
        while (MergeCandidate* const mergeCanp = m_sb.best()) {
            if (SiblingMC* const smcp = mergeCanp->toSiblingMC()) {
                m_sb.removeSibling(smcp);
            } else {
                m_sb.removeEdge(mergeCanp->toEdgeMC()->edgep());
            }
        }
    }

public:
    static void apply(OrderMTaskGraph& mTaskGraph, uint64_t scoreLimit) {
        Contraction{mTaskGraph, scoreLimit};
    }
};

//######################################################################
// OrderMTaskGraph entry point

void OrderMTaskGraph::contract(OrderMTaskGraph& mtaskGraph, uint64_t scoreLimit) {
    Contraction::apply(mtaskGraph, scoreLimit);
}
