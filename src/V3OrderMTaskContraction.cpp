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
//  Coarsens the fine-grained MTask graph by repeatedly contracting MTasks,
//  merging along an edge, or merging two "sibling" MTasks until a
//  critical-path limit is reached.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Global.h"
#include "V3Graph.h"
#include "V3OrderMTaskGraph.h"
#include "V3PairingHeap.h"
#include "V3PoolAllocator.h"

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

//######################################################################
// Tunable settings

// Arbitrarily limit the number of edges on a single vertex that will be
// considered when enumerating siblings, to the given value.  This protects
// the runtime in the presence of huge vertices.
//
// The sibling-merge is less important than the edge merge. Sibling merges
// can be disabled and result in halfway decent coarsening. Edge merges
// cannot be disabled, those are fundamental to the process. So, skipping
// the enumeration of some siblings on a few vertices does not have a large
// impact on the result of the partitioner.
//
// If vertices are small, the limit (at 26) approaches a no-op. Hence
// there's basically no cost to applying this limit even when no huge
// vertices are expected.
//
// If runtime is not a concern and the most precise result is desired,
// set the limit very high.
constexpr unsigned PART_SIBLING_EDGE_LIMIT = 26;

// If the user doesn't give one with '--threads-max-mtasks', we'll set the
// maximum # of MTasks to (# of threads * PART_DEFAULT_MAX_MTASKS_PER_THREAD)
constexpr unsigned PART_DEFAULT_MAX_MTASKS_PER_THREAD = 50;

//######################################################################
// MTask utility classes

struct MergeCandidateKey final {
    // Note: Structure layout chosen to minimize padding in PairingHeap<*>::Node
    uint64_t m_id;  // Unique ID part of the key
    uint64_t m_score;  // Score part of the key
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

    // This structure is extremely hot. To save 8 bytes by not having a virtual
    // function table, we implement the few polymorphic methods over the two
    // known subclasses explicitly, using a bit of the id to denote the actual
    // subtype.

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
    bool mergeWouldCreateCycle(OrderMTaskGraph& graph);

    // The current score of this candidate, which changes as the graph is contracted
    inline uint64_t currentScore();
    // The score this candidate was last given, which is its key in the scoreboard heap
    uint64_t score() const { return m_key.m_score; }
    // Set the score of this candidate to its current value. Only valid while it is not in a heap.
    void updateScore() { m_key.m_score = currentScore(); }

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

bool MergeCandidate::mergeWouldCreateCycle(OrderMTaskGraph& graph) {
    // Sibling merge: merging creates a cycle if either sibling is reachable from the other
    if (const SiblingMC* const sibp = toSiblingMC()) {
        return graph.pathExists(sibp->ap(), sibp->bp(), nullptr)
               || graph.pathExists(sibp->bp(), sibp->ap(), nullptr);
    }

    // Edge merge: merging creates a cycle if there is another path between the two MTasks
    MTaskEdge* const edgep = toEdgeMC()->edgep();
    return graph.pathExists(edgep->fromMTaskp(), edgep->toMTaskp(), edgep);
}

uint64_t MergeCandidate::currentScore() {
    // Score this candidate. The score is the new local CP length if we merge this candidate.
    // ("Local" means the longest critical path running through the merged node.)

    // Sibling merge
    if (const SiblingMC* const sibp = toSiblingMC()) {
        const LogicMTask* const ap = sibp->ap();
        const LogicMTask* const bp = sibp->bp();
        const uint64_t mergedCpFwd
            = std::max(ap->cpExclusive<GraphWay::FORWARD>(), bp->cpExclusive<GraphWay::FORWARD>());
        const uint64_t mergedCpRev
            = std::max(ap->cpExclusive<GraphWay::REVERSE>(), bp->cpExclusive<GraphWay::REVERSE>());
        return mergedCpRev + mergedCpFwd + ap->cost() + bp->cost();
    }

    // Edge merge
    {
        MTaskEdge* const edgep = toEdgeMC()->edgep();
        const LogicMTask* const fromp = edgep->fromMTaskp();
        const LogicMTask* const top = edgep->toMTaskp();
        const uint64_t mergedCpFwd = std::max(fromp->cpExclusive<GraphWay::FORWARD>(),
                                              top->cpExclusiveWithout<GraphWay::FORWARD>(edgep));
        const uint64_t mergedCpRev = std::max(fromp->cpExclusiveWithout<GraphWay::REVERSE>(edgep),
                                              top->cpExclusive<GraphWay::REVERSE>());
        // Give a slight preference to sibling merges by increasing the cost of edge merges.
        // This biases towards sibling merges in case they are equal score with edge merges.
        // This avoid a central node growing while many leaves remain due to edge merges.
        return 1 + mergedCpRev + mergedCpFwd + fromp->cost() + top->cost();
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

// Scoreboard of MTask merge candidates.
//
// This is a heap, sorted by the local critical path that would result from merging the candidate,
// that is: the longest critical path running through the merged MTask. Merges proceed by picking
// the candidate yielding the lowest such critical path, which is the merge that does the least
// damage: a merge can only ever lengthen paths, and one whose local critical path is no longer
// than the current global critical path cannot lengthen that at all.
//
// A candidate's score changes as the graph is contracted, so the score a candidate is in the heap
// with is only the score it was last given, which is a lower bound on its current score. This
// makes the top of the heap a lower bound on the score of every candidate, so the caller can pick
// the best candidate by checking whether the top still has the score it was given, and
// rescoring it if not (see the contraction loop).
//
// The scoreboard owns the lifetime of the merge candidate objects: callers add/remove candidates
// via the methods below and never allocate or free them directly. For edges this maintains the
// invariant that an MTaskEdge has an associated EdgeMC (held in its userp()), if and only if it is
// currently on the scoreboard.
class MergeCandidateScoreboard final {
    // TYPES
    using Heap = PairingHeap<MergeCandidateKey>;

    // MEMBERS
    Heap m_heap;  // The heap of candidates, keyed on their score (see class comment above)
    PoolAllocator<EdgeMC> m_edgeMCPool;  // Allocator for the edge merge candidates
    PoolAllocator<SiblingMC> m_siblingMCPool;  // Allocator for the sibling merge candidates

    // METHODS
    // Set the score of a candidate and add it to the heap. The score is computed from the critical
    // paths of the MTasks, which are up to date while the graph is being contracted.
    void insert(MergeCandidate* nodep) {
        nodep->updateScore();
        m_heap.insert(nodep);
    }

    // Remove a candidate from the scoreboard.
    void remove(MergeCandidate* nodep) { m_heap.remove(nodep); }

public:
    // CONSTRUCTORS
    MergeCandidateScoreboard() = default;
    ~MergeCandidateScoreboard() = default;
    VL_UNCOPYABLE(MergeCandidateScoreboard);

    // The candidate with the lowest score it was given, or nullptr if the scoreboard is empty.
    // Note this is only a lower bound on the best current score, see the class comment above.
    MergeCandidate* best() const { return MergeCandidate::heapNodeToElem(m_heap.max()); }

    // Update the score of a candidate to its current value, and reposition it in the heap
    void rescore(MergeCandidate* nodep) {
        remove(nodep);
        insert(nodep);
    }

    // Create a merge candidate for 'edgep' and add it to the scoreboard
    void addEdgeMC(MTaskEdge* edgep) {
        UDEBUGONLY(UASSERT(!edgep->userp(), "Edge already has a merge candidate"););
        EdgeMC* const edgeMCp = m_edgeMCPool.alloc(edgep);
        edgep->userp(edgeMCp);
        insert(edgeMCp);
    }
    // Remove 'edgep's merge candidate from the scoreboard and release it
    void removeEdgeMC(MTaskEdge* edgep) {
        EdgeMC* const edgeMCp = edgeMC(edgep);
        UDEBUGONLY(UASSERT(edgeMCp, "Edge has no merge candidate"););
        edgep->userp(nullptr);
        remove(edgeMCp);
        VL_DO_DANGLING(m_edgeMCPool.free(edgeMCp), edgeMCp);
    }

    // Create a sibling merge candidate for 'ap' and 'bp' and add it to the scoreboard
    void addSiblingMC(LogicMTask* ap, LogicMTask* bp) { insert(m_siblingMCPool.alloc(ap, bp)); }
    // Remove sibling merge candidate 'smcp' from the scoreboard and release it
    void removeSiblingMC(SiblingMC* smcp) {
        remove(smcp);
        smcp->unlinkA();
        smcp->unlinkB();
        VL_DO_DANGLING(m_siblingMCPool.free(smcp), smcp);
    }

    // Remove the given merge candidate, whichever kind it is, from the scoreboard and release it
    void removeMC(MergeCandidate* nodep) {
        if (SiblingMC* const smcp = nodep->toSiblingMC()) {
            removeSiblingMC(smcp);
        } else {
            removeEdgeMC(nodep->toEdgeMC()->edgep());
        }
    }
};

//######################################################################
// Contraction - Perform greedy edge or sibling merges on the MTask graph
class Contraction final {
    // MEMBERS
    OrderMTaskGraph& m_mTaskGraph;  // The Mtask graph
    uint64_t m_scoreLimit;  // Critical path limit for merges
    MergeCandidateScoreboard m_sb;  // Scoreboard
    // Auxiliary per-MTask data (the SiblingMC lists) attached to each MTask via its user pointer.
    // Owned here for the lifetime of this Contraction. A single array, as the number of MTasks
    // can only decrease during contraction.
    std::unique_ptr<MTaskContractionData[]> m_mtaskDatap;

    // Add merge candidates for all edges of 'mtaskp' to the scoreboard
    void addEdgeMCs(LogicMTask* mtaskp) {
        for (V3GraphEdge& e : mtaskp->outEdges()) m_sb.addEdgeMC(static_cast<MTaskEdge*>(&e));
        for (V3GraphEdge& e : mtaskp->inEdges()) m_sb.addEdgeMC(static_cast<MTaskEdge*>(&e));
    }

    // Remove the merge candidates of all edges of 'mtaskp' from the scoreboard.
    void removeEdgeMCs(LogicMTask* mtaskp) {
        // Note not all edges have a merge candidate:
        // those rejected by the main contraction loop had theirs removed there.
        for (V3GraphEdge& edge : mtaskp->outEdges()) {
            MTaskEdge* const edgep = static_cast<MTaskEdge*>(&edge);
            if (edgeMC(edgep)) m_sb.removeEdgeMC(edgep);
        }
        for (V3GraphEdge& edge : mtaskp->inEdges()) {
            MTaskEdge* const edgep = static_cast<MTaskEdge*>(&edge);
            if (edgeMC(edgep)) m_sb.removeEdgeMC(edgep);
        }
    }

    void makeSiblingMC(LogicMTask* ap, LogicMTask* bp) {
        if (ap->id() < bp->id()) std::swap(ap, bp);
        // The higher id vertex owns the association set
        const bool first = mtaskData(ap).siblings.insert(bp).second;
        if (first) {
            m_sb.addSiblingMC(ap, bp);
            return;
        }

        if (VL_UNLIKELY(m_mTaskGraph.slowAsserts())) {
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
    void addSiblingMCsFromRelatives(LogicMTask* mtaskp) {
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
            sortRecs[n].m_cp = otherp->cpInclusive<way>();
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

    void removeSiblingMCs(LogicMTask* mtaskp) {
        // Note: 'removeSiblingMC' unlinks the candidate from both of its MTasks' lists, so taking
        // the front element repeatedly does terminate. It also erases the candidate from the
        // owning (higher id) MTask's sibling set as it goes, so both the sets and the lists are
        // left consistent, whichever side of the candidate 'mtaskp' happens to be on.
        while (SiblingMC* const smcp = mtaskData(mtaskp).aSiblingMCs.frontp()) {
            m_sb.removeSiblingMC(smcp);
        }
        while (SiblingMC* const smcp = mtaskData(mtaskp).bSiblingMCs.frontp()) {
            m_sb.removeSiblingMC(smcp);
        }
    }

    // Merge the two MTasks of 'mergeCanp'
    void contract(MergeCandidate* mergeCanp) {
        // The two MTasks to merge. Note the order of the two decides which of them becomes the
        // recipient below when their costs are equal, so keep it stable.
        LogicMTask* fromp;
        LogicMTask* top;
        if (const EdgeMC* const edgeMCp = mergeCanp->toEdgeMC()) {
            fromp = edgeMCp->edgep()->fromMTaskp();
            top = edgeMCp->edgep()->toMTaskp();
        } else {
            const SiblingMC* const sibMCp = mergeCanp->toSiblingMC();
            fromp = sibMCp->bp();
            top = sibMCp->ap();
        }

        // Merge the smaller mtask into the larger mtask.
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

        // Remove all SiblingMCs that include either MTask
        removeSiblingMCs(recipientp);
        removeSiblingMCs(donorp);

        // Remove the EdgeMCs of both MTasks
        removeEdgeMCs(recipientp);
        removeEdgeMCs(donorp);

        // Merge the MTasks. This redirects all edges, updates critical paths, and deletes donorp
        m_mTaskGraph.mergeMTasks(recipientp, donorp);
        VL_DANGLING(donorp);

        // Confirm we haven't botched the CP updates. This is a whole graph walk after every single
        // merge, so it is quadratic in the size of the graph, hence only under '--debug 9'.
        if (VL_UNLIKELY(debug() >= 9)) m_mTaskGraph.validate();

        // Add the EdgeMCs of the merged MTask
        addEdgeMCs(recipientp);

        // Finally, make new sibling pairs as needed:
        //  - prereqs and postreqs of recipientp
        //  - prereqs of recipientp's postreqs
        //  - postreqs of recipientp's prereqs
        // Note that this depends on the updated critical paths (above).
        addSiblingMCsFromRelatives<GraphWay::REVERSE, true>(recipientp);
        addSiblingMCsFromRelatives<GraphWay::FORWARD, true>(recipientp);
        unsigned edges = 0;
        for (V3GraphEdge& edge : recipientp->outEdges()) {
            LogicMTask* const postreqp = static_cast<LogicMTask*>(edge.top());
            addSiblingMCsFromRelatives<GraphWay::REVERSE, false>(postreqp);
            ++edges;
            if (edges >= PART_SIBLING_EDGE_LIMIT) break;
        }
        edges = 0;
        for (V3GraphEdge& edge : recipientp->inEdges()) {
            LogicMTask* const prereqp = static_cast<LogicMTask*>(edge.fromp());
            addSiblingMCsFromRelatives<GraphWay::FORWARD, false>(prereqp);
            ++edges;
            if (edges >= PART_SIBLING_EDGE_LIMIT) break;
        }
    }

    // CONSTRUCTORS
    Contraction(OrderMTaskGraph& mTaskGraph, uint64_t cpLimit)
        : m_mTaskGraph{mTaskGraph}
        , m_scoreLimit{cpLimit} {

        // Check the graph we were given is consistent.
        m_mTaskGraph.validate();

        // Figure out maximum number of MTasks
        const uint32_t maxMTasks = []() -> uint32_t {
            // If specified, use the given value
            const int given = v3Global.opt.threadsMaxMTasks();
            if (given > 0) return given;
            // Unspecified so estimate
            return PART_DEFAULT_MAX_MTASKS_PER_THREAD * v3Global.opt.threads();
        }();

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
            for (V3GraphEdge& edge : vtx.outEdges())
                m_sb.addEdgeMC(static_cast<MTaskEdge*>(&edge));
            LogicMTask* const mtaskp = static_cast<LogicMTask*>(&vtx);
            addSiblingMCsFromRelatives<GraphWay::REVERSE, true>(mtaskp);
            addSiblingMCsFromRelatives<GraphWay::FORWARD, true>(mtaskp);
        }

        while (true) {
            // Pick the candidate yielding the lowest local critical path.
            MergeCandidate* const mergeCanp = m_sb.best();
            if (!mergeCanp) break;  // No more candidates

            // If the score has changed since it was inserted into the scoreboard, rescore it and
            // pick again. (The real scores can differ from the one used to insert it into the
            // scoreboard, due to merges between insertion and retrieval.)
            const uint64_t score = mergeCanp->currentScore();
            if (score != mergeCanp->score()) {
                m_sb.rescore(mergeCanp);
                continue;
            }

            // Check if the critical path limit is reached.
            if (score > m_scoreLimit) {

                // If there are still too many MTasks, raise the limit and keep going
                const unsigned mtaskCount = m_mTaskGraph.vertices().size();
                if (mtaskCount > maxMTasks) {
                    m_scoreLimit = (m_scoreLimit * 120) / 100;
                    FileLine* const flp = v3Global.rootp()->fileline();
                    if (!flp->warnIsOff(V3ErrorCode::UNOPTTHREADS)) {
                        flp->v3warn(UNOPTTHREADS,
                                    "Thread scheduler is unable to provide requested "
                                    "parallelism; suggest asking for fewer threads.");
                        flp->modifyWarnOff(V3ErrorCode::UNOPTTHREADS, true);
                    }
                    continue;
                }

                // MTasks limit and CP limit reached. Stop.
                break;
            }

            // Avoid merging the entry/exit nodes. This would create serialization, by forcing the
            // merged MTask to run before/after everything else. Empirically this helps performance
            // in a modest way by allowing other MTasks to start earlier.
            if (EdgeMC* const edgeMCp = mergeCanp->toEdgeMC()) {
                MTaskEdge* const edgep = edgeMCp->edgep();
                if (edgep->fromp() == m_mTaskGraph.entryp()
                    || edgep->top() == m_mTaskGraph.exitp()) {
                    m_sb.removeEdgeMC(edgep);
                    continue;
                }
            }

            // Avoid merging any edge that would create a cycle. For example suppose we begin with
            // vertices A, B, C and edges A->B, B->C, A->C. Merging A->C would create a cycle.
            if (mergeCanp->mergeWouldCreateCycle(m_mTaskGraph)) {
                m_sb.removeMC(mergeCanp);
                continue;
            }

            // Merge this candidate
            contract(mergeCanp);
        }

        // Free all remaining merge candidates.
        while (MergeCandidate* const mergeCanp = m_sb.best()) m_sb.removeMC(mergeCanp);
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
