#pragma once

#include <array>

#include "../datastructure/border.h"
#include "../datastructure/flow_hypergraph.h"
#include "../datastructure/node_border.h"

#include "../datastructure/border.h"
#include "../datastructure/flow_hypergraph.h"
#include "../datastructure/node_border.h"
#include "../datastructure/queue.h"
#include "../definitions.h"
#include "../util/math.h"
#include "../util/random.h"

#include <tbb/blocked_range.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_reduce.h>
#include <tbb/scalable_allocator.h>

namespace whfc {
    template<typename T>
    using vec = std::vector<T, tbb::scalable_allocator<T>>;

    struct SimulatedNodeAssignment {
        bool assign_unclaimed_to_source = true;
        bool perfect_balance = false;
        double balance_source_block = std::numeric_limits<double>::max(), balance_target_block = std::numeric_limits<double>::max();
        size_t number_of_tracked_moves = 0;

        double balance() const {
            if (perfect_balance) {
                return 1.0;
            }
            return std::min(balance_source_block, balance_target_block);
        }

        bool isPerfectlyBalanced() const { return perfect_balance || std::abs(balance_source_block - balance_target_block) < 1e-9; }
    };

    struct Move {
        Node node;
        int direction;
        Move(Node node, int dir) : node(node), direction(dir) {}
    };

    struct NonDynamicCutterState {
        vec<Node> source_piercing_nodes, target_piercing_nodes;
    };

    template<typename FlowAlgorithm>
    class CutterState {
    public:
        static constexpr bool log = false;

        using Pin = FlowHypergraph::Pin;

        FlowAlgorithm flow_algo;
        int side_to_pierce = 0;
        FlowHypergraph& hg;

        NodeWeight source_weight, target_weight, source_reachable_weight, target_reachable_weight;
        std::vector<Move> tracked_moves;

        bool force_sequential = true;

        bool augmenting_path_available_from_piercing = true;
        bool has_cut = false;
        bool most_balanced_cut_mode = false;
        HyperedgeCuts cuts;
        NodeBorders border_nodes;
        std::array<NodeWeight, 2> max_block_weight_per_side;
        bool partition_written_to_node_set = false;
        TimeReporter& timer;
        Randomizer rng;

        CutterState(FlowHypergraph& _hg, TimeReporter& timer) :
            flow_algo(_hg), hg(_hg), cuts(_hg.numHyperedges()), border_nodes(_hg.numNodes()), max_block_weight_per_side({ NodeWeight(0), NodeWeight(0) }),
            timer(timer) {}

        bool isNonTerminal(const Node u) const { return !flow_algo.isSource(u) && !flow_algo.isTarget(u); }

        NodeWeight unclaimedNodeWeight() const { return hg.totalNodeWeight() - source_reachable_weight - target_reachable_weight; }

        NodeWeight notSettledNodeWeight() const { return hg.totalNodeWeight() - source_weight - target_weight; }

        void addToSourceSideCut(const Hyperedge e) {
            // Note: the current implementation of selecting piercing nodes relies on not inserting target-reachable nodes during most balanced cut mode
            if (!cuts.source_side.wasAdded(e)) {
                cuts.source_side.add(e);
                for (const Pin& px : hg.pinsOf(e)) {
                    if (isNonTerminal(px.pin) && !border_nodes.source_side.wasAdded(px.pin) &&
                        (!most_balanced_cut_mode || !flow_algo.isTargetReachable(px.pin))) {
                        border_nodes.source_side.add(px.pin, flow_algo.isTargetReachable(px.pin));
                    }
                }
            }
        }

        void addToTargetSideCut(const Hyperedge e) {
            if (!cuts.target_side.wasAdded(e)) {
                cuts.target_side.add(e);
                for (const Pin& px : hg.pinsOf(e)) {
                    if (isNonTerminal(px.pin) && !border_nodes.target_side.wasAdded(px.pin) &&
                        (!most_balanced_cut_mode || !flow_algo.isSourceReachable(px.pin))) {
                        border_nodes.target_side.add(px.pin, flow_algo.isSourceReachable(px.pin));
                    }
                }
            }
        }

        void setMaxBlockWeight(int side, NodeWeight mw) { max_block_weight_per_side[side] = mw; }

        NodeWeight maxBlockWeight(int side) const { return max_block_weight_per_side[side]; }

        bool reachableFromSideNotToPierce(const Node u) const { return side_to_pierce == 0 ? flow_algo.isTargetReachable(u) : flow_algo.isSourceReachable(u); }

        void clearPiercingNodes() {
            has_cut = false;
            flow_algo.clearPiercingNodes(side_to_pierce == 0);
            augmenting_path_available_from_piercing = false;
        }

        void addPiercingNode(const Node piercingNode) {
            augmenting_path_available_from_piercing |= reachableFromSideNotToPierce(piercingNode);
            if (side_to_pierce == 0) {
                source_weight += hg.nodeWeight(piercingNode);
            } else {
                target_weight += hg.nodeWeight(piercingNode);
            }
            if (most_balanced_cut_mode) {
                tracked_moves.emplace_back(piercingNode, side_to_pierce);
            }
            flow_algo.pierce(piercingNode, side_to_pierce == 0);
        }

        void computeReachableWeights() {
            if (augmenting_path_available_from_piercing) {
                // tbb::parallel_invoke([&] {
                computeSourceReachableWeight();
                //	}, [&] {
                computeTargetReachableWeight();
                // });
            } else {
                // no flow increased --> one side didn't change
                if (side_to_pierce == 0) {
                    computeSourceReachableWeight();
                } else {
                    computeTargetReachableWeight();
                }
            }
            assert(source_reachable_weight + target_reachable_weight <= hg.totalNodeWeight());
        }

        void computeSourceReachableWeight() {
            auto sr = flow_algo.sourceReachableNodes();
            source_reachable_weight = source_weight;
            if (augmenting_path_available_from_piercing && sr.size() > 5000 && !force_sequential) {
                source_reachable_weight += tbb::parallel_reduce(
                        tbb::blocked_range<size_t>(0, sr.size(), 2000), 0,
                        [&](const auto& r, NodeWeight sum) -> NodeWeight {
                            for (size_t i = r.begin(); i < r.end(); ++i) {
                                Node u = sr[i];
                                assert(flow_algo.isSourceReachable(u));
                                if (flow_algo.isHypernode(u) && !flow_algo.isSource(u)) {
                                    sum += hg.nodeWeight(u);
                                }
                            }
                            return sum;
                        },
                        std::plus<>());
            } else {
                // expect less work
                for (Node u : sr) {
                    assert(flow_algo.isSourceReachable(u));
                    if (flow_algo.isHypernode(u) && !flow_algo.isSource(u)) {
                        source_reachable_weight += hg.nodeWeight(u);
                    }
                }
            }


            assert([&] {
                NodeWeight w = 0;
                for (Node u : hg.nodeIDs()) {
                    if (flow_algo.isSourceReachable(u))
                        w += hg.nodeWeight(u);
                }
                return w == source_reachable_weight;
            }());
        }

        void computeTargetReachableWeight() {
            auto tr = flow_algo.targetReachableNodes();
            target_reachable_weight = target_weight;
            if (augmenting_path_available_from_piercing && tr.size() > 5000 && !force_sequential) {
                target_reachable_weight += tbb::parallel_reduce(
                        tbb::blocked_range<size_t>(0, tr.size(), 2000), 0,
                        [&](const auto& r, NodeWeight sum) -> NodeWeight {
                            for (size_t i = r.begin(); i < r.end(); ++i) {
                                Node u = tr[i];
                                assert(flow_algo.isTargetReachable(u));
                                if (flow_algo.isHypernode(u) && !flow_algo.isTarget(u)) {
                                    sum += hg.nodeWeight(u);
                                }
                            }
                            return sum;
                        },
                        std::plus<>());
            } else {
                // expect less work
                for (Node u : tr) {
                    assert(flow_algo.isTargetReachable(u));
                    if (flow_algo.isHypernode(u) && !flow_algo.isTarget(u)) {
                        target_reachable_weight += hg.nodeWeight(u);
                    }
                }
            }

            assert([&] {
                NodeWeight w = 0;
                for (Node u : hg.nodeIDs()) {
                    if (flow_algo.isTargetReachable(u))
                        w += hg.nodeWeight(u);
                }
                return w == target_reachable_weight;
            }());
        }

        void assimilateSourceSide() {
            source_weight = source_reachable_weight;
            for (Node u : flow_algo.sourceReachableNodes()) {
                assert(flow_algo.isSourceReachable(u));
                if (!flow_algo.isSource(u)) {
                    if (most_balanced_cut_mode) {
                        tracked_moves.emplace_back(u, 0);
                    }
                    if (flow_algo.isInNode(u)) {
                        Hyperedge e = flow_algo.inNodeToEdge(u);
                        Node out_node = flow_algo.edgeToOutNode(e);
                        if (!flow_algo.isSourceReachable(out_node)) { // in node visited but not out node --> cut hyperedge
                            addToSourceSideCut(e);
                        }
                    }
                    flow_algo.makeSource(u);
                }
            }
        }

        void assimilateTargetSide() {
            target_weight = target_reachable_weight;
            for (Node u : flow_algo.targetReachableNodes()) {
                assert(flow_algo.isTargetReachable(u));
                if (!flow_algo.isTarget(u)) {
                    if (most_balanced_cut_mode) {
                        tracked_moves.emplace_back(u, 1);
                    }
                    if (flow_algo.isOutNode(u)) {
                        Hyperedge e = flow_algo.outNodeToEdge(u);
                        Node in_node = flow_algo.edgeToInNode(e);
                        if (!flow_algo.isTargetReachable(in_node)) { // out node visited but not in node --> cut hyperedge
                            addToTargetSideCut(e);
                        }
                    }
                    flow_algo.makeTarget(u);
                }
            }
        }

        void assimilate() {
            computeReachableWeights();
            side_to_pierce = sideToGrow();
            if (side_to_pierce == 0 /* source side */) {
                assimilateSourceSide();
            } else {
                assimilateTargetSide();
            }
            LOGGER << toString();
            verifyCutPostConditions();
        }


        void reset() { // TODO could consolidate with initialize
            flow_algo.reset();
            tracked_moves.clear();
            augmenting_path_available_from_piercing = true;
            has_cut = false;
            most_balanced_cut_mode = false;
            cuts.reset(hg.numHyperedges()); // this requires that FlowHypergraph is reset before resetting the CutterState
            border_nodes.reset(hg.numNodes());
            partition_written_to_node_set = false;
        }

        void initialize(Node s, Node t) {
            if (hg.nodeWeight(s) > maxBlockWeight(0) || hg.nodeWeight(t) > maxBlockWeight(1)) {
                throw std::runtime_error("Terminal weight already exceeds max block weight at initialization. Consider setting max block weights per side via "
                                         "hfc.cs.setMaxBlockWeight(  side  )");
            }

            flow_algo.initialize(s, t);

            source_weight = hg.nodeWeight(s);
            source_reachable_weight = source_weight;
            target_weight = hg.nodeWeight(t);
            target_reachable_weight = target_weight;
        }

        int sideToGrow() const {
            const double imb_s = static_cast<double>(source_reachable_weight) / static_cast<double>(maxBlockWeight(0));
            const double imb_t = static_cast<double>(target_reachable_weight) / static_cast<double>(maxBlockWeight(1));
            return imb_s <= imb_t ? 0 : 1;
        }

        bool isBalanced() {
            assert(has_cut);
            assert(!partition_written_to_node_set && "Cannot call isBalanced() once the partition has been written");
            return (source_reachable_weight <= maxBlockWeight(0) && hg.totalNodeWeight() - source_reachable_weight <= maxBlockWeight(1)) ||
                   (hg.totalNodeWeight() - target_reachable_weight <= maxBlockWeight(0) && target_reachable_weight <= maxBlockWeight(1));
        }

        bool rejectPiercingIfAugmenting() const { return most_balanced_cut_mode || flow_algo.flow_value == flow_algo.upper_flow_bound; }

        bool addingAllUnreachableNodesDoesNotChangeHeavierBlock() const {
            if (unclaimedNodeWeight() == 0) {
                return false;
            }
            if (sideToGrow() == 0) {
                const double imb_S_U = static_cast<double>(hg.totalNodeWeight() - target_reachable_weight) / static_cast<double>(maxBlockWeight(0));
                const double imb_T = static_cast<double>(target_reachable_weight) / static_cast<double>(maxBlockWeight(1));
                return imb_S_U <= imb_T;
            } else {
                const double imb_S = static_cast<double>(source_reachable_weight) / static_cast<double>(maxBlockWeight(0));
                const double imb_T_U = static_cast<double>(hg.totalNodeWeight() - source_reachable_weight) / static_cast<double>(maxBlockWeight(1));
                return imb_T_U <= imb_S;
            }
        }

        NonDynamicCutterState enterMostBalancedCutMode() {
            assert(!most_balanced_cut_mode);
            assert(tracked_moves.empty());
            assert(has_cut);
            most_balanced_cut_mode = true; // activates move tracking
            border_nodes.enterMostBalancedCutMode();
            cuts.enterMostBalancedCutMode();
            return { flow_algo.source_piercing_nodes, flow_algo.target_piercing_nodes };
        }

        void resetToFirstBalancedState(NonDynamicCutterState& nds) {
            flow_algo.source_piercing_nodes = nds.source_piercing_nodes;
            flow_algo.target_piercing_nodes = nds.target_piercing_nodes;
            revertMoves(0);
            border_nodes.resetForMostBalancedCut();
            cuts.resetForMostBalancedCut();
            side_to_pierce = sideToGrow();
        }

        SimulatedNodeAssignment mostBalancedAssignment() {
            assert(isBalanced());
            auto gap = [&](NodeWeight a, NodeWeight max_a) { return (static_cast<double>(a) / static_cast<double>(max_a)); };
            SimulatedNodeAssignment suw;
            suw.balance_source_block = gap(hg.totalNodeWeight() - target_reachable_weight, maxBlockWeight(0));
            suw.balance_target_block = gap(target_reachable_weight, maxBlockWeight(1));
            suw.assign_unclaimed_to_source = true;

            SimulatedNodeAssignment tuw;
            tuw.balance_source_block = gap(source_reachable_weight, maxBlockWeight(0));
            tuw.balance_target_block = gap(hg.totalNodeWeight() - source_reachable_weight, maxBlockWeight(1));
            tuw.assign_unclaimed_to_source = false;

            if (maxBlockWeight(0) == maxBlockWeight(1) && hg.totalNodeWeight() % 2 == 1) {
                // special case because it's harder to catch
                suw.perfect_balance = hg.totalNodeWeight() - 2 * target_reachable_weight == 1;
                tuw.perfect_balance = hg.totalNodeWeight() - 2 * source_reachable_weight == 1;
            }

            SimulatedNodeAssignment sol = suw.balance() > tuw.balance() ? suw : tuw;

            sol.number_of_tracked_moves = tracked_moves.size();
            return sol;
        }

        // takes the information from mostBalancedIsolatedNodesAssignment()
        // can be an old run, since the DP solution for trackedIsolatedWeight only contains nodes that were isolated during that run
        void writePartition(const SimulatedNodeAssignment& assignment) {
            assert(!partition_written_to_node_set);
            assert(isBalanced());

            for (Node u : hg.nodeIDs()) {
                if (flow_algo.isSourceReachable(u) && !flow_algo.isSource(u)) {
                    flow_algo.makeSource(u);
                    source_weight += hg.nodeWeight(u);
                } else if (flow_algo.isTargetReachable(u) && !flow_algo.isTarget(u)) {
                    flow_algo.makeTarget(u);
                    target_weight += hg.nodeWeight(u);
                } else if (!flow_algo.isSourceReachable(u) && !flow_algo.isTargetReachable(u)) {
                    if (assignment.assign_unclaimed_to_source) {
                        flow_algo.makeSource(u);
                        source_weight += hg.nodeWeight(u);
                    } else {
                        flow_algo.makeTarget(u);
                        target_weight += hg.nodeWeight(u);
                    }
                }
            }

            assert(source_weight + target_weight == hg.totalNodeWeight());
            source_reachable_weight = source_weight;
            target_reachable_weight = target_weight;
            partition_written_to_node_set = true;

#ifndef NDEBUG
            NodeWeight sw = 0, tw = 0;
            for (Node u : hg.nodeIDs()) {
                assert(flow_algo.isSource(u) || flow_algo.isTarget(u));
                if (flow_algo.isSource(u))
                    sw += hg.nodeWeight(u);
                else
                    tw += hg.nodeWeight(u);
            }
            assert(source_weight == sw);
            assert(target_weight == tw);
#endif
            verifyCutInducedByPartitionMatchesFlowValue();
        }

        void writePartition() { writePartition(mostBalancedAssignment()); }

        void revertMoves(const size_t numberOfTrackedMoves) {
            // only in most balanced cut mode --> no need for parallelism
            while (tracked_moves.size() > numberOfTrackedMoves) {
                Move& m = tracked_moves.back();
                flow_algo.unreach(m.node);
                if (flow_algo.isHypernode(m.node)) {
                    if (m.direction == 0)
                        source_weight -= hg.nodeWeight(m.node);
                    else
                        target_weight -= hg.nodeWeight(m.node);
                }
                tracked_moves.pop_back();
            }
            source_reachable_weight = source_weight;
            target_reachable_weight = target_weight;
        }

        void applyMoves(const std::vector<Move>& moves) {
            for (const Move& m : moves) {
                if (m.direction == 0) {
                    flow_algo.makeSource(m.node);
                    if (flow_algo.isHypernode(m.node))
                        source_weight += hg.nodeWeight(m.node);
                } else {
                    flow_algo.makeTarget(m.node);
                    if (flow_algo.isHypernode(m.node))
                        target_weight += hg.nodeWeight(m.node);
                }
            }
            source_reachable_weight = source_weight;
            target_reachable_weight = target_weight;
        }

        std::string toString(bool skip_iso_and_unclaimed = false) {
            std::stringstream os;
            os << " cut= " << flow_algo.flow_value << " s=" << source_weight << "|" << source_reachable_weight << " t=" << target_weight << "|"
               << target_reachable_weight;
            if (!skip_iso_and_unclaimed) {
                os << " u=" << unclaimedNodeWeight();
            }
            os << " mbw=[" << maxBlockWeight(0) << " " << maxBlockWeight(1) << "]"
               << " total=" << hg.totalNodeWeight();
            return os.str();
        }

        void verifyCutPostConditions() {
            assert(has_cut);

#ifndef NDEBUG
            Flow expected_flow = 0;
            if (side_to_pierce == 0) {
                cuts.source_side.cleanUp([&](const Hyperedge& e) { return flow_algo.isSource(flow_algo.edgeToOutNode(e)); });
                for (const Hyperedge& e : cuts.source_side.entries()) {
                    assert(flow_algo.isSource(flow_algo.edgeToInNode(e)) && !flow_algo.isSource(flow_algo.edgeToOutNode(e)));
                    assert(flow_algo.flow[flow_algo.bridgeEdgeIndex(e)] == hg.capacity(e));
                    expected_flow += hg.capacity(e);
                }
            } else {
                cuts.target_side.cleanUp([&](const Hyperedge& e) { return flow_algo.isTarget(flow_algo.edgeToInNode(e)); });
                for (const Hyperedge& e : cuts.target_side.entries()) {
                    assert(!flow_algo.isTarget(flow_algo.edgeToInNode(e)) && flow_algo.isTarget(flow_algo.edgeToOutNode(e)));
                    assert(flow_algo.flow[flow_algo.bridgeEdgeIndex(e)] == hg.capacity(e));
                    expected_flow += hg.capacity(e);
                }
            }
            verifyCutInducedByPartitionMatchesExtractedCutHyperedges();
            verifyExtractedCutHyperedgesActuallySplitHypergraph();
            assert(flow_algo.flow_value == expected_flow);
#endif
        }

        void verifyCutInducedByPartitionMatchesExtractedCutHyperedges() {
#ifndef NDEBUG
            std::vector<Hyperedge> cut_from_partition;
            if (side_to_pierce == 0) {
                for (Hyperedge e : hg.hyperedgeIDs()) {
                    bool hasSource = false;
                    bool hasOther = false;
                    for (Pin& p : hg.pinsOf(e)) {
                        Node v = p.pin;
                        hasSource |= flow_algo.isSource(v);
                        hasOther |= !flow_algo.isSource(v);
                    }

                    if (hasSource && hasOther) {
                        cut_from_partition.push_back(e);
                        assert(flow_algo.isSource(flow_algo.edgeToInNode(e)));
                    }

                    if (hasSource && !hasOther) {
                        assert(flow_algo.isSource(flow_algo.edgeToOutNode(e)));
                    }
                }
                auto sorted_cut = cuts.source_side.copy();
                std::sort(sorted_cut.begin(), sorted_cut.end());
                assert(sorted_cut == cut_from_partition);
            } else {
                for (Hyperedge e : hg.hyperedgeIDs()) {
                    bool hasTarget = false;
                    bool hasOther = false;
                    for (Pin& p : hg.pinsOf(e)) {
                        Node v = p.pin;
                        hasTarget |= flow_algo.isTarget(v);
                        hasOther |= !flow_algo.isTarget(v);
                    }
                    if (hasTarget && hasOther) {
                        cut_from_partition.push_back(e);
                        assert(flow_algo.isTarget(flow_algo.edgeToOutNode(e)));
                    }

                    if (hasTarget && !hasOther) {
                        assert(flow_algo.isTarget(flow_algo.edgeToInNode(e)));
                    }
                }
                auto sorted_cut = cuts.target_side.copy();
                std::sort(sorted_cut.begin(), sorted_cut.end());
                assert(sorted_cut == cut_from_partition);
            }
#endif
        }

        void verifyCutInducedByPartitionMatchesFlowValue() {
#ifndef NDEBUG
            Flow cut_weight = 0, t_cut_weight = 0;
            for (Hyperedge e : hg.hyperedgeIDs()) {
                bool hasSource = false, hasOther = false, hasTarget = false, hasTargetOther = false;
                for (Pin& p : hg.pinsOf(e)) {
                    hasSource |= flow_algo.isSource(p.pin);
                    hasOther |= !flow_algo.isSource(p.pin);
                    hasTarget |= flow_algo.isTarget(p.pin);
                    hasTargetOther |= !flow_algo.isTarget(p.pin);
                }
                if (hasTarget && hasTargetOther) {
                    assert(flow_algo.flow[flow_algo.bridgeEdgeIndex(e)] == hg.capacity(e));
                    t_cut_weight += hg.capacity(e);
                }

                if (hasSource && hasOther) {
                    assert(flow_algo.flow[flow_algo.bridgeEdgeIndex(e)] == hg.capacity(e));
                    cut_weight += hg.capacity(e);
                }
            }
            assert(flow_algo.flow_value == t_cut_weight);
            assert(flow_algo.flow_value == cut_weight);
#endif
        }


        void verifyExtractedCutHyperedgesActuallySplitHypergraph() {
#ifndef NDEBUG
            BitVector he_seen(hg.numHyperedges()), node_seen(hg.numNodes());
            LayeredQueue<Node> queue(hg.numNodes());
            for (Node u : hg.nodeIDs()) {
                if (flow_algo.isSource(u)) {
                    queue.push(u);
                    node_seen.set(u);
                }
            }

            bool source_side_grown = side_to_pierce == 0;

            if (source_side_grown) {
                for (Hyperedge e : cuts.source_side.entries())
                    he_seen.set(e);
            } else {
                for (Hyperedge e : cuts.target_side.entries())
                    he_seen.set(e);
            }

            while (!queue.empty()) {
                Node u = queue.pop();
                for (auto& he_inc : hg.hyperedgesOf(u)) {
                    Hyperedge e = he_inc.e;
                    if (!he_seen[e]) {
                        he_seen.set(e);
                        for (auto& pin : hg.pinsOf(e)) {
                            Node v = pin.pin;
                            assert(!flow_algo.isTargetReachable(v));
                            // if target-side cut hyperedges are blocked but not source-side cut, we can still visit unreachable nodes
                            assert(!source_side_grown || flow_algo.isSourceReachable(v));
                            if (!node_seen[v]) {
                                node_seen.set(v);
                                queue.push(v);
                            }
                        }
                    }
                }
            }

            for (Node u : hg.nodeIDs()) {
                if (flow_algo.isTargetReachable(u))
                    assert(!node_seen[u]);
                if (flow_algo.isSourceReachable(u))
                    assert(node_seen[u]);
            }

            queue.clear();
            he_seen.reset();
            node_seen.reset();
            for (Node u : hg.nodeIDs()) {
                if (flow_algo.isTarget(u)) {
                    queue.push(u);
                    node_seen.set(u);
                }
            }

            if (side_to_pierce == 0) {
                for (Hyperedge e : cuts.source_side.entries())
                    he_seen.set(e);
            } else {
                for (Hyperedge e : cuts.target_side.entries())
                    he_seen.set(e);
            }

            while (!queue.empty()) {
                Node u = queue.pop();
                for (auto& he_inc : hg.hyperedgesOf(u)) {
                    Hyperedge e = he_inc.e;
                    if (!he_seen[e]) {
                        he_seen.set(e);
                        for (auto& pin : hg.pinsOf(e)) {
                            Node v = pin.pin;
                            assert(!flow_algo.isSourceReachable(v));
                            assert(source_side_grown || flow_algo.isTargetReachable(v)); // since we removed the source-side cut
                            if (!node_seen[v]) {
                                node_seen.set(v);
                                queue.push(v);
                            }
                        }
                    }
                }
            }

            for (Node u : hg.nodeIDs()) {
                if (flow_algo.isTargetReachable(u))
                    assert(node_seen[u]);
                if (flow_algo.isSourceReachable(u))
                    assert(!node_seen[u]);
            }
#endif
        }
    };

} // namespace whfc
