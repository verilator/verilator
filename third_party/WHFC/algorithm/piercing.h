#pragma once

#include <array>

#include "../definitions.h"
#include "cutter_state.h"

namespace whfc {

    template<class FlowAlgorithm>
    class Piercer {
    public:
        explicit Piercer(FlowHypergraph& hg, CutterState<FlowAlgorithm>& cs) : hg(hg), cs(cs) {}

        bool findPiercingNode(bool reject_piercing_if_augmenting) {
            if (cs.notSettledNodeWeight() == 0)
                return false;

            NodeBorder* border = cs.side_to_pierce == 0 ? &cs.border_nodes.source_side : &cs.border_nodes.target_side;
            cs.clearPiercingNodes();
            size_t num_piercing_nodes = 0;
            const bool add_all_unreachables = cs.addingAllUnreachableNodesDoesNotChangeHeavierBlock() && !cs.most_balanced_cut_mode;

            for (Index i = 0; i != 2; ++i) {
                HopDistance& dist = border->max_occupied_bucket[i];
                const size_t max_num_piercing_nodes = (i == 0 || cs.most_balanced_cut_mode) ? 1 : estimateMaxNumPiercingNodes();

                for (; dist >= border->min_occupied_bucket[i]; --dist) {
                    NodeBorder::Bucket& bucket = border->buckets[dist][i];

                    if (i == NodeBorder::not_reachable_bucket_index && add_all_unreachables) {
                        // bucket.prepare(deterministic); // Not necessary for equal partitions, but necessary for equal piercing sequences
                        // add all unreachable border nodes to speed up the process (we're going to add all unreachable nodes anyway)
                        for (Node candidate : bucket) {
                            if (cs.isNonTerminal(candidate) && settlingDoesNotExceedMaxWeight(candidate)) {
                                if (!cs.reachableFromSideNotToPierce(candidate)) {
                                    cs.addPiercingNode(candidate);
                                    num_piercing_nodes++;
                                } else {
                                    border->insertIntoBucket(candidate, NodeBorder::reachable_bucket_index, dist);
                                }
                            }
                        }
                        bucket.clear();
                    } else {
                        // in deterministic mode we have to filter the list first
                        // we store candidates that become terminals after we discover them as candidates
                        // the BFS visit order affects how many of these superfluous candidates we get, so the random number generation below is
                        // non-deterministic if we have them all in there.
                        if (deterministic) {
                            auto new_end = std::remove_if(bucket.begin() + bucket.sorted_end, bucket.end(), [&](Node u) {
                                if (!cs.isNonTerminal(u)) {
                                    if (cs.most_balanced_cut_mode) {
                                        // track for reset
                                        border->removed_during_most_balanced_cut_mode[i].push_back(u);
                                    }
                                    return true;
                                }
                                return false;
                            });
                            bucket.nodes.erase(new_end, bucket.end());
                        }
                        bucket.prepare(deterministic);

                        // the old random, lazy-clear method. except we might do more than one node
                        while (!bucket.empty()) {
                            size_t pos = cs.rng.randomIndex(0, bucket.size() - 1);
                            Node candidate = bucket.get_and_remove(pos);

                            if (cs.most_balanced_cut_mode) {
                                // track for reset
                                border->removed_during_most_balanced_cut_mode[i].push_back(candidate);
                            }

                            if (cs.isNonTerminal(candidate) && settlingDoesNotExceedMaxWeight(candidate)) {
                                if (i != NodeBorder::not_reachable_bucket_index || !cs.reachableFromSideNotToPierce(candidate)) {
                                    cs.addPiercingNode(candidate);
                                    if (++num_piercing_nodes >= max_num_piercing_nodes) {
                                        if (use_bulk_piercing && i == 1 && !cs.most_balanced_cut_mode) {
                                            bulk_piercing[cs.side_to_pierce].total_bulk_piercing_nodes += num_piercing_nodes;
                                        }
                                        return true;
                                    }
                                    // restrict adding multiple nodes to one distance bucket at a time?
                                } else if (!cs.most_balanced_cut_mode) {
                                    // node got reachable --> move to other bucket. (no need to move if it can't be pierced in the future)
                                    border->insertIntoBucket(candidate, NodeBorder::reachable_bucket_index, dist);
                                }
                            }
                        }
                    }
                }

                border->clearBuckets(i);

                if (num_piercing_nodes > 0) {
                    if (use_bulk_piercing && i == 1 && !cs.most_balanced_cut_mode) {
                        bulk_piercing[cs.side_to_pierce].total_bulk_piercing_nodes += num_piercing_nodes;
                    }
                    return true;
                } else if (i == NodeBorder::not_reachable_bucket_index && !cs.most_balanced_cut_mode) {
                    if (cs.unclaimedNodeWeight() > 0) {

                        // nodes may have been mis-classified as reachable when first inserted (this happens with nodes that get isolated)
                        // move those to the first PQ
                        size_t num_moved = 0;
                        size_t r = NodeBorder::reachable_bucket_index;
                        for (HopDistance d = border->max_occupied_bucket[r]; d >= border->min_occupied_bucket[r]; --d) {
                            auto& bucket = border->buckets[d][r];
                            bucket.prepare(deterministic);

                            auto new_end = std::remove_if(bucket.begin(), bucket.end(), [&](const Node& u) {
                                if (cs.isNonTerminal(u)) {
                                    if (!cs.reachableFromSideNotToPierce(u)) {
                                        num_moved++;
                                        border->insertIntoBucket(u, NodeBorder::not_reachable_bucket_index, d);
                                        return true;
                                    }
                                    return false;
                                }
                                return true;
                            });
                            bucket.erase(new_end, bucket.end());
                        }

                        if (num_moved > 0) {
                            --i; // go again with i == 0 in the next round
                        }
                    } else if (reject_piercing_if_augmenting) {
                        // in mbc mode there can be unreachable nodes in the 2nd bucket
                        return false;
                    }
                }
            }

            if (reject_piercing_if_augmenting) {
                return false;
            }

            Node p = invalidNode;
            if (piercing_fallbacks[cs.side_to_pierce]++ < piercing_fallback_limit_per_side) {
                // didn't find one in the bucket PQs, so pick a random unsettled node
                uint32_t rndScore = 0;
                HopDistance d = 0;
                for (const Node u : hg.nodeIDs()) {
                    if (isCandidate(u)) {
                        const HopDistance dist_u = border->getDistance(u);
                        if (dist_u >= d) {
                            const uint32_t score_u = cs.rng.randomNumber(1, max_random_score);
                            if (dist_u > d || score_u > rndScore) {
                                rndScore = score_u;
                                p = u;
                                d = dist_u;
                            }
                        }
                    }
                }
            }

            if (p != invalidNode) {
                cs.addPiercingNode(p);
                return true;
            } else {
                return false;
            }
        }

        void reset() { piercing_fallbacks = { 0, 0 }; }

        void initialize() { initializeBulkPiercing(); }

        void setBulkPiercing(bool use) { use_bulk_piercing = use; }

        bool deterministic = false;

    private:
        bool isCandidate(const Node u) const { return cs.isNonTerminal(u) && settlingDoesNotExceedMaxWeight(u); }

        bool settlingDoesNotExceedMaxWeight(const Node u) const {
            return (cs.side_to_pierce == 0 ? cs.source_weight : cs.target_weight) + hg.nodeWeight(u) <= cs.maxBlockWeight(cs.side_to_pierce);
        }

        FlowHypergraph& hg;
        CutterState<FlowAlgorithm>& cs;

        static constexpr uint32_t max_random_score = 1 << 25;

        std::array<int, 2> piercing_fallbacks = { 0, 0 };
        static constexpr int piercing_fallback_limit_per_side = 3;

        size_t estimateMaxNumPiercingNodes() {
            int side = cs.side_to_pierce;
            if (!use_bulk_piercing || ++bulk_piercing[side].num_steps < 5 || bulk_piercing[side].stop) {
                LOGGER << "estimate 1" << V(bulk_piercing[side].num_steps);
                return 1;
            }
            auto& bp = bulk_piercing[side];
            bp.current_tier_weight_goal *= next_tier_scaling_factor;
            bp.current_tier_weight_goal_remaining += bp.current_tier_weight_goal;

            NodeWeight added = (side == 0 ? cs.source_weight : cs.target_weight) - bp.initial_terminal_weight - bp.weight_added_so_far;
            bp.weight_added_so_far += added;
            bp.current_tier_weight_goal_remaining -= added;

            double speed = double(bp.weight_added_so_far) / double(bp.total_bulk_piercing_nodes);
            LOGGER << V(speed) << V(bp.weight_added_so_far) << V(bp.total_bulk_piercing_nodes);

            if (bp.current_tier_weight_goal_remaining <= speed) { // this intentionally includes remaining < 0 !
                LOGGER << "estimate 1. too little left in tier";
                return 1;
            }
            size_t res = bp.current_tier_weight_goal_remaining / speed;
            LOGGER << V(res);
            return res;
        }

        void initializeBulkPiercing() {
            for (int side = 0; side < 2; ++side) {
                auto& bp = bulk_piercing[side];
                bp = BulkPierce();

                bp.initial_terminal_weight = (side == 0 ? cs.source_weight : cs.target_weight);
                double ratio = static_cast<double>(cs.maxBlockWeight(side)) / static_cast<double>(cs.maxBlockWeight(0) + cs.maxBlockWeight(1));
                // This can be negative if the initial weight is higher than the perfectly balanced part weight. 
                // In that case we only want to grow the other side, so this value was never being accessed in the first place, but sanitizers complain rightfully.
                bp.initial_total_weight_goal_to_add = std::max<double>(0.0, ratio * hg.totalNodeWeight() - bp.initial_terminal_weight);
                // bp.initial_total_weight_goal_to_add = cs.maxBlockWeight(side) - bp.initial_terminal_weight;
                bp.current_tier_weight_goal = bp.initial_total_weight_goal_to_add;
            }
        }

        struct BulkPierce {
            size_t num_steps = 0;
            size_t total_bulk_piercing_nodes = 0;
            NodeWeight initial_total_weight_goal_to_add = 0;
            NodeWeight current_tier_weight_goal = 0;
            NodeWeight weight_added_so_far = 0;
            NodeWeight initial_terminal_weight = 0;
            int current_tier_weight_goal_remaining = 0;
            bool stop = false;
        };
        std::array<BulkPierce, 2> bulk_piercing;
        bool use_bulk_piercing = true;
        static constexpr double next_tier_scaling_factor = 0.55;

        static constexpr bool log = false;
    };
} // namespace whfc
