#pragma once

#include "../definitions.h"
#include "bitvector.h"

namespace whfc {

    class NodeBorder {
    public:
        struct Bucket {
            std::vector<Node> nodes;
            using iterator = decltype(nodes.begin());
            size_t sorted_end = 0;
            iterator begin() { return nodes.begin(); }
            iterator end() { return nodes.end(); }
            void clear() {
                nodes.clear();
                sorted_end = 0;
            }
            void push_back(Node u) { nodes.push_back(u); }
            bool empty() const { return nodes.empty(); }
            size_t size() const { return nodes.size(); }
            Node get_and_remove(size_t pos) {
                assert(sorted_end == nodes.size());
                Node candidate = nodes[pos];
                nodes[pos] = nodes.back();
                nodes.pop_back();
                sorted_end--;
                return candidate;
            }
            iterator erase(iterator first, iterator last) {
                assert(sorted_end == nodes.size());
                auto ret = nodes.erase(first, last);
                sorted_end = nodes.size();
                return ret;
            }
            void prepare(bool deterministic) {
                if (deterministic) {
                    std::sort(nodes.begin() + sorted_end, nodes.end());
                }
                sorted_end = nodes.size();
            }
        };

        NodeBorder(const size_t initialN, const std::vector<HopDistance>& dfc, const int multiplier) :
            was_added(initialN), buckets(10, { Bucket(), Bucket() }), max_occupied_bucket({ -1, -1 }), min_occupied_bucket({ 0, 0 }),
            backup_max_occupied_bucket({ -1, -1 }), backup_min_occupied_bucket({ 0, 0 }), removed_during_most_balanced_cut_mode({ Bucket(), Bucket() }),
            distance(dfc), multiplier(multiplier) {}

        bool wasAdded(const Node u) const { return was_added[u]; }

        void add(const Node u, bool is_tr) {
            assert(!most_balanced_cut_mode || !is_tr);
            assert(!wasAdded(u));
            was_added.set(u);
            const HopDistance d = getDistance(u);
            is_tr |= most_balanced_cut_mode; // reuse target_reachable_bucket_index buckets for nodes inserted during mbc
            const auto i = static_cast<Index>(is_tr);
            insertIntoBucket(u, i, d);
        }

        void insertIntoBucket(const Node u, const Index i, const HopDistance d) {
            buckets[d][i].push_back(u);
            max_occupied_bucket[i] = std::max(max_occupied_bucket[i], d);
            min_occupied_bucket[i] = std::min(min_occupied_bucket[i], d);
        }

        void reset(const size_t newN) {
            most_balanced_cut_mode = false;
            was_added.resize(newN);
            was_added.reset(0, newN);

            for (Index i = 0; i < 2; ++i) {
                clearBuckets(i);
                assert(removed_during_most_balanced_cut_mode[i].empty());
            }
            verifyBucketsAreClean();

            HopDistance maxDistance = 0;
            for (Node i(0); i < newN; ++i) {
                maxDistance = std::max(maxDistance, getDistance(i));
            }
            if (static_cast<size_t>(maxDistance) >= buckets.size()) {
                buckets.resize(static_cast<size_t>(maxDistance + 1));
            }
        }

        void resetForMostBalancedCut() {
            // remove everything that was added during most balanced cut and is still in the buckets
            for (HopDistance d = min_occupied_bucket[most_balanced_cut_bucket_index]; d <= max_occupied_bucket[most_balanced_cut_bucket_index]; ++d) {
                for (Node u : buckets[d][most_balanced_cut_bucket_index]) {
                    was_added.reset(u);
                }
                buckets[d][most_balanced_cut_bucket_index].clear();
            }

            // reinsert the non-target-reachable nodes that were removed during most balanced cut
            for (Node u : removed_during_most_balanced_cut_mode[not_reachable_bucket_index]) {
                buckets[getDistance(u)][not_reachable_bucket_index].push_back(u);
            }

            for (Node u : removed_during_most_balanced_cut_mode[most_balanced_cut_bucket_index]) {
                was_added.reset(u);
            }

            removed_during_most_balanced_cut_mode[not_reachable_bucket_index].clear();
            removed_during_most_balanced_cut_mode[most_balanced_cut_bucket_index].clear();

            max_occupied_bucket = backup_max_occupied_bucket;
            min_occupied_bucket = backup_min_occupied_bucket;
        }

        void clearBuckets(const Index i) {
            for (HopDistance d = min_occupied_bucket[i]; d <= max_occupied_bucket[i]; ++d) {
                buckets[d][i].clear();
            }
            min_occupied_bucket[i] = 0;
            max_occupied_bucket[i] = -1;
        }

        void enterMostBalancedCutMode() {
            most_balanced_cut_mode = true;
            clearBuckets(reachable_bucket_index);
            // TODO could also filter non_reachable_bucket for already reachable nodes
            backup_max_occupied_bucket = max_occupied_bucket;
            backup_min_occupied_bucket = min_occupied_bucket;
        }

        HopDistance getDistance(const Node u) const {
            return std::max(multiplier * distance[u], 0); // distances of vertices on opposite side are negative --> throw away
        }

        BitVector was_added;

        static constexpr Index not_reachable_bucket_index = 0, reachable_bucket_index = 1, most_balanced_cut_bucket_index = 1;
        std::vector<std::array<Bucket, 2>> buckets;

        std::array<HopDistance, 2> max_occupied_bucket, min_occupied_bucket, backup_max_occupied_bucket, backup_min_occupied_bucket;

        std::array<Bucket, 2> removed_during_most_balanced_cut_mode;

        const std::vector<HopDistance>& distance;

        int multiplier;
        bool most_balanced_cut_mode = false;

    private:
        void verifyBucketsAreClean() {
#ifndef NDEBUG
            for (auto& bb : buckets) {
                for (Bucket& b : bb) {
                    assert(b.empty());
                }
            }
#endif
        }
    };

    class NodeBorders {
    public:
        NodeBorders(const size_t initialN) : distance(initialN, 0), source_side(initialN, distance, -1), target_side(initialN, distance, 1) {}

        void reset(const size_t newN) {
            distance.resize(newN, 0); // resize here in case distances are not used. however, users have to resize themselves at construction time
            source_side.reset(newN);
            target_side.reset(newN);
        }

        void enterMostBalancedCutMode() {
            source_side.enterMostBalancedCutMode();
            target_side.enterMostBalancedCutMode();
        }

        void resetForMostBalancedCut() {
            source_side.resetForMostBalancedCut();
            target_side.resetForMostBalancedCut();
        }

        std::vector<HopDistance> distance;
        NodeBorder source_side, target_side;
    };

} // namespace whfc
