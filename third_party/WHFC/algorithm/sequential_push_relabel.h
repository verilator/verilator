#pragma once

#include <queue>
#include <vector>

#include "../datastructure/buffered_vector.h"
#include "../datastructure/flow_hypergraph.h"
#include "push_relabel_commons.h"


namespace whfc {

    template<typename T>
    using vec = std::vector<T, tbb::scalable_allocator<T>>;

    class SequentialPushRelabel : public PushRelabelCommons {
    public:
        using Type = SequentialPushRelabel;
        static constexpr bool log = false;
        static constexpr bool capacitate_incoming_edges_of_in_nodes = true;

        explicit SequentialPushRelabel(FlowHypergraph& hg) : PushRelabelCommons(hg) {}


        bool findMinCuts() {
            saturateSourceEdges();
            globalRelabel(); // previous excess nodes have been relabeled to max_level and there is no back-up check to reinsert them
            while (!active.empty()) {
                if (flow_value > upper_flow_bound || shall_terminate) {
                    return false;
                }
                if (work_since_last_global_relabel > global_relabel_work_threshold) {
                    globalRelabel();
                }
                const Node u = active.front();
                active.pop();
                if (excess[u] == 0 || level[u] >= max_level) {
                    continue;
                }
                if (isHypernode(u)) {
                    work_since_last_global_relabel += dischargeHypernode(u);
                } else if (isOutNode(u)) {
                    work_since_last_global_relabel += dischargeOutNode(u);
                } else {
                    work_since_last_global_relabel += dischargeInNode(u);
                }
            }
            LOGGER << V(flow_value);

            deriveSourceSideCut(true);
            deriveTargetSideCut();
            return true;
        }

        size_t dischargeHypernode(Node u) {
            size_t work = 0;
            Flow my_excess = excess[u];
            int my_level = level[u];

            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level - 1;      // to make the assertion checks for the level of unreachable excess nodes work

                auto i = hg.beginIndexHyperedges(u);
                // push to in-nodes of incident nets
                for (; my_excess > 0 && i < hg.endIndexHyperedges(u); ++i) {
                    Hyperedge e = hg.getInHe(i).e;
                    Node e_in = edgeToInNode(e);
                    Flow d = my_excess;
                    if constexpr (capacitate_incoming_edges_of_in_nodes) {
                        // (u, e_in) has infinite capacity but it never makes sense to push more flow into e_in than can be sent on (e_in, e_out)
                        d = std::min(d, hg.capacity(e) - flow[inNodeIncidenceIndex(i)]);
                    }
                    if (my_level == level[e_in] + 1) {
                        if (d > 0) {
                            flow[inNodeIncidenceIndex(i)] += d;
                            my_excess -= d;
                            if (isTarget(e_in)) {
                                flow_value += d;
                            } else if (excess[e_in] == 0) {
                                active.push(e_in);
                            }
                            excess[e_in] += d;
                        }
                    } else if (my_level <= level[e_in] && d > 0) {
                        new_level = std::min(new_level, level[e_in]);
                    }
                }
                work += i - hg.beginIndexHyperedges(u);

                if (my_excess == 0) {
                    break;
                }

                // push back to out-nodes of incident nets
                for (i = hg.beginIndexHyperedges(u); my_excess > 0 && i < hg.endIndexHyperedges(u); ++i) {
                    Hyperedge e = hg.getInHe(i).e;
                    Node e_out = edgeToOutNode(e);
                    if (my_level == level[e_out] + 1) {
                        assert(flow[outNodeIncidenceIndex(i)] <= hg.capacity(e));
                        const Flow d = std::min(my_excess, flow[outNodeIncidenceIndex(i)]);
                        if (d > 0) {
                            flow[outNodeIncidenceIndex(i)] -= d;
                            my_excess -= d;
                            if (isTarget(e_out)) {
                                flow_value += d;
                            } else if (excess[e_out] == 0) {
                                active.push(e_out);
                            }
                            excess[e_out] += d;
                        }
                    } else if (my_level <= level[e_out] && flow[outNodeIncidenceIndex(i)] > 0) {
                        new_level = std::min(new_level, level[e_out]);
                    }
                }
                work += i - hg.beginIndexHyperedges(u);

                if (my_excess == 0) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            level[u] = my_level; // make relabel visible
            if (my_level < max_level && my_excess > 0) { // go again in the next round if excess left
                active.push(u);
            }
            excess[u] = my_excess;

            return work;
        }

        size_t dischargeInNode(Node e_in) {
            size_t work = 0;
            Flow my_excess = excess[e_in];
            int my_level = level[e_in];
            Hyperedge e = inNodeToEdge(e_in);
            assert(e < hg.numHyperedges());
            Node e_out = edgeToOutNode(e);

            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level - 1;

                // push through bridge edge
                if (my_level == level[e_out] + 1) {
                    Flow d = std::min(hg.capacity(e) - flow[bridgeEdgeIndex(e)], my_excess);
                    if (d > 0) {
                        flow[bridgeEdgeIndex(e)] += d;
                        my_excess -= d;
                        if (isTarget(e_out)) {
                            flow_value += d;
                        } else if (excess[e_out] == 0) {
                            active.push(e_out);
                        }
                        excess[e_out] += d;
                    }
                } else if (my_level <= level[e_out] && flow[bridgeEdgeIndex(e)] < hg.capacity(e)) {
                    new_level = std::min(new_level, level[e_out]);
                }

                // push back to pins
                for (const auto& p : hg.pinsOf(e)) {
                    if (my_excess == 0) {
                        break;
                    }
                    Node v = p.pin;
                    size_t j = inNodeIncidenceIndex(p.he_inc_iter);
                    Flow d = flow[j];
                    if constexpr (capacitate_incoming_edges_of_in_nodes) {
                        assert(d <= hg.capacity(e));
                    }
                    if (my_level == level[v] + 1) {
                        if (d > 0) {
                            d = std::min(d, my_excess);
                            flow[j] -= d;
                            my_excess -= d;
                            if (isTarget(v)) {
                                flow_value += d;
                            } else if (excess[v] == 0) {
                                active.push(v);
                            }
                            excess[v] += d;
                        }
                    } else if (my_level <= level[v] && d > 0) {
                        new_level = std::min(new_level, level[v]);
                    }
                }
                work += hg.pinCount(e) + 6;

                if (my_excess == 0) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            level[e_in] = my_level; // make relabel visible
            if (my_level < max_level && my_excess > 0) { // go again in the next round if excess left
                active.push(e_in);
            }
            excess[e_in] = my_excess;
            return work;
        }

        size_t dischargeOutNode(Node e_out) {
            size_t work = 0;
            Flow my_excess = excess[e_out];
            int my_level = level[e_out];
            Hyperedge e = outNodeToEdge(e_out);
            assert(e < hg.numHyperedges());
            Node e_in = edgeToInNode(e);
            assert(my_excess <= hg.capacity(e));

            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level - 1;

                // push out to pins
                for (const auto& p : hg.pinsOf(e)) {
                    if (my_excess == 0) {
                        break;
                    }
                    Node v = p.pin;
                    Flow d = my_excess;
                    if (my_level == level[v] + 1) {
                        assert(d <= hg.capacity(e) - flow[outNodeIncidenceIndex(p.he_inc_iter)]);
                        flow[outNodeIncidenceIndex(p.he_inc_iter)] += d;
                        my_excess -= d;
                        if (isTarget(v)) {
                            flow_value += d;
                        } else if (excess[v] == 0) {
                            active.push(v);
                        }
                        excess[v] += d;
                    } else if (my_level <= level[v] && d > 0) {
                        new_level = std::min(new_level, level[v]);
                    }
                }
                work += hg.pinCount(e) + 6;

                if (my_excess == 0) {
                    break;
                }

                // push back through bridge edge
                if (my_level == level[e_in] + 1) {
                    Flow d = std::min(flow[bridgeEdgeIndex(e)], my_excess);
                    if (d > 0) {
                        flow[bridgeEdgeIndex(e)] -= d;
                        my_excess -= d;
                        if (isTarget(e_in)) {
                            flow_value += d;
                        } else if (excess[e_in] == 0) {
                            active.push(e_in);
                        }
                        excess[e_in] += d;
                    }
                } else if (my_level <= level[e_in] && flow[bridgeEdgeIndex(e)] > 0) {
                    new_level = std::min(new_level, level[e_in]);
                }

                if (my_excess == 0) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            level[e_out] = my_level; // make relabel visible
            if (my_level < max_level && my_excess > 0) { // go again in the next round if excess left
                active.push(e_out);
            }
            excess[e_out] = my_excess;
            return work;
        }

        void globalRelabel() {
            for (int i = 0; i < max_level; ++i) {
                level[i] = isTarget(Node(i)) ? 0 : max_level;
            }
            relabel_queue.clear();
            for (const Node t : target_piercing_nodes) {
                relabel_queue.push_back(t);
            }
            auto scan = [&](Node u, int dist) {
                scanBackward(u, [&](const Node v) {
                    if (!isSource(v) && !isTarget(v) && level[v] == max_level) {
                        relabel_queue.push_back(v);
                        level[v] = dist;
                    }
                });
            };
            sequentialBFS(relabel_queue, scan);
            work_since_last_global_relabel = 0;
            distance_labels_broken_from_target_side_piercing = false;
        }

        void deriveSourceSideCut(bool flow_changed) {
            source_reachable_nodes.clear();
            if (flow_changed) {
                resetReachability(true); // if flow didn't change, we can reuse the old stamp
                for (int i = 0; i < max_level; ++i) { // collect excess nodes
                    Node u(i);
                    if (!isSource(u) && !isTarget(u) && excess[u] > 0) {
                        assert(level[u] == max_level);
                        source_reachable_nodes.push_back(u);
                        reach[u] = source_reachable_stamp;
                    }
                }
                LOGGER << V(source_reachable_nodes.size()) << "excess nodes";
            }
            for (const Node s : source_piercing_nodes) {
                source_reachable_nodes.push_back(s);
            }

            auto scan = [&](Node u, int) {
                scanForward(u, [&](const Node v) {
                    assert(flow_changed || !isTargetReachable(v));
                    assert(!isTarget(v));
                    if (!isSourceReachable(v)) {
                        assert(flow_changed || excess[v] == 0);
                        reach[v] = source_reachable_stamp;
                        source_reachable_nodes.push_back(v);
                    }
                });
            };
            sequentialBFS(source_reachable_nodes, scan);
        }

        void deriveTargetSideCut() {
            relabel_queue.clear();
            resetReachability(false);
            for (const Node t : target_piercing_nodes) {
                relabel_queue.push_back(t);
            }
            auto scan = [&](Node u, int) {
                scanBackward(u, [&](const Node v) {
                    assert(!isSourceReachable(v));
                    if (!isTargetReachable(v)) {
                        assert(excess[v] == 0);
                        reach[v] = target_reachable_stamp;
                        relabel_queue.push_back(v);
                    }
                });
            };
            sequentialBFS(relabel_queue, scan);
        }

        template<typename ScanFunc>
        void sequentialBFS(vec<Node>& queue, ScanFunc&& scan) {
            size_t first = 0;
            size_t last = queue.size();
            int dist = 1;
            while (first != last) {
                for (; first < last; ++first) {
                    scan(queue[first], dist);
                }
                last = queue.size();
                dist++;
            }
        }

        const vec<Node>& sourceReachableNodes() const { return source_reachable_nodes; }
        const vec<Node>& targetReachableNodes() const { return relabel_queue; }


        void saturateSourceEdges() {
            while (!active.empty()) {
                active.pop();
            }

            for (Node u : source_reachable_nodes) {
                if (excess[u] <= 0 || isSource(u)) { // all excess nodes are at the beginning
                    break;
                }
                assert(level[u] == max_level || isTarget(u)); // can have target piercing nodes in there...
                if (!isTarget(u)) {
                    active.push(u);
                }
            }

#ifndef NDEBUG
            size_t num_excesses = 0;
            for (int i = 0; i < max_level; ++i) {
                num_excesses += static_cast<size_t>(excess[i] > 0 && !isTarget(Node(i)) && !isSource(Node(i)));
            }
            assert(active.size() == num_excesses);
#endif

            if (source_piercing_nodes_not_exhausted) {
                for (const Node source : source_piercing_nodes) {
                    for (InHeIndex inc_iter : hg.incidentHyperedgeIndices(source)) {
                        const Hyperedge e = hg.getInHe(inc_iter).e;
                        Node e_in = edgeToInNode(e), e_out = edgeToOutNode(e);
                        if (!isSource(e_in)) {
                            Flow d = hg.capacity(e) - flow[inNodeIncidenceIndex(inc_iter)];
                            if (d > 0) {
                                excess[source] -= d;
                                if (excess[e_in] == 0) {
                                    active.push(e_in);
                                }
                                excess[e_in] += d;
                                flow[inNodeIncidenceIndex(inc_iter)] += d;
                            }
                            assert(flow[inNodeIncidenceIndex(inc_iter)] == hg.capacity(e));
                        }
                        if (!isSource(e_out)) {
                            Flow d = flow[outNodeIncidenceIndex(inc_iter)];
                            if (d > 0) {
                                excess[source] -= d;
                                if (excess[e_out] == 0) {
                                    active.push(e_out);
                                }
                                excess[e_out] += d;
                                flow[outNodeIncidenceIndex(inc_iter)] -= d;
                            }
                        }
                    }
                }
                source_piercing_nodes_not_exhausted = false;
            }
#ifndef NDEBUG
            for (Node source : source_piercing_nodes) {
                for (InHeIndex inc_iter : hg.incidentHyperedgeIndices(source)) {
                    const Hyperedge e = hg.getInHe(inc_iter).e;
                    // should still be saturated because no flow was pushed back to source
                    assert(flow[inNodeIncidenceIndex(inc_iter)] == hg.capacity(e) || isSource(edgeToInNode(e)));
                }
            }
#endif
        }

        void reset() {
            PushRelabelCommons::reset();
            relabel_queue.reserve(max_level);

            while (!active.empty()) {
                active.pop();
            }
            relabel_queue.clear();
            source_reachable_nodes.clear();
        }

    private:
        std::queue<Node> active;
        vec<Node> relabel_queue, source_reachable_nodes;
    };

} // namespace whfc
