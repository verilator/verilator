#pragma once

#include "repcut_serial.h"

#include <atomic>

#include "push_relabel_commons.h"

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_reduce.h>
#include <tbb/tick_count.h>

#include "../util/sub_range.h"

#include "../datastructure/buffered_vector.h"

namespace whfc {

    class ParallelPushRelabel : public PushRelabelCommons {
    public:
        static constexpr bool log = false;
        static constexpr bool capacitate_incoming_edges_of_in_nodes = true;

        ParallelPushRelabel(FlowHypergraph& hg) : PushRelabelCommons(hg), next_active(0) {}

        bool findMinCuts() {
            if (!augmentFlow()) {
                return false;
            }
            auto t = tbb::tick_count::now();
            deriveSourceSideCut(true);
            auto t2 = tbb::tick_count::now();
            source_cut_time += (t2 - t).seconds();
            return true;
        }

        Flow computeMaxFlow(Node s, Node t) {
            reset();
            initialize(s, t);
            augmentFlow();
            return flow_value;
        }

        bool augmentFlow() {
            auto t = tbb::tick_count::now();
            saturateSourceEdges();
            auto t2 = tbb::tick_count::now();
            saturate_time += (t2 - t).seconds();
            size_t num_iterations_with_same_flow = 0;
            bool termination_check_triggered = false;
            do {
                while (!next_active.empty()) {
                    if (flow_value > upper_flow_bound || shall_terminate) {
                        return false;
                    }
                    num_active = next_active.size();
                    next_active.swap_container(active);

                        if (distance_labels_broken_from_target_side_piercing || work_since_last_global_relabel > global_relabel_work_threshold) {
                            globalRelabel<false>();
                        }

                        Flow old_flow_value = flow_value;

                        auto t3 = tbb::tick_count::now();
                        dischargeActiveNodes();
                        auto t4 = tbb::tick_count::now();
                        discharge_time += (t4 - t3).seconds();
                        applyUpdates();
                        auto t5 = tbb::tick_count::now();
                        update_time += (t5 - t4).seconds();


                        if (old_flow_value == flow_value && num_active < 1500 && next_active.size() < 1500) {
                            num_iterations_with_same_flow++;
                            if (num_iterations_with_same_flow > 500 && !termination_check_triggered) {
                                resetRound(); // delete active nodes and their markers --> trigger termination check global relabel
                                termination_check_triggered = true; // do this only once! if it didn't work the first time, terminate regularly
                            }
                        } else {
                            num_iterations_with_same_flow = 0;
                        }
                    }

                // no more nodes with level < n and excess > 0 left.
                // however labels might be broken from parallelism
                // --> run global relabeling to check if done.
                num_active = 0;
                globalRelabel<true>();	// setting the template parameter to true means the function sets reachability info, since we expect to be finished
                // plug queue back in (regular loop picks it out again)
                next_active.swap_container(active);
                next_active.set_size(num_active);
            } while (!next_active.empty());
            return true;
        }

        void dischargeActiveNodes() {
            resetRound();
            tbb::enumerable_thread_specific<size_t> work(0);
            auto task = [&](size_t i) {
                const Node u = active[i];
                assert(excess[u] > 0);
                if (level[u] >= max_level || isTarget(u)) {
                    return;
                } // target nodes can be pushed to consume updates
                if (isHypernode(u)) {
                    work.local() += dischargeHypernode(u);
                } else if (isOutNode(u)) {
                    work.local() += dischargeOutNode(u);
                } else {
                    work.local() += dischargeInNode(u);
                }
            };
            tbb::parallel_for<size_t>(0UL, num_active, task);
            next_active.finalize();
            work_since_last_global_relabel += work.combine(std::plus<>());
        }

        void applyUpdates() {
            tbb::parallel_for<size_t>(0UL, num_active, [&](size_t i) {
                const Node u = active[i];
                if (level[u] >= max_level) {
                    return;
                }
                if (!isTarget(u)) {
                    level[u] = next_level[u];
                } else {
                    repcut_serial::Ref<Flow>(flow_value).fetch_add(excess_diff[u], std::memory_order_relaxed);
                }
                excess[u] += excess_diff[u];
                excess_diff[u] = 0;
            });
            tbb::parallel_for<size_t>(0UL, next_active.size(), [&](size_t i) {
                const Node u = next_active[i];
                excess[u] += excess_diff[u];
                if (isTarget(u) && excess_diff[u] > 0) {
                    repcut_serial::Ref<Flow>(flow_value).fetch_add(excess_diff[u], std::memory_order_relaxed);
                }
                excess_diff[u] = 0;
            });
        }

        size_t dischargeHypernode(Node u) {
            auto next_active_handle = next_active.local_buffer();
            auto push = [&](Node v) {
                if (activate(v))
                    next_active_handle.push_back(v);
            };
            size_t work = 0;
            Flow my_excess = excess[u];
            int my_level = level[u];

            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level;
                bool skipped = false;

                // push to in-nodes of incident nets
                auto i = hg.beginIndexHyperedges(u);
                for (; my_excess > 0 && i < hg.endIndexHyperedges(u); ++i) {
                    Hyperedge e = hg.getInHe(i).e;
                    Node e_in = edgeToInNode(e);
                    Flow d = my_excess;
                    if constexpr (capacitate_incoming_edges_of_in_nodes) {
                        d = std::min(d, hg.capacity(e) - flow[inNodeIncidenceIndex(i)]);
                    }
                    if (my_level == level[e_in] + 1) {
                        if (excess[e_in] > 0 && !winEdge(u, e_in)) {
                            skipped = true;
                        } else if (d > 0) {
                            flow[inNodeIncidenceIndex(i)] += d;
                            my_excess -= d;
                            repcut_serial::Ref<Flow>(excess_diff[e_in]).fetch_add(d, std::memory_order_relaxed);
                            push(e_in);
                        }
                    } else if (my_level <= level[e_in] && d > 0) {
                        new_level = std::min(new_level, level[e_in]);
                    }
                }
                work += i - hg.beginIndexHyperedges(u);
                if (my_excess == 0)
                    break;

                // push back to out-nodes of incident nets
                for (i = hg.beginIndexHyperedges(u); my_excess > 0 && i < hg.endIndexHyperedges(u); ++i) {
                    Hyperedge e = hg.getInHe(i).e;
                    Node e_out = edgeToOutNode(e);
                    if (my_level == level[e_out] + 1) {
                        if (excess[e_out] > 0 && !winEdge(u, e_out)) {
                            skipped = true;
                        } else {
                            const Flow d = std::min(my_excess, flow[outNodeIncidenceIndex(i)]);
                            if (d > 0) {
                                assert(flow[outNodeIncidenceIndex(i)] <= hg.capacity(e));
                                flow[outNodeIncidenceIndex(i)] -= d;
                                my_excess -= d;
                                repcut_serial::Ref<Flow>(excess_diff[e_out]).fetch_add(d, std::memory_order_relaxed);
                                push(e_out);
                            }
                        }
                    } else if (my_level <= level[e_out] && flow[outNodeIncidenceIndex(i)] > 0) {
                        new_level = std::min(new_level, level[e_out]);
                    }
                }
                work += i - hg.beginIndexHyperedges(u);

                if (my_excess == 0 || skipped) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            next_level[u] = my_level; // make relabel visible
            if (my_excess > 0 && my_level < max_level) { // go again in the next round if excess left
                push(u);
            }
            // excess[u] serves as indicator for other nodes that u is active --> update later
            repcut_serial::Ref<Flow>(excess_diff[u]).fetch_sub((excess[u] - my_excess), std::memory_order_relaxed);
            return work;
        }

        size_t dischargeInNode(Node e_in) {
            auto next_active_handle = next_active.local_buffer();
            auto push = [&](Node v) {
                if (activate(v))
                    next_active_handle.push_back(v);
            };
            size_t work = 0;
            Flow my_excess = excess[e_in];
            int my_level = level[e_in];
            next_level[e_in] = my_level;
            Hyperedge e = inNodeToEdge(e_in);
            assert(e < hg.numHyperedges());
            Node e_out = edgeToOutNode(e);
            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level;
                bool skipped = false;

                // push through bridge edge
                if (my_level == level[e_out] + 1) {
                    if (excess[e_out] > 0 && !winEdge(e_in, e_out)) {
                        skipped = true;
                    } else {
                        const Flow d = std::min(hg.capacity(e) - flow[bridgeEdgeIndex(e)], my_excess);
                        if (d > 0) {
                            flow[bridgeEdgeIndex(e)] += d;
                            my_excess -= d;
                            repcut_serial::Ref<Flow>(excess_diff[e_out]).fetch_add(d, std::memory_order_relaxed);
                            push(e_out);
                        }
                    }
                    work++;
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
                    if (my_level == level[v] + 1) {
                        if (excess[v] > 0 && !winEdge(e_in, v)) {
                            skipped = true;
                        } else if (d > 0) {
                            d = std::min(d, my_excess);
                            flow[j] -= d;
                            my_excess -= d;
                            repcut_serial::Ref<Flow>(excess_diff[v]).fetch_add(d, std::memory_order_relaxed);
                            push(v);
                        }
                    } else if (d > 0 && my_level <= level[v]) {
                        new_level = std::min(new_level, level[v]);
                    }
                    work++;
                }

                if (my_excess == 0 || skipped) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            next_level[e_in] = my_level; // make relabel visible
            if (my_excess > 0 && my_level < max_level) { // go again in the next round if excess left
                push(e_in);
            }
            // excess[u] serves as indicator for other nodes that u is active --> update later
            repcut_serial::Ref<Flow>(excess_diff[e_in]).fetch_sub((excess[e_in] - my_excess), std::memory_order_relaxed);
            return work;
        }

        size_t dischargeOutNode(Node e_out) {
            auto next_active_handle = next_active.local_buffer();
            auto push = [&](Node v) {
                if (activate(v))
                    next_active_handle.push_back(v);
            };
            size_t work = 0;
            Flow my_excess = excess[e_out];
            int my_level = level[e_out];
            Hyperedge e = outNodeToEdge(e_out);
            assert(e < hg.numHyperedges());
            Node e_in = edgeToInNode(e);
            assert(my_excess <= hg.capacity(e));

            while (my_excess > 0 && my_level < max_level) {
                int new_level = max_level;
                bool skipped = false;

                // push out to pins
                for (const auto& p : hg.pinsOf(e)) {
                    if (my_excess == 0) {
                        break;
                    }
                    Node v = p.pin;
                    Flow d = my_excess;
                    if (my_level == level[v] + 1) {
                        // subtlety here. if target has excess updated (for tracking flow value) winEdge(e_out, v) has to be true if isTarget(v)
                        // otherwise there's an infinite loop. --> reverted winEdge condition to the original one
                        if (excess[v] > 0 && !winEdge(e_out, v)) {
                            skipped = true;
                        } else {
                            assert(d > 0 && d <= hg.capacity(e) - flow[outNodeIncidenceIndex(p.he_inc_iter)]);
                            flow[outNodeIncidenceIndex(p.he_inc_iter)] += d;
                            my_excess -= d;
                            repcut_serial::Ref<Flow>(excess_diff[v]).fetch_add(d, std::memory_order_relaxed);
                            push(v);
                        }
                    } else if (my_level <= level[v]) {
                        new_level = std::min(new_level, level[v]);
                    }
                    work++;
                }

                if (my_excess == 0) {
                    break;
                }

                // push back through bridge edge
                if (my_level == level[e_in] + 1) {
                    if (excess[e_in] > 0 && !winEdge(e_out, e_in)) {
                        skipped = true;
                    } else {
                        Flow d = std::min(flow[bridgeEdgeIndex(e)], my_excess);
                        if (d > 0) {
                            flow[bridgeEdgeIndex(e)] -= d;
                            my_excess -= d;
                            repcut_serial::Ref<Flow>(excess_diff[e_in]).fetch_add(d, std::memory_order_relaxed);
                            push(e_in);
                        }
                        work++;
                    }
                } else if (my_level <= level[e_in] && flow[bridgeEdgeIndex(e)] > 0) {
                    new_level = std::min(new_level, level[e_in]);
                }

                if (my_excess == 0 || skipped) {
                    break;
                }
                my_level = new_level + 1; // relabel
            }

            next_level[e_out] = my_level; // make relabel visible
            if (my_excess > 0 && my_level < max_level) { // go again in the next round if excess left
                push(e_out);
            }
            // excess[u] serves as indicator for other nodes that u is active --> update later
            repcut_serial::Ref<Flow>(excess_diff[e_out]).fetch_sub((excess[e_out] - my_excess), std::memory_order_relaxed);
            return work;
        }

        template<bool set_reachability>
        void globalRelabel() {
            auto t = tbb::tick_count::now();
            tbb::parallel_for<size_t>(
                    0, max_level, [&](size_t i) { level[i] = isTarget(Node(i)) ? 0 : max_level; }, tbb::static_partitioner());
            next_active.clear();
            for (const Node t : target_piercing_nodes) {
                next_active.push_back_atomic(t);
            }

            if (set_reachability) {
                resetReachability(false);
            }

            auto scan = [&](Node u, int dist) {
                auto next_layer = next_active.local_buffer();
                scanBackward(u, [&](const Node v) {
                    if (!isSource(v) && !isTarget(v) && level[v] == max_level &&
                        repcut_serial::Ref<int>(level[v]).exchange(dist, std::memory_order_acq_rel) == max_level) {
                        next_layer.push_back(v);
                    }
                });

                if (!isTarget(u) && excess[u] > 0 && last_activated[u] != round) { // add previously mis-labeled nodes to active queue, if not already contained
                    size_t pos = repcut_serial::Ref<size_t>(num_active).fetch_add(1, std::memory_order_relaxed);
                    active[pos] = u;
                }

                if constexpr (set_reachability) {
                    if (!isTarget(u)) {
                        reach[u] = target_reachable_stamp;
                    }
                }
            };

            parallelBFS(0, scan);

            if (set_reachability) {
                last_target_side_queue_entry = next_active.size();
            }
            work_since_last_global_relabel = 0;
            distance_labels_broken_from_target_side_piercing = false;
            auto t2 = tbb::tick_count::now();
            global_relabel_time += (t2 - t).seconds();
        }

        void deriveSourceSideCut(bool flow_changed) {
            // after global relabel with termination check its container is swapped out --> this function doesn't swap

            next_active.clear();
            if (flow_changed) {
                // if flow didnt change, we can reuse the old stamp (all source-reachable nodes were made sources)
                resetReachability(true);

                // calculate new excess nodes
                tbb::parallel_for<size_t>(0, max_level, [&](int i) {
                    Node u(i);
                    if (!isSource(u) && !isTarget(u) && excess[u] > 0) {
                        assert(level[u] == max_level);
                        next_active.push_back_buffered(u);
                        reach[u] = source_reachable_stamp;
                    }
                });
                next_active.finalize();
            }

            for (const Node& s : source_piercing_nodes) {
                next_active.push_back_atomic(s);
            }

            if (flow_changed) {
                auto scan = [&](Node u, int) {
                    auto next_layer = next_active.local_buffer();
                    scanForward(u, [&](const Node v) {
                        assert(!isTargetReachable(v));
                        if (!isSourceReachable(v) &&
                            repcut_serial::Ref<uint32_t>(reach[v]).exchange(source_reachable_stamp, std::memory_order_acq_rel) != source_reachable_stamp) {
                            assert(flow_changed || excess[v] == 0);
                            next_layer.push_back(v);
                        }
                    });
                };
                parallelBFS(0, scan);
            } else {
                // expect less work
                auto scan = [&](Node u, int) {
                    scanForward(u, [&](const Node v) {
                        assert(!isTargetReachable(v));
                        if (!isSourceReachable(v)) {
                            assert(flow_changed || excess[v] == 0);
                            reach[v] = source_reachable_stamp;
                            next_active.push_back_atomic(v);
                        }
                    });
                };
                sequentialBFS(0, scan);
            }

            last_source_side_queue_entry = next_active.size();
        }

        void deriveTargetSideCut() {
            next_active.swap_container(active); // don't overwrite contents of source side
            next_active.clear();

            resetReachability(false);
            for (const Node& t : target_piercing_nodes) {
                next_active.push_back_atomic(t);
            }

            /*
            auto scan = [&](Node u, int ) {
                auto next_layer = next_active.local_buffer();
                scanBackward(u, [&](const Node v) {
                    assert(!isSourceReachable(v));
                    if (!isTargetReachable(v) &&
                        repcut_serial::Ref<uint32_t>(reach[v]).exchange(target_reachable_stamp, std::memory_order_acq_rel) != target_reachable_stamp) {
                        assert(excess[v] == 0);
                        next_layer.push_back(v);
                    }
                });
            };
            parallelBFS(0, scan);
            */

            auto scan = [&](Node u, int) {
                scanBackward(u, [&](const Node v) {
                    if (!isTargetReachable(v)) {
                        reach[v] = target_reachable_stamp;
                        next_active.push_back_atomic(v);
                    }
                });
            };
            sequentialBFS(0, scan);


            last_target_side_queue_entry = next_active.size();
            next_active.swap_container(active); // go back
        }

        template<typename ScanFunc>
        void parallelBFS(size_t first, ScanFunc&& scan) {
            size_t last = next_active.size();
            int dist = 1;
            while (first != last) {
                tbb::parallel_for<size_t>(first, last, [&](size_t i) { scan(next_active[i], dist); });
                next_active.finalize();
                first = last;
                last = next_active.size();
                dist++;
            }
        }

        template<typename ScanFunc>
        void sequentialBFS(size_t first, ScanFunc&& scan) {
            size_t last = next_active.size();
            int dist = 1;
            while (first != last) {
                for (; first < last; ++first) {
                    scan(next_active[first], dist);
                }
                last = next_active.size();
                dist++;
            }
        }

        sub_range<vec<Node>> sourceReachableNodes() const { return sub_range<vec<Node>>(next_active.getData(), 0, last_source_side_queue_entry); }

        sub_range<vec<Node>> targetReachableNodes() const { return sub_range<vec<Node>>(active, 0, last_target_side_queue_entry); }

        void saturateSourceEdges() {
            /*
             * if no new active nodes are pushed, we proceed straight to the termination checking global relabeling,
             * which then inserts the mis-labeled excess nodes, and then proceeds to the regular main loop
             */
            resetRound();
            if (source_piercing_nodes_not_exhausted) {
                for (const Node source : source_piercing_nodes) {
                    for (InHeIndex inc_iter : hg.incidentHyperedgeIndices(source)) {
                        const Hyperedge e = hg.getInHe(inc_iter).e;
                        Node e_in = edgeToInNode(e), e_out = edgeToOutNode(e);
                        if (!isSource(e_in)) {
                            Flow d = hg.capacity(e) - flow[inNodeIncidenceIndex(inc_iter)];
                            if (d > 0) {
                                excess[source] -= d;
                                excess[e_in] += d;
                                flow[inNodeIncidenceIndex(inc_iter)] += d;
                                if (activate(e_in)) { // necessary, otherwise global relabel may add them as well --> duplicates
                                    next_active.push_back_atomic(e_in);
                                }
                            }
                            assert(flow[inNodeIncidenceIndex(inc_iter)] == hg.capacity(e));
                        }
                        if (!isSource(e_out)) {
                            Flow d = flow[outNodeIncidenceIndex(inc_iter)];
                            if (d > 0) {
                                excess[source] -= d;
                                excess[e_out] += d;
                                flow[outNodeIncidenceIndex(inc_iter)] -= d;
                                if (activate(e_out)) {
                                    next_active.push_back_atomic(e_out);
                                }
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

            excess_diff.assign(max_level, 0);
            next_level.assign(max_level, 0);

            next_active.clear();
            next_active.adapt_capacity(max_level);
            active.resize(max_level);
            last_activated.assign(max_level, 0);
            round = 0;

            last_source_side_queue_entry = 0;
            last_target_side_queue_entry = 0;
        }

    private:
        vec<Flow> excess_diff;
        vec<int> next_level;
        size_t num_active = 0;
        BufferedVector<Node> next_active;
        vec<Node> active;

        vec<uint32_t> last_activated;
        uint32_t round = 0;
        bool activate(Node u) {
            return last_activated[u] != round && repcut_serial::Ref<uint32_t>(last_activated[u]).exchange(round, std::memory_order_acq_rel) != round;
        }
        void resetRound() {
            if (++round == 0) {
                last_activated.assign(max_level, 0);
                ++round;
            }
            next_active.clear();
        }

        size_t last_source_side_queue_entry = 0, last_target_side_queue_entry = 0;
    };

} // namespace whfc
