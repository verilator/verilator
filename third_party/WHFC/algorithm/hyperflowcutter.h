#pragma once

#include <tbb/tick_count.h>
#include "../datastructure/flow_hypergraph.h"
#include "cutter_state.h"
#include "piercing.h"

namespace whfc {

    template<class FlowAlgorithm>
    class HyperFlowCutter {
    public:
        TimeReporter timer;
        FlowHypergraph& hg;
        CutterState<FlowAlgorithm> cs;
        Piercer<FlowAlgorithm> piercer;
        bool find_most_balanced = true;
        double pierce_time = 0.0, assimilate_time = 0.0;

        static constexpr bool log = false;

        HyperFlowCutter(FlowHypergraph& hg, int seed, bool deterministic = false) : timer("HyperFlowCutter"), hg(hg), cs(hg, timer), piercer(hg, cs) {
            piercer.deterministic = deterministic;
            cs.rng.setSeed(seed);
            reset();
        }

        void reset() {
            cs.reset();
            piercer.reset();
            // timer.clear();
        }

        bool pierce() {
            auto t = tbb::tick_count::now();
            // DO NOT CHANGE THE ORDER OF THESE!
            const bool reject_if_aug = cs.rejectPiercingIfAugmenting();
            bool res = piercer.findPiercingNode(reject_if_aug) && (!reject_if_aug || !cs.augmenting_path_available_from_piercing);
            pierce_time += (tbb::tick_count::now() - t).seconds();
            return res;
        }


        bool findNextCut() {
            if (cs.has_cut && !pierce()) {
                return false;
            }

            if (cs.augmenting_path_available_from_piercing) {
                cs.has_cut = cs.flow_algo.findMinCuts();
            } else {
                auto t = tbb::tick_count::now();
                if (cs.side_to_pierce == 0) {
                    cs.flow_algo.deriveSourceSideCut(false); // no flow changed --> no new excesses created
                } else {
                    cs.flow_algo.deriveTargetSideCut();
                }
                cs.flow_algo.source_cut_time += (tbb::tick_count::now() - t).seconds();
                cs.has_cut = true; // no flow increased
            }

            if (cs.has_cut) {
                auto t = tbb::tick_count::now();
                cs.assimilate();
                assimilate_time += (tbb::tick_count::now() - t).seconds();
            }

            return cs.has_cut && cs.flow_algo.flow_value <= cs.flow_algo.upper_flow_bound;
        }


        /*
         * Equivalent to runUntilBalancedOrFlowBoundExceeded(s,t) except that it does not use the flow-based interleaving that is necessary when running
         * multiple HFC instances
         */
        template<typename CutReporter>
        bool enumerateCutsUntilBalancedOrFlowBoundExceeded(const Node s, const Node t, CutReporter&& on_cut) {
            cs.initialize(s, t);
            piercer.initialize();
            bool has_balanced_cut_below_flow_bound = false;
            while (!has_balanced_cut_below_flow_bound && findNextCut() && on_cut()) {
                has_balanced_cut_below_flow_bound |= cs.isBalanced();
            }

            if (has_balanced_cut_below_flow_bound) {
                if (find_most_balanced && !cs.addingAllUnreachableNodesDoesNotChangeHeavierBlock()) {
                    mostBalancedCut();
                } else {
                    cs.writePartition();
                }
                LOGGER << cs.toString();
            }

            return has_balanced_cut_below_flow_bound;
        }

        bool enumerateCutsUntilBalancedOrFlowBoundExceeded(const Node s, const Node t) {
            return enumerateCutsUntilBalancedOrFlowBoundExceeded(s, t, [] { return true; });
        }

        void mostBalancedCut() {
            timer.start("MBMC");
            LOGGER << "MBC Mode";
            // assimilate the missing side, so we don't have to track it in the moves
            if (cs.side_to_pierce == 0) {
                cs.assimilateTargetSide();
            } else {
                cs.assimilateSourceSide();
            }
            assert(cs.source_reachable_weight == cs.source_weight);
            assert(cs.target_reachable_weight == cs.target_weight);

            NonDynamicCutterState first_balanced_state = cs.enterMostBalancedCutMode();
            SimulatedNodeAssignment initial_sol = cs.mostBalancedAssignment();
            std::vector<Move> best_moves;
            SimulatedNodeAssignment best_sol = initial_sol;

            const size_t mbc_iterations = 7;
            for (size_t i = 0; i < mbc_iterations && !best_sol.isPerfectlyBalanced(); ++i) {
                LOGGER << "MBC it" << i;
                SimulatedNodeAssignment sol = best_sol;
                while (!sol.isPerfectlyBalanced() && pierce()) { // piercer says no cut
                    if (cs.side_to_pierce == 0) {
                        cs.flow_algo.deriveSourceSideCut(false);
                        cs.computeSourceReachableWeight();
                        cs.assimilateSourceSide();
                    } else {
                        cs.flow_algo.deriveTargetSideCut();
                        cs.computeTargetReachableWeight();
                        cs.assimilateTargetSide();
                    }
                    cs.side_to_pierce = cs.sideToGrow();
                    cs.has_cut = true; // piercer reset the flag, but we didn't change flow
                    LOGGER << cs.toString() << V(cs.side_to_pierce);
                    cs.verifyCutPostConditions();

                    SimulatedNodeAssignment sim = cs.mostBalancedAssignment();
                    if (sim.balance() > sol.balance()) {
                        sol = sim;
                    }
                }

                if (sol.balance() > best_sol.balance()) {
                    best_sol = sol;
                    cs.revertMoves(sol.number_of_tracked_moves);
                    best_moves = cs.tracked_moves;
                }
                cs.resetToFirstBalancedState(first_balanced_state);
                cs.has_cut = true;
            }

            cs.applyMoves(best_moves);
            cs.writePartition(best_sol);

            timer.stop("MBMC");
        }

        void signalTermination() { cs.flow_algo.shall_terminate = true; }

        void setFlowBound(Flow bound) { cs.flow_algo.upper_flow_bound = bound; }

        void setBulkPiercing(bool use) { piercer.setBulkPiercing(use); }

        void forceSequential(bool force) { cs.force_sequential = force; }

        void setSeed(int seed) { cs.rng.setSeed(seed); }
    };

} // namespace whfc
