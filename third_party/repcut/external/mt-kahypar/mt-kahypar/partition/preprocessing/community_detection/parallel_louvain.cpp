/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 ******************************************************************************/


#include "parallel_louvain.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/utils/utilities.h"

namespace mt_kahypar::community_detection {

  ds::Clustering local_moving_contract_recurse(Graph& fine_graph,
                                               ParallelLocalMovingModularity& mlv,
                                               const Context& context) {
    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.start_timer("local_moving", "Local Moving");
    ds::Clustering communities(fine_graph.numNodes());
    bool communities_changed = mlv.localMoving(fine_graph, communities);
    timer.stop_timer("local_moving");

    if (communities_changed) {
      timer.start_timer("contraction_cd", "Contraction");
      // Contract Communities
      Graph coarse_graph = fine_graph.contract(communities, context.preprocessing.community_detection.low_memory_contraction);
      ASSERT(coarse_graph.totalVolume() == fine_graph.totalVolume());
      timer.stop_timer("contraction_cd");

      // Recurse on contracted graph
      ds::Clustering coarse_communities = local_moving_contract_recurse(coarse_graph, mlv, context);

      timer.start_timer("project", "Project");
      // Prolong Clustering
      tbb::parallel_for(UL(0), fine_graph.numNodes(), [&](const NodeID u) {
        ASSERT(communities[u] < static_cast<PartitionID>(coarse_communities.size()));
        communities[u] = coarse_communities[communities[u]];
      });
      timer.stop_timer("project");
    }

    return communities;
  }

  ds::Clustering run_parallel_louvain(Graph& graph,
                                      const Context& context,
                                      bool disable_randomization) {
    ParallelLocalMovingModularity mlv(context, graph.numNodes(), disable_randomization);
    ds::Clustering communities = local_moving_contract_recurse(graph, mlv, context);
    return communities;
  }

}
