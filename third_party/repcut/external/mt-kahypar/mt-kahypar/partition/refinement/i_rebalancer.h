/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#pragma once

#include <vector>

#include "include/mtkahypartypes.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"

namespace mt_kahypar {

class IRebalancer: public IRefiner {

 public:
  virtual ~IRebalancer() = default;

  bool refineAndOutputMoves(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                            const parallel::scalable_vector<HypernodeID>& refinement_nodes,
                            parallel::scalable_vector<parallel::scalable_vector<Move>>& moves_by_part,
                            Metrics& best_metrics,
                            const double time_limit) {
    return refineAndOutputMovesImpl(hypergraph, refinement_nodes, moves_by_part, best_metrics, time_limit);
  }

  bool refineAndOutputMovesLinear(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                  const parallel::scalable_vector<HypernodeID>& refinement_nodes,
                                  parallel::scalable_vector<Move>& moves,
                                  Metrics& best_metrics,
                                  const double time_limit) {
    return refineAndOutputMovesLinearImpl(hypergraph, refinement_nodes, moves, best_metrics, time_limit);
  }

 protected:
  IRebalancer() = default;

 private:
  virtual bool refineAndOutputMovesImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                        const parallel::scalable_vector<HypernodeID>& refinement_nodes,
                                        parallel::scalable_vector<parallel::scalable_vector<Move>>& moves_by_part,
                                        Metrics& best_metrics,
                                        const double time_limit) = 0;

  virtual bool refineAndOutputMovesLinearImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                              const parallel::scalable_vector<HypernodeID>& refinement_nodes,
                                              parallel::scalable_vector<Move>& moves,
                                              Metrics& best_metrics,
                                              const double time_limit) = 0;
};

}  // namespace mt_kahypar
