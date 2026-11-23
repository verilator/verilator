/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/partition/initial_partitioning/i_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_data_container.h"

namespace mt_kahypar {

namespace {
  struct MaxGainMove {
    const PartitionID block;
    const Gain gain;
  };
}

template<typename TypeTraits>
class LabelPropagationInitialPartitioner : public IInitialPartitioner {

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using DeltaFunction = std::function<void (const SynchronizedEdgeUpdate&)>;
  #define NOOP_FUNC [] (const SynchronizedEdgeUpdate&) { }

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

 public:
  LabelPropagationInitialPartitioner(const InitialPartitioningAlgorithm,
                                     ip_data_container_t* ip_data,
                                     const Context& context,
                                     const int seed, const int tag) :
    _ip_data(ip::to_reference<TypeTraits>(ip_data)),
    _context(context),
    _valid_blocks(context.partition.k),
    _tmp_scores(context.partition.k),
    _rng(seed),
    _tag(tag) { }

 private:
  void partitionImpl() final;

  bool fitsIntoBlock(PartitionedHypergraph& hypergraph,
                     const HypernodeID hn,
                     const PartitionID block) const {
    ASSERT(block != kInvalidPartition && block < _context.partition.k);
    return hypergraph.partWeight(block) + hypergraph.nodeWeight(hn) <=
      _context.partition.perfect_balance_part_weights[block] *
      std::min(1.005, 1 + _context.partition.epsilon);
  }

  MaxGainMove computeMaxGainMove(PartitionedHypergraph& hypergraph,
                                 const HypernodeID hn) {
    if ( hypergraph.partID(hn) == kInvalidPartition ) {
      return computeMaxGainMoveForUnassignedVertex(hypergraph, hn);
    } else {
      return computeMaxGainMoveForAssignedVertex(hypergraph, hn);
    }
  }

  MaxGainMove computeMaxGainMoveForUnassignedVertex(PartitionedHypergraph& hypergraph,
                                                    const HypernodeID hn);

  MaxGainMove computeMaxGainMoveForAssignedVertex(PartitionedHypergraph& hypergraph,
                                                  const HypernodeID hn);

  MaxGainMove findMaxGainMove(PartitionedHypergraph& hypergraph,
                              const HypernodeID hn,
                              const HyperedgeWeight internal_weight);

  void extendBlockToInitialBlockSize(PartitionedHypergraph& hypergraph,
                                     const vec<HypernodeID>& seed_vertices,
                                     const PartitionID block);

  void assignVertexToBlockWithMinimumWeight(PartitionedHypergraph& hypergraph,
                                            const HypernodeID hn);

  InitialPartitioningDataContainer<TypeTraits>& _ip_data;
  const Context& _context;
  kahypar::ds::FastResetFlagArray<> _valid_blocks;
  parallel::scalable_vector<Gain> _tmp_scores;
  std::mt19937 _rng;
  const int _tag;
};


} // namespace mt_kahypar
