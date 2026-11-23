/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/concurrent_vector.h>
#include <tbb/enumerable_thread_specific.h>

#include "WHFC/algorithm/hyperflowcutter.h"
#include "WHFC/algorithm/parallel_push_relabel.h"

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/concurrent_flat_map.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"
#include "mt-kahypar/partition/refinement/flows/flow_hypergraph_builder.h"
#include "mt-kahypar/parallel/stl/zero_allocator.h"

namespace mt_kahypar {

struct FlowProblem;

template<typename GraphAndGainTypes>
class ParallelConstruction {

  static constexpr bool debug = false;

  static constexpr size_t NUM_CSR_BUCKETS = 1024;

  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using FlowNetworkConstruction = typename GraphAndGainTypes::FlowNetworkConstruction;

  struct TmpPin {
    HyperedgeID e;
    whfc::Node pin;
    PartitionID block;
  };

  // for non-deterministic construction
  struct TmpHyperedge {
    const size_t hash;
    const size_t bucket;
    const whfc::Hyperedge e;
  };

  class DynamicIdenticalNetDetection {

    struct ThresholdHyperedge {
      const TmpHyperedge e;
      const uint32_t threshold;
    };

    using IdenticalNetVector = tbb::concurrent_vector<
      ThresholdHyperedge, parallel::zero_allocator<ThresholdHyperedge>>;

    struct HashBucket {
      HashBucket() :
        identical_nets(),
        threshold(0) { }

      IdenticalNetVector identical_nets;
      uint32_t threshold;
    };

   public:
    explicit DynamicIdenticalNetDetection(const HyperedgeID num_hyperedges,
                                          FlowHypergraphBuilder& flow_hg,
                                          const Context& context) :
      _flow_hg(flow_hg),
      _hash_buckets(),
      _threshold(2) {
      _hash_buckets.resize(std::max(UL(1024), num_hyperedges /
        context.refinement.flows.num_parallel_searches));
    }

    TmpHyperedge get(const size_t he_hash,
                     const vec<whfc::Node>& pins);

    void add(const TmpHyperedge& tmp_he);

    void reset() {
      _threshold += 2;
    }

   private:
    FlowHypergraphBuilder& _flow_hg;
    vec<HashBucket> _hash_buckets;
    uint32_t _threshold;
  };

  // for deterministic construction
  struct TmpDeterministicHyperedge {
    size_t weight;
    vec<whfc::Node> pins;
  };

  struct HashedHyperedge {
    size_t he;
    size_t hash;
    size_t size;
  };

  struct TmpHyperedgeBuffer {
    void resize(const HyperedgeID num_hyperedges);

    vec<TmpDeterministicHyperedge> tmp_hyperedges;
    vec<uint8_t> valid_hyperedges;
  };

 public:
  explicit ParallelConstruction(const HyperedgeID num_hyperedges,
                                FlowHypergraphBuilder& flow_hg,
                                whfc::HyperFlowCutter<whfc::ParallelPushRelabel>& hfc,
                                const Context& context) :
    _context(context),
    _flow_hg(flow_hg),
    _hfc(hfc),
    _node_to_whfc(),
    _visited_hns(),
    _tmp_pins(),
    _cut_hes(),
    _pins(),
    _he_to_whfc(),
    _identical_nets(num_hyperedges, flow_hg, context),
    _tmp_hyperedge_buffer() {}

  ParallelConstruction(const ParallelConstruction&) = delete;
  ParallelConstruction(ParallelConstruction&&) = delete;
  ParallelConstruction & operator= (const ParallelConstruction &) = delete;
  ParallelConstruction & operator= (ParallelConstruction &&) = delete;

  virtual ~ParallelConstruction() = default;


  FlowProblem constructFlowHypergraph(const PartitionedHypergraph& phg,
                                      const Subhypergraph& sub_hg,
                                      const PartitionID block_0,
                                      const PartitionID block_1,
                                      vec<HypernodeID>& whfc_to_node,
                                      const bool deterministic);

  // ! Only for testing
  FlowProblem constructFlowHypergraphExplicit(const PartitionedHypergraph& phg,
                                              const Subhypergraph& sub_hg,
                                              const PartitionID block_0,
                                              const PartitionID block_1,
                                              vec<HypernodeID>& whfc_to_node,
                                              const bool default_construction,
                                              const bool deterministic);

 private:
  FlowProblem constructDefault(const PartitionedHypergraph& phg,
                               const Subhypergraph& sub_hg,
                               const PartitionID block_0,
                               const PartitionID block_1,
                               vec<HypernodeID>& whfc_to_node);

  FlowProblem constructDefaultDeterministic(const PartitionedHypergraph& phg,
                                            const Subhypergraph& sub_hg,
                                            const PartitionID block_0,
                                            const PartitionID block_1,
                                            vec<HypernodeID>& whfc_to_node);

  FlowProblem constructOptimizedForLargeHEs(const PartitionedHypergraph& phg,
                                            const Subhypergraph& sub_hg,
                                            const PartitionID block_0,
                                            const PartitionID block_1,
                                            vec<HypernodeID>& whfc_to_node);

  FlowProblem constructOptimizedForLargeHEsDeterministic(const PartitionedHypergraph& phg,
                                                         const Subhypergraph& sub_hg,
                                                         const PartitionID block_0,
                                                         const PartitionID block_1,
                                                         vec<HypernodeID>& whfc_to_node);

  void initializeWHFCNodes(const PartitionedHypergraph& phg,
                           const Subhypergraph& sub_hg,
                           const PartitionID block_0,
                           const PartitionID block_1,
                           FlowProblem& flow_problem,
                           vec<HypernodeID>& whfc_to_node,
                           bool collect_pins);

  bool checkIfHyperedgesAreParallel(const TmpDeterministicHyperedge& lhs,
                                    const TmpDeterministicHyperedge& rhs);

  void deduplicateParallelHyperedges(vec<HashedHyperedge>& bucket,
                                     vec<TmpDeterministicHyperedge>& tmp_hyperedges,
                                     vec<uint8_t>& valid_hyperedges);

  void determineDistanceFromCut(const PartitionedHypergraph& phg,
                                const whfc::Node source,
                                const whfc::Node sink,
                                const PartitionID block_0,
                                const PartitionID block_1,
                                const vec<HypernodeID>& whfc_to_node);

  const Context& _context;

  FlowHypergraphBuilder& _flow_hg;
  whfc::HyperFlowCutter<whfc::ParallelPushRelabel>& _hfc;

  ds::ConcurrentFlatMap<HypernodeID, whfc::Node> _node_to_whfc;
  ds::ThreadSafeFastResetFlagArray<> _visited_hns;
  tbb::enumerable_thread_specific<vec<whfc::Node>> _tmp_pins;
  tbb::concurrent_vector<TmpHyperedge> _cut_hes;

  ds::ConcurrentBucketMap<TmpPin> _pins;
  ds::ConcurrentFlatMap<HyperedgeID, HyperedgeID> _he_to_whfc;

  DynamicIdenticalNetDetection _identical_nets;

  TmpHyperedgeBuffer _tmp_hyperedge_buffer;
};
}  // namespace mt_kahypar
