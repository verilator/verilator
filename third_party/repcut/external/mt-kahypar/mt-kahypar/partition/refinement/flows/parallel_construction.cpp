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

#include "repcut_serial.h"

#include "mt-kahypar/partition/refinement/flows/parallel_construction.h"

#include "kahypar-resources/utils/math.h"

#include <atomic>

#include <tbb/concurrent_queue.h>

#include "mt-kahypar/datastructures/flow_network_edge_parameters.h"
#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/datastructures/concurrent_bucket_map.h"


namespace mt_kahypar {

template<typename GraphAndGainTypes>
void ParallelConstruction<GraphAndGainTypes>::TmpHyperedgeBuffer::resize(const HyperedgeID num_hyperedges) {
  tbb::parallel_invoke([&] {
    tmp_hyperedges.resize(num_hyperedges);
  }, [&] {
    valid_hyperedges.resize(num_hyperedges, 0);
  });
}

template<typename GraphAndGainTypes>
typename ParallelConstruction<GraphAndGainTypes>::TmpHyperedge
ParallelConstruction<GraphAndGainTypes>::DynamicIdenticalNetDetection::get(const size_t he_hash,
                                                                        const vec<whfc::Node>& pins) {
  const size_t bucket_idx = he_hash % _hash_buckets.size();
  if ( repcut_serial::Ref(_hash_buckets[bucket_idx].threshold).load(std::memory_order_relaxed) == _threshold ) {
    // There exists already some hyperedges with the same hash
    for ( const ThresholdHyperedge& tmp : _hash_buckets[bucket_idx].identical_nets ) {
      // Check if there is some hyperedge equal to he
      const TmpHyperedge& tmp_e = tmp.e;
      if ( tmp.threshold == _threshold && tmp_e.hash == he_hash &&
           _flow_hg.tmpPinCount(tmp_e.bucket, tmp_e.e) == pins.size() ) {
        bool is_identical = true;
        size_t idx = 0;
        for ( const whfc::FlowHypergraph::Pin& u : _flow_hg.tmpPinsOf(tmp_e.bucket, tmp_e.e) ) {
          if ( u.pin != pins[idx++] ) {
            is_identical = false;
            break;
          }
        }
        if ( is_identical ) {
          return tmp_e;
        }
      }
    }
  }
  return TmpHyperedge { 0, std::numeric_limits<size_t>::max(), whfc::invalidHyperedge };
}

template<typename GraphAndGainTypes>
void ParallelConstruction<GraphAndGainTypes>::DynamicIdenticalNetDetection::add(const TmpHyperedge& tmp_he) {
  const size_t bucket_idx = tmp_he.hash % _hash_buckets.size();
  uint32_t expected = repcut_serial::Ref(_hash_buckets[bucket_idx].threshold)
                          .load(std::memory_order_relaxed);
  uint32_t desired = _threshold - 1;
  while ( repcut_serial::Ref(_hash_buckets[bucket_idx].threshold )
               .load(std::memory_order_relaxed) < _threshold ) {
    if ( expected < desired &&
        repcut_serial::Ref(_hash_buckets[bucket_idx].threshold)
             .compare_exchange_strong(expected, desired,
                                      std::memory_order_acq_rel,
                                      std::memory_order_relaxed) ) {
      _hash_buckets[bucket_idx].identical_nets.clear();
      repcut_serial::Ref(_hash_buckets[bucket_idx].threshold)
          .store(_threshold, std::memory_order_relaxed);
    }
  }
  _hash_buckets[bucket_idx].identical_nets.push_back(ThresholdHyperedge { tmp_he, _threshold });
}

template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructFlowHypergraph(const PartitionedHypergraph& phg,
                                                                             const Subhypergraph& sub_hg,
                                                                             const PartitionID block_0,
                                                                             const PartitionID block_1,
                                                                             vec<HypernodeID>& whfc_to_node,
                                                                             const bool deterministic) {
  const double density = static_cast<double>(phg.initialNumEdges()) / phg.initialNumNodes();
  const double avg_he_size = static_cast<double>(phg.initialNumPins()) / phg.initialNumEdges();
  const bool default_construction = density >= 0.5 && avg_he_size <= 100;
  return constructFlowHypergraphExplicit(phg, sub_hg, block_0, block_1, whfc_to_node, default_construction, deterministic);
}

template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructFlowHypergraphExplicit(const PartitionedHypergraph& phg,
                                                                                     const Subhypergraph& sub_hg,
                                                                                     const PartitionID block_0,
                                                                                     const PartitionID block_1,
                                                                                     vec<HypernodeID>& whfc_to_node,
                                                                                     const bool default_construction,
                                                                                     const bool deterministic) {
  FlowProblem flow_problem;

  if constexpr (PartitionedHypergraph::is_graph) {
    // Since non-determinism only arises from the deduplication of hyperedges, we can
    // use the default construction even in the deterministic case if the input is a graph
    flow_problem = constructDefault(phg, sub_hg, block_0, block_1, whfc_to_node);
  } else if (default_construction) {
    // This algorithm iterates over all hyperedges and checks for all pins if
    // they are contained in the flow problem.
    if (deterministic) {
      flow_problem = constructDefaultDeterministic(phg, sub_hg, block_0, block_1, whfc_to_node);
    } else {
      flow_problem = constructDefault(phg, sub_hg, block_0, block_1, whfc_to_node);
    }
  } else {
    // The default construction algorithm always scans all hyperedges which
    // intersect the sub-hypergraph. In case of large hyperedges, this is slow
    // because it includes many pins outside of the flow problem.
    // The algorithm used below avoids this by scanning the nodes and collecting
    // the incident hyperedges. However, it requires an additional step to copy
    // and sort the pins. Therefore it can have overheads for hypergraphs with
    // small hyperedges.
    if (deterministic) {
      flow_problem = constructOptimizedForLargeHEsDeterministic(phg, sub_hg, block_0, block_1, whfc_to_node);
    } else {
      flow_problem = constructOptimizedForLargeHEs(phg, sub_hg, block_0, block_1, whfc_to_node);
    }
  }

  if ( _flow_hg.nodeWeight(flow_problem.source) == 0 ||
       _flow_hg.nodeWeight(flow_problem.sink) == 0 ) {
    // Source or sink not connected to vertices in the flow problem
    flow_problem.non_removable_cut = 0;
    flow_problem.total_cut = 0;
  } else {
    _flow_hg.finalizeParallel();

    if ( _context.refinement.flows.determine_distance_from_cut ) {
      // Determine the distance of each node contained in the flow network from the cut.
      // This technique improves piercing decision within the WHFC framework.
      determineDistanceFromCut(phg, flow_problem.source,
        flow_problem.sink, block_0, block_1, whfc_to_node);
    }
  }

  DBG << "Flow Hypergraph [ Nodes =" << _flow_hg.numNodes()
      << ", Edges =" << _flow_hg.numHyperedges()
      << ", Pins =" << _flow_hg.numPins()
      << ", Blocks = (" << block_0 << "," << block_1 << ") ]";

  return flow_problem;
}

template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructDefault(const PartitionedHypergraph& phg,
                                                                      const Subhypergraph& sub_hg,
                                                                      const PartitionID block_0,
                                                                      const PartitionID block_1,
                                                                      vec<HypernodeID>& whfc_to_node) {
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;

  tbb::parallel_invoke([&]() {
    _node_to_whfc.clear();
    _node_to_whfc.setMaxSize(sub_hg.numNodes());
  }, [&] {
    whfc_to_node.resize(sub_hg.numNodes() + 2);
  }, [&] {
    _flow_hg.allocateNodes(sub_hg.numNodes() + 2);
  }, [&] {
    _identical_nets.reset();
  });

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  initializeWHFCNodes(phg, sub_hg, block_0, block_1, flow_problem, whfc_to_node, false);

  const HyperedgeID max_hyperedges = sub_hg.hes.size();
  const HypernodeID max_pins = sub_hg.num_pins + max_hyperedges;
  _flow_hg.allocateHyperedgesAndPins(max_hyperedges, max_pins);

  // Add hyperedges to flow network and configure source and sink
  auto push_into_tmp_pins = [&](vec<whfc::Node>& tmp_pins, const whfc::Node pin,
                                size_t& current_hash, const bool is_source_or_sink) {
    tmp_pins.push_back(pin);
    current_hash += kahypar::math::hash(pin);
    if ( is_source_or_sink ) {
      // According to Lars: Adding to source or sink to the start of
      // each pin list improves running time
      std::swap(tmp_pins[0], tmp_pins.back());
    }
  };

  _flow_hg.setNumCSRBuckets(NUM_CSR_BUCKETS);
  const size_t step = (max_hyperedges + NUM_CSR_BUCKETS - 1) / NUM_CSR_BUCKETS;
  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t bucket_idx) {
    const size_t start = std::min(step * bucket_idx, static_cast<size_t>(max_hyperedges));
    const size_t end = std::min(step * (bucket_idx + 1), static_cast<size_t>(max_hyperedges));
    const size_t num_hes = end - start;
    size_t num_pins = 0;
    for ( size_t i = start; i < end; ++i ) {
      const HyperedgeID he = sub_hg.hes[i];
      num_pins += phg.edgeSize(he) + 1;
    }
    _flow_hg.initializeCSRBucket(bucket_idx, num_hes, num_pins);

    whfc::Hyperedge e(0);
    size_t pin_idx = 0;
    vec<whfc::Node>& tmp_pins = _tmp_pins.local();
    for ( size_t i = start; i < end; ++i ) {
      const HyperedgeID he = sub_hg.hes[i];
      FlowNetworkEdgeParameters parameters =
        FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);
      ASSERT(parameters.capacity >= 0);

      // this check removes any edges that can't affect the global objective
      if (parameters.capacity == 0) continue;

      tmp_pins.clear();
      size_t he_hash = 0;
      if ( parameters.is_cut || (phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0) ) {
        repcut_serial::Ref(flow_problem.total_cut)
            .fetch_add(parameters.capacity, std::memory_order_relaxed);
      }
      for ( const HypernodeID& pin : phg.pins(he) ) {
        whfc::Node* whfc_pin = _node_to_whfc.get_if_contained(pin);
        if ( whfc_pin ) {
          push_into_tmp_pins(tmp_pins, *whfc_pin, he_hash, false);
        } else {
          const PartitionID pin_block = phg.partID(pin);
          parameters.connect_to_source |= pin_block == block_0;
          parameters.connect_to_sink |= pin_block == block_1;
        }
      }

      const bool connected_to_source_and_sink = parameters.connect_to_source && parameters.connect_to_sink;
      if ( connected_to_source_and_sink ) {
        // Hyperedge is connected to source and sink which means we can not remove it
        // from the cut with the current flow problem => remove he from flow problem
        repcut_serial::Ref(flow_problem.non_removable_cut)
            .fetch_add(parameters.capacity, std::memory_order_relaxed);
      } else if ( !tmp_pins.empty() ) {
        if ( parameters.connect_to_source ) {
          push_into_tmp_pins(tmp_pins, flow_problem.source, he_hash, true);
        } else if ( parameters.connect_to_sink ) {
          push_into_tmp_pins(tmp_pins, flow_problem.sink, he_hash, true);
        }

        // Sort pins for identical net detection
        std::sort( tmp_pins.begin() +
                  ( tmp_pins[0] == flow_problem.source ||
                    tmp_pins[0] == flow_problem.sink), tmp_pins.end());

        if ( tmp_pins.size() > 1 ) {
          const TmpHyperedge identical_net = _identical_nets.get(he_hash, tmp_pins);
          if ( identical_net.e == whfc::invalidHyperedge ) {
            const size_t pin_start = pin_idx;
            const size_t pin_end = pin_start + tmp_pins.size();
            for ( size_t i = 0; i < tmp_pins.size(); ++i ) {
              _flow_hg.addPin(tmp_pins[i], bucket_idx, pin_idx++);
            }
            TmpHyperedge tmp_e { he_hash, bucket_idx, e++ };
            if ( _context.refinement.flows.determine_distance_from_cut &&
                phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0 ) {
              _cut_hes.push_back(tmp_e);
            }
            _flow_hg.finishHyperedge(tmp_e.e, parameters.capacity, bucket_idx, pin_start, pin_end);
            _identical_nets.add(tmp_e);
          } else {
            // Current hyperedge is identical to an already added
            repcut_serial::Ref(_flow_hg.capacity(identical_net.bucket, identical_net.e))
                .fetch_add(parameters.capacity, std::memory_order_relaxed);
          }
        }
      }
    }
  });

  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t idx) {
    _flow_hg.finalizeCSRBucket(idx);
  });
  _flow_hg.finalizeHyperedges();

  return flow_problem;
}

template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructDefaultDeterministic(const PartitionedHypergraph& phg,
                                                                                   const Subhypergraph& sub_hg,
                                                                                   const PartitionID block_0,
                                                                                   const PartitionID block_1,
                                                                                   vec<HypernodeID>& whfc_to_node) {
  ALWAYS_ASSERT(!PartitionedHypergraph::is_graph);
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;

  tbb::parallel_invoke([&]() {
    _node_to_whfc.clear();
    _node_to_whfc.setMaxSize(sub_hg.numNodes());
  }, [&] {
    whfc_to_node.resize(sub_hg.numNodes() + 2);
  }, [&] {
    _flow_hg.allocateNodes(sub_hg.numNodes() + 2);
  });

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  initializeWHFCNodes(phg, sub_hg, block_0, block_1, flow_problem, whfc_to_node, false);

  // Add hyperedges to flow network and configure source and sink
  const HyperedgeID max_hyperedges = sub_hg.hes.size();
  const HypernodeID max_pins = sub_hg.num_pins + max_hyperedges;
  _flow_hg.allocateHyperedgesAndPins(max_hyperedges, max_pins);
  _tmp_hyperedge_buffer.resize(max_hyperedges);
  vec<TmpDeterministicHyperedge>& tmp_hyperedges = _tmp_hyperedge_buffer.tmp_hyperedges;
  vec<uint8_t>& valid_hyperedges = _tmp_hyperedge_buffer.valid_hyperedges;

  auto push_into_tmp_pins = [&](vec<whfc::Node>& tmp_pins, const whfc::Node pin,
                                size_t& current_hash, const bool is_source_or_sink) {
    tmp_pins.push_back(pin);
    current_hash += pin * pin;
    if ( is_source_or_sink ) {
      // According to Lars: Adding to source or sink to the start of
      // each pin list improves running time
      std::swap(tmp_pins[0], tmp_pins.back());
    }
  };

  ds::ConcurrentBucketMap<HashedHyperedge> hyperedge_hash_map;
  hyperedge_hash_map.reserve_for_estimated_number_of_insertions(max_hyperedges);
  // Contract Hyperedges
  tbb::parallel_for(ID(0), max_hyperedges, [&](const size_t i) {
    const HyperedgeID he = sub_hg.hes[i];
    FlowNetworkEdgeParameters parameters =
      FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);
    ASSERT(parameters.capacity >= 0);

    // mark HE as invalid if it is not later explicitly marked as valid
    valid_hyperedges[i] = static_cast<uint8_t>(false);

    // this check removes any edges that can't affect the global objective
    if (parameters.capacity == 0) return;

    vec<whfc::Node>& tmp_pins = tmp_hyperedges[i].pins;
    // Copy hyperedge and pins to temporary buffer
    size_t he_hash = 0;
    tmp_hyperedges[i].weight = parameters.capacity;
    tmp_pins.clear();
    tmp_pins.reserve(phg.edgeSize(he));
    if ( parameters.is_cut || (phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0) ) {
      repcut_serial::Ref(flow_problem.total_cut)
          .fetch_add(parameters.capacity, std::memory_order_relaxed);
    }
    for (const HypernodeID& pin : phg.pins(he)) {
      whfc::Node* whfc_pin = _node_to_whfc.get_if_contained(pin);
      if (whfc_pin) {
        push_into_tmp_pins(tmp_pins, *whfc_pin, he_hash, false);
      } else {
        const PartitionID pin_block = phg.partID(pin);
        parameters.connect_to_source |= pin_block == block_0;
        parameters.connect_to_sink |= pin_block == block_1;
      }
    }

    const bool connected_to_source_and_sink = parameters.connect_to_source && parameters.connect_to_sink;
    if (connected_to_source_and_sink) {
      // Hyperedge is connected to source and sink which means we can not remove it
      // from the cut with the current flow problem => remove he from flow problem
      repcut_serial::Ref(flow_problem.non_removable_cut)
          .fetch_add(tmp_hyperedges[i].weight, std::memory_order_relaxed);
    } else if (!tmp_pins.empty()) {
      if (parameters.connect_to_source) {
        push_into_tmp_pins(tmp_pins, flow_problem.source, he_hash, true);
      } else if (parameters.connect_to_sink) {
        push_into_tmp_pins(tmp_pins, flow_problem.sink, he_hash, true);
      }

      if (tmp_pins.size() > 1) {
        // Insert contracted hyperedge
        hyperedge_hash_map.insert(he_hash,
          HashedHyperedge{ i, he_hash, tmp_pins.size() });
        valid_hyperedges[i] = static_cast<uint8_t>(true);
        std::sort( tmp_pins.begin() +
                  ( tmp_pins[0] == flow_problem.source ||
                    tmp_pins[0] == flow_problem.sink), tmp_pins.end());
      }
    }
  });

  // Deduplicate Hyperedges
  tbb::parallel_for(UL(0), hyperedge_hash_map.numBuckets(), [&](const size_t bucket) {
    auto& hyperedge_bucket = hyperedge_hash_map.getBucket(bucket);
    deduplicateParallelHyperedges(hyperedge_bucket, tmp_hyperedges, valid_hyperedges);
    hyperedge_hash_map.free(bucket);
  });

  _flow_hg.setNumCSRBuckets(NUM_CSR_BUCKETS);
  const size_t step = (max_hyperedges + NUM_CSR_BUCKETS - 1) / NUM_CSR_BUCKETS;
  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t bucket_idx) {
    const size_t start = std::min(step * bucket_idx, static_cast<size_t>(max_hyperedges));
    const size_t end = std::min(step * (bucket_idx + 1), static_cast<size_t>(max_hyperedges));
    const size_t num_hes = end - start;
    size_t num_pins = 0;
    for (size_t i = start; i < end; ++i) {
      if (valid_hyperedges[i]) {
        num_pins += tmp_hyperedges[i].pins.size();
      }
    }
    _flow_hg.initializeCSRBucket(bucket_idx, num_hes, num_pins);

    whfc::Hyperedge e(0);
    size_t pin_idx = 0;
    for ( size_t i = start; i < end; ++i ) {
      if (valid_hyperedges[i]) {
        const size_t pin_start = pin_idx;
        const size_t pin_end = pin_start + tmp_hyperedges[i].pins.size();
        for (size_t j = 0; j < tmp_hyperedges[i].pins.size(); ++j) {
          _flow_hg.addPin(tmp_hyperedges[i].pins[j], bucket_idx, pin_idx++);
        }
        TmpHyperedge tmp_e{ 0, bucket_idx, e++ };
        const HyperedgeID he = sub_hg.hes[i];
        if (_context.refinement.flows.determine_distance_from_cut &&
          phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0) {
          _cut_hes.push_back(tmp_e);
        }
        _flow_hg.finishHyperedge(tmp_e.e, tmp_hyperedges[i].weight, bucket_idx, pin_start, pin_end);
      }
    }
  });

  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t idx) {
    _flow_hg.finalizeCSRBucket(idx);
  });
  _flow_hg.finalizeHyperedges();

  return flow_problem;
}

template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructOptimizedForLargeHEs(const PartitionedHypergraph& phg,
                                                                                   const Subhypergraph& sub_hg,
                                                                                   const PartitionID block_0,
                                                                                   const PartitionID block_1,
                                                                                   vec<HypernodeID>& whfc_to_node) {
  ALWAYS_ASSERT(!PartitionedHypergraph::is_graph);
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;

  tbb::parallel_invoke([&]() {
    _he_to_whfc.clear();
    _he_to_whfc.setMaxSize(sub_hg.hes.size());
    tbb::parallel_for(UL(0), sub_hg.hes.size(), [&](const size_t i) {
      const HyperedgeID he = sub_hg.hes[i];
      _he_to_whfc[he] = i;
    });
  }, [&]() {
    _node_to_whfc.clear();
    _node_to_whfc.setMaxSize(sub_hg.numNodes());
  }, [&] {
    whfc_to_node.resize(sub_hg.numNodes() + 2);
  }, [&] {
    _flow_hg.allocateNodes(sub_hg.numNodes() + 2);
  }, [&] {
    _identical_nets.reset();
  });

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  initializeWHFCNodes(phg, sub_hg, block_0, block_1, flow_problem, whfc_to_node, true);

  const size_t num_buckets = _pins.numBuckets();
  const HyperedgeID max_hyperedges = sub_hg.hes.size();
  const HypernodeID max_pins = sub_hg.num_pins + max_hyperedges;
  _flow_hg.allocateHyperedgesAndPins(max_hyperedges, max_pins);
  _flow_hg.setNumCSRBuckets(num_buckets);

  _pins.doParallelForAllBuckets([&](const size_t bucket_idx) {
    vec<TmpPin>& pins_of_bucket = _pins.getBucket(bucket_idx);
    if ( pins_of_bucket.size() > 0 ) {
      std::sort(pins_of_bucket.begin(), pins_of_bucket.end(),
        [&](const TmpPin& lhs, const TmpPin& rhs ) {
          return lhs.e < rhs.e || (lhs.e == rhs.e && lhs.pin < rhs.pin);
        });

      HyperedgeID last_he = kInvalidHyperedge;
      size_t num_hes = 0;
      size_t num_pins = 0;
      for ( const TmpPin& pin : pins_of_bucket ) {
        if ( pin.e != last_he ) {
          ++num_hes;
          last_he = pin.e;
        }
        ++num_pins;
      }
      num_pins += num_hes;
      _flow_hg.initializeCSRBucket(bucket_idx, num_hes, num_pins);

      whfc::Hyperedge current_he(0);
      size_t pin_idx = 0;
      vec<whfc::Node>& tmp_pins = _tmp_pins.local();
      size_t start_idx = 0;
      last_he = pins_of_bucket[start_idx].e;
      HypernodeID pin_count_in_block_0 = 0;
      HypernodeID pin_count_in_block_1 = 0;

      auto add_hyperedge = [&](const size_t end_idx) {
        ASSERT(start_idx < end_idx);
        tmp_pins.clear();
        const HyperedgeID he = sub_hg.hes[last_he];
        FlowNetworkEdgeParameters parameters =
          FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);
        ASSERT(parameters.capacity >= 0);

        // this check removes any edges that can't affect the global objective
        if (parameters.capacity == 0) return;

        const HypernodeID actual_pin_count_block_0 = phg.pinCountInPart(he, block_0);
        const HypernodeID actual_pin_count_block_1 = phg.pinCountInPart(he, block_1);
        parameters.connect_to_source |= pin_count_in_block_0 < actual_pin_count_block_0;
        parameters.connect_to_sink |= pin_count_in_block_1 < actual_pin_count_block_1;
        if ( parameters.is_cut || (actual_pin_count_block_0 > 0 && actual_pin_count_block_1 > 0) ) {
          repcut_serial::Ref(flow_problem.total_cut)
              .fetch_add(parameters.capacity, std::memory_order_relaxed);
        }

        if ( parameters.connect_to_source && parameters.connect_to_sink ) {
          // Hyperedge is connected to source and sink which means we can not remove it
          // from the cut with the current flow problem => remove he from flow problem
          repcut_serial::Ref(flow_problem.non_removable_cut)
              .fetch_add(parameters.capacity, std::memory_order_relaxed);
        } else {
          // Add hyperedge to flow network and configure source and sink
          size_t hash = 0;
          if ( parameters.connect_to_source ) {
            tmp_pins.push_back(flow_problem.source);
            hash += kahypar::math::hash(flow_problem.source);
          } else if ( parameters.connect_to_sink ) {
            tmp_pins.push_back(flow_problem.sink);
            hash += kahypar::math::hash(flow_problem.sink);
          }
          for ( size_t i = start_idx; i < end_idx; ++i ) {
            tmp_pins.push_back(pins_of_bucket[i].pin);
            hash += kahypar::math::hash(pins_of_bucket[i].pin);
          }

          if ( tmp_pins.size() > 1 ) {
            const TmpHyperedge identical_net = _identical_nets.get(hash, tmp_pins);
            if ( identical_net.e == whfc::invalidHyperedge ) {
              const size_t pin_start = pin_idx;
              const size_t pin_end = pin_start + tmp_pins.size();
              for ( const whfc::Node& pin : tmp_pins ) {
                _flow_hg.addPin(pin, bucket_idx, pin_idx++);
              }
              TmpHyperedge tmp_e { hash, bucket_idx, current_he++ };
              if ( _context.refinement.flows.determine_distance_from_cut &&
                  actual_pin_count_block_0 > 0 && actual_pin_count_block_1 > 0 ) {
                _cut_hes.push_back(tmp_e);
              }
              _flow_hg.finishHyperedge(tmp_e.e, parameters.capacity, bucket_idx, pin_start, pin_end);
              _identical_nets.add(tmp_e);
            } else {
              // Current hyperedge is identical to an already added
              repcut_serial::Ref(_flow_hg.capacity(identical_net.bucket, identical_net.e))
                  .fetch_add(parameters.capacity, std::memory_order_relaxed);
            }
          }
        }
      };

      for ( size_t i = 0; i < pins_of_bucket.size(); ++i ) {
        if ( last_he != pins_of_bucket[i].e ) {
          add_hyperedge(i);
          start_idx = i;
          last_he = pins_of_bucket[i].e;
          pin_count_in_block_0 = 0;
          pin_count_in_block_1 = 0;
        }
        pin_count_in_block_0 += pins_of_bucket[i].block == block_0;
        pin_count_in_block_1 += pins_of_bucket[i].block == block_1;
      }
      add_hyperedge(pins_of_bucket.size());
    } else {
      _flow_hg.initializeCSRBucket(bucket_idx, 0, 0);
    }
    _pins.clear(bucket_idx);
  });

  tbb::parallel_for(UL(0), num_buckets, [&](const size_t idx) {
    _flow_hg.finalizeCSRBucket(idx);
  });
  _flow_hg.finalizeHyperedges();

  return flow_problem;
}


template<typename GraphAndGainTypes>
FlowProblem ParallelConstruction<GraphAndGainTypes>::constructOptimizedForLargeHEsDeterministic(const PartitionedHypergraph& phg,
                                                                                                const Subhypergraph& sub_hg,
                                                                                                const PartitionID block_0,
                                                                                                const PartitionID block_1,
                                                                                                vec<HypernodeID>& whfc_to_node) {
  ALWAYS_ASSERT(!PartitionedHypergraph::is_graph);
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;

  tbb::parallel_invoke([&]() {
    _he_to_whfc.clear();
    _he_to_whfc.setMaxSize(sub_hg.hes.size());
    tbb::parallel_for(UL(0), sub_hg.hes.size(), [&](const size_t i) {
      const HyperedgeID he = sub_hg.hes[i];
      _he_to_whfc[he] = i;
    });
  }, [&]() {
    _node_to_whfc.clear();
    _node_to_whfc.setMaxSize(sub_hg.numNodes());
  }, [&] {
    whfc_to_node.resize(sub_hg.numNodes() + 2);
  }, [&] {
    _flow_hg.allocateNodes(sub_hg.numNodes() + 2);
  });

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  initializeWHFCNodes(phg, sub_hg, block_0, block_1, flow_problem, whfc_to_node, true);

  const size_t num_buckets = _pins.numBuckets();
  const HyperedgeID max_hyperedges = sub_hg.hes.size();
  const HypernodeID max_pins = sub_hg.num_pins + max_hyperedges;
  _flow_hg.allocateHyperedgesAndPins(max_hyperedges, max_pins);
  _flow_hg.setNumCSRBuckets(num_buckets);
  _tmp_hyperedge_buffer.resize(max_hyperedges);
  vec<TmpDeterministicHyperedge>& tmp_hyperedges = _tmp_hyperedge_buffer.tmp_hyperedges;
  vec<uint8_t>& valid_hyperedges = _tmp_hyperedge_buffer.valid_hyperedges;

  ds::ConcurrentBucketMap<HashedHyperedge> hyperedge_hash_map;
  hyperedge_hash_map.reserve_for_estimated_number_of_insertions(max_hyperedges);
  _pins.doParallelForAllBuckets([&](const size_t bucket_idx) {
    vec<TmpPin>& pins_of_bucket = _pins.getBucket(bucket_idx);
    if (pins_of_bucket.size() > 0) {
      std::sort(pins_of_bucket.begin(), pins_of_bucket.end(),
        [&](const TmpPin& lhs, const TmpPin& rhs) {
        return lhs.e < rhs.e || (lhs.e == rhs.e && lhs.pin < rhs.pin);
      });

      size_t start_idx = 0;
      HyperedgeID last_he = pins_of_bucket[start_idx].e;
      HypernodeID pin_count_in_block_0 = 0;
      HypernodeID pin_count_in_block_1 = 0;

      auto add_hyperedge = [&](const size_t end_idx) {
        vec<whfc::Node>& tmp_pins = tmp_hyperedges[last_he].pins;
        ASSERT(start_idx < end_idx);
        tmp_pins.clear();
        const HyperedgeID he = sub_hg.hes[last_he];
        FlowNetworkEdgeParameters parameters =
          FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);
        ASSERT(parameters.capacity >= 0);

        // mark HE as invalid if it is not later explicitly marked as valid
        valid_hyperedges[last_he] = static_cast<uint8_t>(false);

        // this check removes any edges that can't affect the global objective
        if (parameters.capacity == 0) return;

        tmp_pins.reserve(phg.edgeSize(he));
        tmp_hyperedges[last_he].weight = parameters.capacity;
        const HypernodeID actual_pin_count_block_0 = phg.pinCountInPart(he, block_0);
        const HypernodeID actual_pin_count_block_1 = phg.pinCountInPart(he, block_1);
        parameters.connect_to_source |= pin_count_in_block_0 < actual_pin_count_block_0;
        parameters.connect_to_sink |= pin_count_in_block_1 < actual_pin_count_block_1;
        if ( parameters.is_cut || (actual_pin_count_block_0 > 0 && actual_pin_count_block_1 > 0) ) {
          repcut_serial::Ref(flow_problem.total_cut)
              .fetch_add(parameters.capacity, std::memory_order_relaxed);
        }

        if ( parameters.connect_to_source && parameters.connect_to_sink ) {
          // Hyperedge is connected to source and sink which means we can not remove it
          // from the cut with the current flow problem => remove he from flow problem
          repcut_serial::Ref(flow_problem.non_removable_cut)
              .fetch_add(parameters.capacity, std::memory_order_relaxed);
        } else {
          // Add hyperedge to flow network and configure source and sink
          size_t hash = 0;
          if ( parameters.connect_to_source ) {
            tmp_pins.push_back(flow_problem.source);
            hash += kahypar::math::hash(flow_problem.source);
          } else if ( parameters.connect_to_sink ) {
            tmp_pins.push_back(flow_problem.sink);
            hash += kahypar::math::hash(flow_problem.sink);
          }
          for ( size_t i = start_idx; i < end_idx; ++i ) {
            tmp_pins.push_back(pins_of_bucket[i].pin);
            hash += kahypar::math::hash(pins_of_bucket[i].pin);
          }
          if (tmp_pins.size() > 1) {
            hyperedge_hash_map.insert(hash,
              HashedHyperedge{ last_he, hash, tmp_pins.size() });
            valid_hyperedges[last_he] = static_cast<uint8_t>(true);
          }
        }
      };

      for ( size_t i = 0; i < pins_of_bucket.size(); ++i ) {
        if ( last_he != pins_of_bucket[i].e ) {
          add_hyperedge(i);
          start_idx = i;
          last_he = pins_of_bucket[i].e;
          pin_count_in_block_0 = 0;
          pin_count_in_block_1 = 0;
        }
        pin_count_in_block_0 += pins_of_bucket[i].block == block_0;
        pin_count_in_block_1 += pins_of_bucket[i].block == block_1;
      }
      add_hyperedge(pins_of_bucket.size());
    }
    _pins.clear(bucket_idx);
  });

  // Deduplicate Hyperedges
  tbb::parallel_for(UL(0), hyperedge_hash_map.numBuckets(), [&](const size_t bucket) {
    auto& hyperedge_bucket = hyperedge_hash_map.getBucket(bucket);
    deduplicateParallelHyperedges(hyperedge_bucket, tmp_hyperedges, valid_hyperedges);
    hyperedge_hash_map.free(bucket);
  });

  _flow_hg.setNumCSRBuckets(NUM_CSR_BUCKETS);
  const size_t step = (max_hyperedges + NUM_CSR_BUCKETS - 1) / NUM_CSR_BUCKETS;
  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t bucket_idx) {
    const size_t start = std::min(step * bucket_idx, static_cast<size_t>(max_hyperedges));
    const size_t end = std::min(step * (bucket_idx + 1), static_cast<size_t>(max_hyperedges));
    const size_t num_hes = end - start;
    size_t num_pins = 0;
    for (size_t i = start; i < end; ++i) {
      if (valid_hyperedges[i]) {
        num_pins += tmp_hyperedges[i].pins.size();
      }
    }
    _flow_hg.initializeCSRBucket(bucket_idx, num_hes, num_pins);

    whfc::Hyperedge e(0);
    size_t pin_idx = 0;
    for (size_t i = start; i < end; ++i) {
      const HyperedgeID he = sub_hg.hes[i];
      if (valid_hyperedges[i]) {
        const size_t pin_start = pin_idx;
        const size_t pin_end = pin_start + tmp_hyperedges[i].pins.size();
        for (const auto p : tmp_hyperedges[i].pins) {
          _flow_hg.addPin(p, bucket_idx, pin_idx++);
        }
        TmpHyperedge tmp_e{ 0, bucket_idx, e++ };
        if (_context.refinement.flows.determine_distance_from_cut &&
          phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0) {
          _cut_hes.push_back(tmp_e);
        }
        _flow_hg.finishHyperedge(tmp_e.e, tmp_hyperedges[i].weight, bucket_idx, pin_start, pin_end);
      }
    }
  });
  tbb::parallel_for(UL(0), NUM_CSR_BUCKETS, [&](const size_t idx) {
    _flow_hg.finalizeCSRBucket(idx);
  });
  _flow_hg.finalizeHyperedges();

  return flow_problem;
}

namespace {
template<typename T>
class BFSQueue {

 public:
  explicit BFSQueue(const size_t num_threads) :
    _q(num_threads) { }

  bool empty() {
    bool is_empty = true;
    for ( size_t i = 0; i < _q.size(); ++i ) {
      is_empty &= _q[i].empty();
    }
    return is_empty;
  }

  bool empty(const size_t i) {
    ASSERT(i < _q.size());
    return _q[i].empty();
  }

  void push(const T elem, const size_t i) {
    ASSERT(i < _q.size());
    return _q[i].push(elem);
  }

  T front(const size_t i) {
    ASSERT(i < _q.size());
    return _q[i].front();
  }

  void pop(const size_t i) {
    ASSERT(i < _q.size());
    return _q[i].pop();
  }

 private:
  vec<parallel::scalable_queue<T>> _q;
};
}

template<typename GraphAndGainTypes>
void ParallelConstruction<GraphAndGainTypes>::initializeWHFCNodes(const PartitionedHypergraph& phg,
                                                                  const Subhypergraph& sub_hg,
                                                                  const PartitionID block_0,
                                                                  const PartitionID block_1,
                                                                  FlowProblem& flow_problem,
                                                                  vec<HypernodeID>& whfc_to_node,
                                                                  bool collect_pins) {
  const size_t num_buckets = _pins.numBuckets();
  const HyperedgeID max_hyperedges = sub_hg.hes.size();
  const size_t hes_per_bucket = (max_hyperedges + num_buckets - 1) / num_buckets;
  tbb::parallel_invoke([&] {
    // Add source nodes
    flow_problem.source = whfc::Node(0);
    whfc_to_node[flow_problem.source] = kInvalidHypernode;
    _flow_hg.nodeWeight(flow_problem.source) = whfc::NodeWeight(
      std::max(0, phg.partWeight(block_0) - sub_hg.weight_of_block_0));
    tbb::parallel_for(UL(0), sub_hg.nodes_of_block_0.size(), [&](const size_t i) {
      const HypernodeID hn = sub_hg.nodes_of_block_0[i];
      const whfc::Node u(1 + i);
      whfc_to_node[u] = hn;
      _node_to_whfc[hn] = u;
      _flow_hg.nodeWeight(u) = whfc::NodeWeight(phg.nodeWeight(hn));

      if (collect_pins) {
        for (const HyperedgeID& he : phg.incidentEdges(hn)) {
          ASSERT(_he_to_whfc.get_if_contained(he) != nullptr);
          const HyperedgeID e = _he_to_whfc[he];
          _pins.insert(e / hes_per_bucket, TmpPin { e, u, block_0 });
        }
      }
    });
  }, [&] {
    // Add sink nodes
    flow_problem.sink = whfc::Node(sub_hg.nodes_of_block_0.size() + 1);
    whfc_to_node[flow_problem.sink] = kInvalidHypernode;
    _flow_hg.nodeWeight(flow_problem.sink) = whfc::NodeWeight(
      std::max(0, phg.partWeight(block_1) - sub_hg.weight_of_block_1));
    tbb::parallel_for(UL(0), sub_hg.nodes_of_block_1.size(), [&](const size_t i) {
      const HypernodeID hn = sub_hg.nodes_of_block_1[i];
      const whfc::Node u(flow_problem.sink + 1 + i);
      whfc_to_node[u] = hn;
      _node_to_whfc[hn] = u;
      _flow_hg.nodeWeight(u) = whfc::NodeWeight(phg.nodeWeight(hn));

      if (collect_pins) {
        for ( const HyperedgeID& he : phg.incidentEdges(hn) ) {
          ASSERT(_he_to_whfc.get_if_contained(he) != nullptr);
          const HyperedgeID e = _he_to_whfc[he];
          _pins.insert(e / hes_per_bucket, TmpPin { e, u, block_1 });
        }
      }
    });
  });
  flow_problem.weight_of_block_0 = _flow_hg.nodeWeight(flow_problem.source) + sub_hg.weight_of_block_0;
  flow_problem.weight_of_block_1 = _flow_hg.nodeWeight(flow_problem.sink) + sub_hg.weight_of_block_1;
}

template<typename GraphAndGainTypes>
bool ParallelConstruction<GraphAndGainTypes>::checkIfHyperedgesAreParallel(const TmpDeterministicHyperedge& lhs,
                                                                           const TmpDeterministicHyperedge& rhs) {
  if (lhs.pins.size() == rhs.pins.size()) {
    for (size_t i = 0; i < lhs.pins.size(); ++i) {
      if (lhs.pins[i] != rhs.pins[i]) {
        return false;
      }
    }
    return true;
  } else {
    return false;
  }
}

template<typename GraphAndGainTypes>
void ParallelConstruction<GraphAndGainTypes>::deduplicateParallelHyperedges(vec<HashedHyperedge>& bucket,
                                                                            vec<TmpDeterministicHyperedge>& tmp_hyperedges,
                                                                            vec<uint8_t>& valid_hyperedges) {
  std::sort(bucket.begin(), bucket.end(),
    [&](const HashedHyperedge& lhs, const HashedHyperedge& rhs) {
    return std::tie(lhs.hash, lhs.size, lhs.he) < std::tie(rhs.hash, rhs.size, rhs.he);
  });

  // Parallel Hyperedge Detection
  for (size_t i = 0; i < bucket.size(); ++i) {
    HashedHyperedge& hashed_he_lhs = bucket[i];
    const HyperedgeID lhs_he = hashed_he_lhs.he;
    HyperedgeWeight lhs_weight = tmp_hyperedges[lhs_he].weight;
    if (!valid_hyperedges[lhs_he]) continue;

    for (size_t j = i + 1; j < bucket.size() && hashed_he_lhs.hash == bucket[j].hash; ++j) {
      const HyperedgeID rhs_he = bucket[j].he;
      if (checkIfHyperedgesAreParallel(tmp_hyperedges[lhs_he], tmp_hyperedges[rhs_he])) {
        lhs_weight += tmp_hyperedges[rhs_he].weight;
        valid_hyperedges[rhs_he] = static_cast<uint8_t>(false);
      }
    }
    tmp_hyperedges[lhs_he].weight = lhs_weight;
  }
}

template<typename GraphAndGainTypes>
void ParallelConstruction<GraphAndGainTypes>::determineDistanceFromCut(const PartitionedHypergraph& phg,
                                                                    const whfc::Node source,
                                                                    const whfc::Node sink,
                                                                    const PartitionID block_0,
                                                                    const PartitionID block_1,
                                                                    const vec<HypernodeID>& whfc_to_node) {
  auto& distances = _hfc.cs.border_nodes.distance;
  distances.assign(_flow_hg.numNodes(), whfc::HopDistance(0));
  _visited_hns.resize(_flow_hg.numNodes() + _flow_hg.numHyperedges());
  _visited_hns.reset();
  _visited_hns.set(source, true);
  _visited_hns.set(sink, true);

  // Initialize bfs queue with vertices contained in cut hyperedges
  size_t q_idx = 0;

  const size_t num_threads = std::thread::hardware_concurrency();
  vec<BFSQueue<whfc::Node>> q(2, BFSQueue<whfc::Node>(num_threads));
  tbb::parallel_for(UL(0), _cut_hes.size(), [&](const size_t i) {
    const int thread_idx = tbb::this_task_arena::current_thread_index();
    const whfc::Hyperedge he = _flow_hg.originalHyperedgeID(_cut_hes[i].bucket, _cut_hes[i].e);
    for ( const whfc::FlowHypergraph::Pin& pin : _flow_hg.pinsOf(he) ) {
      if ( _visited_hns.compare_and_set_to_true(pin.pin) ) {
        q[q_idx].push(pin.pin, thread_idx);
      }
    }
    _visited_hns.set(_flow_hg.numNodes() + he, true);
  });

  // Perform BFS to determine distance of each vertex from cut
  whfc::HopDistance dist(1);
  whfc::HopDistance max_dist_source(0);
  whfc::HopDistance max_dist_sink(0);
  while ( !q[q_idx].empty() ) {
    bool reached_source_side = false;
    bool reached_sink_side = false;
    tbb::parallel_for(UL(0), num_threads, [&](const size_t idx) {
      while ( !q[q_idx].empty(idx) ) {
        whfc::Node u = q[q_idx].front(idx);
        q[q_idx].pop(idx);
        const PartitionID block_of_u = phg.partID(whfc_to_node[u]);
        if ( block_of_u == block_0 ) {
          distances[u] = -dist;
          reached_source_side = true;
        } else if ( block_of_u == block_1 ) {
          distances[u] = dist;
          reached_sink_side = true;
        }

        for ( const whfc::FlowHypergraph::InHe& in_he : _flow_hg.hyperedgesOf(u) ) {
          const whfc::Hyperedge he = in_he.e;
          if ( _visited_hns.compare_and_set_to_true(_flow_hg.numNodes() + he) ) {
            for ( const whfc::FlowHypergraph::Pin& pin : _flow_hg.pinsOf(he) ) {
              if ( _visited_hns.compare_and_set_to_true(pin.pin) ) {
                q[1 - q_idx].push(pin.pin, idx);
              }
            }
          }
        }
      }
    });

    if ( reached_source_side ) max_dist_source = dist;
    if ( reached_sink_side ) max_dist_sink = dist;

    ASSERT(q[q_idx].empty());
    q_idx = 1 - q_idx;
    ++dist;
  }
  distances[source] = -(max_dist_source + 1);
  distances[sink] = max_dist_sink + 1;
}

namespace {
#define PARALLEL_CONSTRUCTION(X) ParallelConstruction<X>
}

INSTANTIATE_CLASS_WITH_VALID_TRAITS(PARALLEL_CONSTRUCTION)

} // namespace mt_kahypar
