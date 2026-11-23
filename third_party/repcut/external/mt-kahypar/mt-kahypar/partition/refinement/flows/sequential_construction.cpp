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

#include "mt-kahypar/partition/refinement/flows/sequential_construction.h"

#include "kahypar-resources/utils/math.h"

#include "mt-kahypar/datastructures/flow_network_edge_parameters.h"
#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"

namespace mt_kahypar {

template<typename GraphAndGainTypes>
whfc::Hyperedge SequentialConstruction<GraphAndGainTypes>::DynamicIdenticalNetDetection::add_if_not_contained(
  const whfc::Hyperedge he, const size_t he_hash, const vec<whfc::Node>& pins) {
  const size_t bucket_idx = he_hash % _hash_buckets.size();
  if ( _hash_buckets[bucket_idx].threshold == _threshold ) {
    // There exists already some hyperedges with the same hash
    for ( const TmpHyperedge& tmp_e : _hash_buckets[bucket_idx].identical_nets ) {
      // Check if there is some hyperedge equal to he
      if ( tmp_e.hash == he_hash && _flow_hg.pinCount(tmp_e.e) == pins.size() ) {
        bool is_identical = true;
        size_t idx = 0;
        for ( const whfc::FlowHypergraph::Pin& u : _flow_hg.pinsOf(tmp_e.e) ) {
          if ( u.pin != pins[idx++] ) {
            is_identical = false;
            break;
          }
        }
        if ( is_identical ) {
          return tmp_e.e;
        }
      }
    }
  } else {
    _hash_buckets[bucket_idx].identical_nets.clear();
    _hash_buckets[bucket_idx].threshold = _threshold;
  }
  _hash_buckets[bucket_idx].identical_nets.push_back(TmpHyperedge { he_hash, he });
  return whfc::invalidHyperedge;
}

template<typename GraphAndGainTypes>
FlowProblem SequentialConstruction<GraphAndGainTypes>::constructFlowHypergraph(const PartitionedHypergraph& phg,
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
FlowProblem SequentialConstruction<GraphAndGainTypes>::constructFlowHypergraphExplicit(const PartitionedHypergraph& phg,
                                                                                       const Subhypergraph& sub_hg,
                                                                                       const PartitionID block_0,
                                                                                       const PartitionID block_1,
                                                                                       vec<HypernodeID>& whfc_to_node,
                                                                                       const bool default_construction,
                                                                                       const bool /*deterministic*/) {
  FlowProblem flow_problem;

  if ( PartitionedHypergraph::is_graph || default_construction ) {
    // This algorithm iterates over all hyperedges and checks for all pins if
    // they are contained in the flow problem.
    flow_problem = constructDefault(phg, sub_hg, block_0, block_1, whfc_to_node);
  } else {
    // The default construction algorithm always scans all hyperedges which
    // intersect the sub-hypergraph. In case of large hyperedges, this is slow
    // because it includes many pins outside of the flow problem.
    // The algorithm used below avoids this by scanning the nodes and collecting
    // the incident hyperedges. However, it requires an additional step to copy
    // and sort the pins. Therefore it can have overheads for hypergraphs with
    // small hyperedges.
    flow_problem = constructOptimizedForLargeHEs(phg, sub_hg, block_0, block_1, whfc_to_node);
  }

  if ( _flow_hg.nodeWeight(flow_problem.source) == 0 ||
       _flow_hg.nodeWeight(flow_problem.sink) == 0 ) {
    // Source or sink not connected to vertices in the flow problem
    flow_problem.non_removable_cut = 0;
    flow_problem.total_cut = 0;
  } else {
    _flow_hg.finalize();

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
FlowProblem SequentialConstruction<GraphAndGainTypes>::constructDefault(const PartitionedHypergraph& phg,
                                                                     const Subhypergraph& sub_hg,
                                                                     const PartitionID block_0,
                                                                     const PartitionID block_1,
                                                                     vec<HypernodeID>& whfc_to_node) {
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;
  _identical_nets.reset();
  _node_to_whfc.clear();
  whfc_to_node.resize(sub_hg.numNodes() + 2);

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  // Add refinement nodes to flow network
  auto add_nodes = [&](const vec<HypernodeID>& nodes, const whfc::Node::ValueType start_u) {
    whfc::Node flow_hn(start_u);
    for ( const HypernodeID& hn : nodes) {
      const HypernodeWeight hn_weight = phg.nodeWeight(hn);
      whfc_to_node[flow_hn] = hn;
      _node_to_whfc[hn] = flow_hn++;
      _flow_hg.addNode(whfc::NodeWeight(hn_weight));
    }
  };
  // Add source nodes
  flow_problem.source = whfc::Node(0);
  whfc_to_node[flow_problem.source] = kInvalidHypernode;
  _flow_hg.addNode(whfc::NodeWeight(
    std::max(0, phg.partWeight(block_0) - sub_hg.weight_of_block_0)));
  add_nodes(sub_hg.nodes_of_block_0, flow_problem.source + 1);
  // Add sink nodes
  flow_problem.sink = whfc::Node(sub_hg.nodes_of_block_0.size() + 1);
  whfc_to_node[flow_problem.sink] = kInvalidHypernode;
  _flow_hg.addNode(whfc::NodeWeight(
    std::max(0, phg.partWeight(block_1) - sub_hg.weight_of_block_1)));
  add_nodes(sub_hg.nodes_of_block_1, flow_problem.sink + 1);
  flow_problem.weight_of_block_0 = _flow_hg.nodeWeight(flow_problem.source) + sub_hg.weight_of_block_0;
  flow_problem.weight_of_block_1 = _flow_hg.nodeWeight(flow_problem.sink) + sub_hg.weight_of_block_1;

  auto push_into_tmp_pins = [&](const whfc::Node pin, size_t& current_hash, const bool is_source_or_sink) {
    _tmp_pins.push_back(pin);
    current_hash += kahypar::math::hash(pin);
    if ( is_source_or_sink ) {
      // According to Lars: Adding to source or sink to the start of
      // each pin list improves running time
      std::swap(_tmp_pins[0], _tmp_pins.back());
    }
  };

  // Add hyperedge to flow network and configure source and sink
  whfc::Hyperedge current_he(0);
  for ( const HyperedgeID& he : sub_hg.hes ) {
    FlowNetworkEdgeParameters parameters =
      FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);
    ASSERT(parameters.capacity >= 0);

    // this check removes any edges that can't affect the global objective
    if (parameters.capacity == 0) continue;

    size_t he_hash = 0;
    _tmp_pins.clear();
    _flow_hg.startHyperedge(whfc::Flow(parameters.capacity));
    if ( parameters.is_cut || (phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0) ) {
      flow_problem.total_cut += parameters.capacity;
    }
    for ( const HypernodeID& pin : phg.pins(he) ) {
      if ( _node_to_whfc.contains(pin) ) {
        push_into_tmp_pins(_node_to_whfc[pin], he_hash, false);
      } else {
        const PartitionID pin_block = phg.partID(pin);
        parameters.connect_to_source |= pin_block == block_0;
        parameters.connect_to_sink |= pin_block == block_1;
      }
    }

    const bool empty_hyperedge = _tmp_pins.size() == 0;
    const bool connected_to_source_and_sink = parameters.connect_to_source && parameters.connect_to_sink;
    if ( connected_to_source_and_sink || empty_hyperedge ) {
      // Hyperedge is connected to source and sink which means we can not remove it
      // from the cut with the current flow problem => remove he from flow problem
      _flow_hg.removeCurrentHyperedge();
      flow_problem.non_removable_cut += connected_to_source_and_sink ? parameters.capacity : 0;
    } else {
      if ( parameters.connect_to_source ) {
        push_into_tmp_pins(flow_problem.source, he_hash, true);
      } else if ( parameters.connect_to_sink ) {
        push_into_tmp_pins(flow_problem.sink, he_hash, true);
      }

      // Sort pins for identical net detection
      std::sort( _tmp_pins.begin() +
                ( _tmp_pins[0] == flow_problem.source ||
                  _tmp_pins[0] == flow_problem.sink), _tmp_pins.end());

      if ( _tmp_pins.size() > 1 ) {
        whfc::Hyperedge identical_net =
          _identical_nets.add_if_not_contained(current_he, he_hash, _tmp_pins);
        if ( identical_net == whfc::invalidHyperedge ) {
          for ( const whfc::Node& pin : _tmp_pins ) {
            _flow_hg.addPin(pin);
          }
          if ( _context.refinement.flows.determine_distance_from_cut &&
                phg.pinCountInPart(he, block_0) > 0 && phg.pinCountInPart(he, block_1) > 0 ) {
            _cut_hes.push_back(current_he);
          }
          ++current_he;
        } else {
          // Current hyperedge is identical to an already added
          _flow_hg.capacity(identical_net) += parameters.capacity;
        }
      }
    }
  }

  return flow_problem;
}

template<typename GraphAndGainTypes>
FlowProblem SequentialConstruction<GraphAndGainTypes>::constructOptimizedForLargeHEs(const PartitionedHypergraph& phg,
                                                                                  const Subhypergraph& sub_hg,
                                                                                  const PartitionID block_0,
                                                                                  const PartitionID block_1,
                                                                                  vec<HypernodeID>& whfc_to_node) {
  ALWAYS_ASSERT(!PartitionedHypergraph::is_graph);
  ASSERT(block_0 != kInvalidPartition && block_1 != kInvalidPartition);
  FlowProblem flow_problem;
  flow_problem.total_cut = 0;
  flow_problem.non_removable_cut = 0;
  _identical_nets.reset();
  _pins.clear();
  _he_to_whfc.clear();
  whfc_to_node.resize(sub_hg.numNodes() + 2);

  if ( _context.refinement.flows.determine_distance_from_cut ) {
    _cut_hes.clear();
  }

  for ( size_t i = 0; i < sub_hg.hes.size(); ++i ) {
    const HyperedgeID he = sub_hg.hes[i];
    _he_to_whfc[he] = i;
  }

  // Add refinement nodes to flow network
  auto add_nodes = [&](const vec<HypernodeID>& nodes, const PartitionID block, const whfc::Node::ValueType start_u) {
    whfc::Node flow_hn(start_u);
    for ( const HypernodeID& hn : nodes) {
      const HypernodeWeight hn_weight = phg.nodeWeight(hn);
      whfc_to_node[flow_hn] = hn;
      _flow_hg.addNode(whfc::NodeWeight(hn_weight));
      for ( const HyperedgeID& he : phg.incidentEdges(hn) ) {
        ASSERT(_he_to_whfc.contains(he));
        _pins.push_back(TmpPin { _he_to_whfc[he], flow_hn, block });
      }
      ++flow_hn;
    }
  };
  // Add source nodes
  flow_problem.source = whfc::Node(0);
  whfc_to_node[flow_problem.source] = kInvalidHypernode;
  _flow_hg.addNode(whfc::NodeWeight(
    std::max(0, phg.partWeight(block_0) - sub_hg.weight_of_block_0)));
  add_nodes(sub_hg.nodes_of_block_0, block_0, flow_problem.source + 1);
  // Add sink nodes
  flow_problem.sink = whfc::Node(sub_hg.nodes_of_block_0.size() + 1);
  whfc_to_node[flow_problem.sink] = kInvalidHypernode;
  _flow_hg.addNode(whfc::NodeWeight(
    std::max(0, phg.partWeight(block_1) - sub_hg.weight_of_block_1)));
  add_nodes(sub_hg.nodes_of_block_1, block_1, flow_problem.sink + 1);
  flow_problem.weight_of_block_0 = _flow_hg.nodeWeight(flow_problem.source) + sub_hg.weight_of_block_0;
  flow_problem.weight_of_block_1 = _flow_hg.nodeWeight(flow_problem.sink) + sub_hg.weight_of_block_1;


  if ( _pins.size() > 0 ) {
    std::sort(_pins.begin(), _pins.end(),
      [&](const TmpPin& lhs, const TmpPin& rhs ) {
        return lhs.e < rhs.e || (lhs.e == rhs.e && lhs.pin < rhs.pin);
      });

    whfc::Hyperedge current_he(0);
    size_t start_idx = 0;
    HyperedgeID last_he = _pins[start_idx].e;
    HypernodeID pin_count_in_block_0 = 0;
    HypernodeID pin_count_in_block_1 = 0;

    auto add_hyperedge = [&](const size_t end_idx) {
      ASSERT(start_idx < end_idx);
      _tmp_pins.clear();
      const HyperedgeID he = sub_hg.hes[last_he];
      FlowNetworkEdgeParameters parameters =
        FlowNetworkConstruction::getParameters(phg, _context, he, block_0, block_1);

      if ( parameters.capacity > 0 ) {
        const HypernodeID actual_pin_count_block_0 = phg.pinCountInPart(he, block_0);
        const HypernodeID actual_pin_count_block_1 = phg.pinCountInPart(he, block_1);
        parameters.connect_to_source |= pin_count_in_block_0 < actual_pin_count_block_0;
        parameters.connect_to_sink |= pin_count_in_block_1 < actual_pin_count_block_1;
        if ( parameters.is_cut || (actual_pin_count_block_0 > 0 && actual_pin_count_block_1 > 0) ) {
          flow_problem.total_cut += parameters.capacity;
        }

        _flow_hg.startHyperedge(whfc::Flow(parameters.capacity));
        if ( parameters.connect_to_source && parameters.connect_to_sink ) {
          // Hyperedge is connected to source and sink which means we can not remove it
          // from the cut with the current flow problem => remove he from flow problem
          flow_problem.non_removable_cut += parameters.capacity;
          _flow_hg.removeCurrentHyperedge();
        } else {
          // Add hyperedge to flow network and configure source and sink
          size_t hash = 0;
          if ( parameters.connect_to_source ) {
            _tmp_pins.push_back(flow_problem.source);
            hash += kahypar::math::hash(flow_problem.source);
          } else if ( parameters.connect_to_sink ) {
            _tmp_pins.push_back(flow_problem.sink);
            hash += kahypar::math::hash(flow_problem.sink);
          }
          for ( size_t i = start_idx; i < end_idx; ++i ) {
            _tmp_pins.push_back(_pins[i].pin);
            hash += kahypar::math::hash(_pins[i].pin);
          }

          if ( _tmp_pins.size() > 1 ) {
            whfc::Hyperedge identical_net =
              _identical_nets.add_if_not_contained(current_he, hash, _tmp_pins);
            if ( identical_net == whfc::invalidHyperedge ) {
              for ( const whfc::Node& pin : _tmp_pins ) {
                _flow_hg.addPin(pin);
              }
              if ( _context.refinement.flows.determine_distance_from_cut &&
                  actual_pin_count_block_0 > 0 && actual_pin_count_block_1 > 0 ) {
                _cut_hes.push_back(current_he);
              }
              ++current_he;
            } else {
              // Current hyperedge is identical to an already added
              _flow_hg.capacity(identical_net) += parameters.capacity;
            }
          }
        }
      }
    };

    for ( size_t i = 0; i < _pins.size(); ++i ) {
      if ( last_he != _pins[i].e ) {
        add_hyperedge(i);
        start_idx = i;
        last_he = _pins[i].e;
        pin_count_in_block_0 = 0;
        pin_count_in_block_1 = 0;
      }
      pin_count_in_block_0 += _pins[i].block == block_0;
      pin_count_in_block_1 += _pins[i].block == block_1;
    }
    add_hyperedge(_pins.size());
  }

  return flow_problem;
}

template<typename GraphAndGainTypes>
void SequentialConstruction<GraphAndGainTypes>::determineDistanceFromCut(const PartitionedHypergraph& phg,
                                                                      const whfc::Node source,
                                                                      const whfc::Node sink,
                                                                      const PartitionID block_0,
                                                                      const PartitionID block_1,
                                                                      const vec<HypernodeID>& whfc_to_node) {
  auto& distances = _hfc.cs.border_nodes.distance;
  distances.assign(_flow_hg.numNodes(), whfc::HopDistance(0));
  _visited_hns.resize(_flow_hg.numNodes() + _flow_hg.numHyperedges());
  _visited_hns.reset();   // Review Note

  // Initialize bfs queue with vertices contained in cut hyperedges
  parallel::scalable_queue<whfc::Node> q, next_q;
  for ( const whfc::Hyperedge& he : _cut_hes ) {
    for ( const whfc::FlowHypergraph::Pin& pin : _flow_hg.pinsOf(he) ) {
      if ( pin.pin != source && pin.pin != sink && !_visited_hns[pin.pin] ) {
        q.push(pin.pin);
        _visited_hns.setUnsafe(pin.pin, true);
      }
    }
    _visited_hns.setUnsafe(_flow_hg.numNodes() + he, true);
  }

  // Perform BFS to determine distance of each vertex from cut
  whfc::HopDistance dist = 1;
  whfc::HopDistance max_dist_source(0);
  whfc::HopDistance max_dist_sink(0);
  while ( !q.empty() ) {
    const whfc::Node u = q.front();
    q.pop();

    const PartitionID block_of_u = phg.partID(whfc_to_node[u]);
    if ( block_of_u == block_0 ) {
      distances[u] = -dist;
      max_dist_source = std::max(max_dist_source, dist);
    } else if ( block_of_u == block_1 ) {
      distances[u] = dist;
      max_dist_sink = std::max(max_dist_sink, dist);
    }

    for ( const whfc::FlowHypergraph::InHe& in_he : _flow_hg.hyperedgesOf(u) ) {
      const whfc::Hyperedge he = in_he.e;
      if ( !_visited_hns[_flow_hg.numNodes() + he] ) {
        for ( const whfc::FlowHypergraph::Pin& pin : _flow_hg.pinsOf(he) ) {
          if ( pin.pin != source && pin.pin != sink && !_visited_hns[pin.pin] ) {
            next_q.push(pin.pin);
            _visited_hns.setUnsafe(pin.pin, true);
          }
        }
        _visited_hns.setUnsafe(_flow_hg.numNodes() + he, true);
      }
    }

    if ( q.empty() ) {
      std::swap(q, next_q);
      ++dist;
    }
  }
  distances[source] = -(max_dist_source + 1);
  distances[sink] = max_dist_sink + 1;
}

namespace {
#define SEQUENTIAL_CONSTRUCTION(X) SequentialConstruction<X>
}

INSTANTIATE_CLASS_WITH_VALID_TRAITS(SEQUENTIAL_CONSTRUCTION)

} // namespace mt_kahypar
