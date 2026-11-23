/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2021 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "mt-kahypar/partition/refinement/flows/flow_hypergraph_builder.h"

#include <atomic>

#include <tbb/blocked_range.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_reduce.h>
#include <tbb/parallel_scan.h>
#include <tbb/parallel_for.h>

namespace mt_kahypar {

// ####################### Sequential Construction #######################

void FlowHypergraphBuilder::finalize() {
  if( !finishHyperedge() )	{ //finish last open hyperedge
    // maybe the last started hyperedge has zero/one pins and thus we still use the
    // previous sentinel. was never a bug, since that capacity is never read
    hyperedges.back().capacity = 0;
  }

  total_node_weight = whfc::NodeWeight(0);
  for (whfc::Node u : nodeIDs()) {
    nodes[u+1].first_out += nodes[u].first_out;
    total_node_weight += nodes[u].weight;
  }

  incident_hyperedges.resize(numPins());
  for (whfc::Hyperedge e : hyperedgeIDs()) {
    for (auto pin_it = beginIndexPins(e); pin_it != endIndexPins(e); pin_it++) {
      Pin& p = pins[pin_it];
      //destroy first_out temporarily and reset later
      whfc::InHeIndex ind_he = nodes[p.pin].first_out++;
      incident_hyperedges[ind_he] = { e, pin_it };
      //set iterator for incident hyperedge -> its position in incident_hyperedges of the node
      p.he_inc_iter = ind_he;
    }
  }

  for (whfc::Node u(numNodes()-1); u > 0; u--) {
    nodes[u].first_out = nodes[u-1].first_out;	//reset temporarily destroyed first_out
  }
  nodes[0].first_out = whfc::InHeIndex(0);

  _finalized = true;
}

bool FlowHypergraphBuilder::finishHyperedge() {
  if (currentHyperedgeSize() == 1) {
    removeLastPin();
  }

  if (currentHyperedgeSize() > 0) {
    hyperedges.push_back({whfc::PinIndex::fromOtherValueType(numPins()), whfc::Flow(0)});//sentinel
    return true;
  }
  return false;
}

// ####################### Parallel Construction #######################

void FlowHypergraphBuilder::allocateHyperedgesAndPins(const size_t num_hyperedges,
                                                      const size_t num_pins) {
  tbb::parallel_invoke([&] {
    hyperedges.assign(num_hyperedges + 1, HyperedgeData {
      whfc::PinIndex::Invalid(), whfc::Flow(0) });
  }, [&] {
    pins.assign(num_pins, Pin { whfc::Node::Invalid(), whfc::InHeIndex::Invalid() });
  });
}

void FlowHypergraphBuilder::finalizeHyperedges() {
  for ( size_t i = 1; i < _tmp_csr_buckets.size(); ++i ) {
    _tmp_csr_buckets[i]._global_start_he =
      _tmp_csr_buckets[i - 1]._global_start_he + _tmp_csr_buckets[i - 1]._num_hes;
    _tmp_csr_buckets[i]._global_start_pin_idx =
      _tmp_csr_buckets[i - 1]._global_start_pin_idx + _tmp_csr_buckets[i - 1]._num_pins;
  }

  tbb::parallel_for(UL(0), _tmp_csr_buckets.size(), [&](const size_t idx) {
    _tmp_csr_buckets[idx].copyDataToFlowHypergraph(hyperedges, pins);
  });

  const size_t num_hyperedges =
    _tmp_csr_buckets.back()._global_start_he + _tmp_csr_buckets.back()._num_hes;
  const size_t num_pins =
    _tmp_csr_buckets.back()._global_start_pin_idx + _tmp_csr_buckets.back()._num_pins;
  resizeHyperedgesAndPins(num_hyperedges, num_pins);
  hyperedges.emplace_back( HyperedgeData { whfc::PinIndex(num_pins), whfc::Flow(0) } ); // sentinel
}

void FlowHypergraphBuilder::finalizeParallel() {
  ASSERT(verifyParallelConstructedHypergraph(), "Parallel construction failed!");

  tbb::parallel_invoke([&] {
    // Determine maximum edge capacity
    maxHyperedgeCapacity = tbb::parallel_reduce(
      tbb::blocked_range<size_t>(UL(0), hyperedges.size()), whfc::Flow(0),
      [&](const tbb::blocked_range<size_t>& range, whfc::Flow init) {
        whfc::Flow max_capacity = init;
        for (size_t i = range.begin(); i < range.end(); ++i) {
          max_capacity = std::max(max_capacity, hyperedges[i].capacity);
        }
        return max_capacity;
      }, [](const whfc::Flow& lhs, const whfc::Flow& rhs) {
        return std::max(lhs, rhs);
      });
  }, [&] {
    // Determine total node weight
    total_node_weight = tbb::parallel_reduce(
      tbb::blocked_range<size_t>(UL(0), static_cast<size_t>(numNodes())), whfc::NodeWeight(0),
      [&](const tbb::blocked_range<size_t>& range, whfc::NodeWeight init) {
        whfc::NodeWeight weight = init;
        for (size_t i = range.begin(); i < range.end(); ++i) {
          weight += nodes[i].weight;
        }
        return weight;
      }, std::plus<>());
  }, [&] {
    incident_hyperedges.resize(numPins());
  }, [&]() {
    _inc_he_pos.assign(numNodes(), 0);
  });

  // Compute node degree prefix sum
  tbb::parallel_scan(
    tbb::blocked_range<size_t>(UL(0), numNodes() + 1), whfc::InHeIndex(0),
    [&](const tbb::blocked_range<size_t>& r, whfc::InHeIndex sum, bool is_final_scan) -> whfc::InHeIndex {
      whfc::InHeIndex tmp = sum;
      for ( size_t i = r.begin(); i < r.end(); ++i ) {
        tmp += nodes[i].first_out;
        if ( is_final_scan ) {
          nodes[i].first_out = tmp;
        }
      }
      return tmp;
    }, [&](const whfc::InHeIndex lhs, const whfc::InHeIndex rhs) {
      return lhs + rhs;
    }
  );

  tbb::parallel_for(UL(0), numHyperedges(), [&](const size_t i) {
    const whfc::Hyperedge e(i);
    for ( auto pin_it = beginIndexPins(e); pin_it != endIndexPins(e); pin_it++ ) {
      Pin& p = pins[pin_it];
      const whfc::Node& u = p.pin;
      //destroy first_out temporarily and reset later
      whfc::InHeIndex::ValueType ind_he = nodes[u].first_out +
          repcut_serial::Ref(_inc_he_pos[u]).fetch_add(1, std::memory_order_relaxed);
      incident_hyperedges[ind_he] = { e, pin_it };
      //set iterator for incident hyperedge -> its position in incident_hyperedges of the node
      p.he_inc_iter = whfc::InHeIndex(ind_he);
    }
  });

  ASSERT([&]() {
    size_t num_pins = 0;
    for ( const whfc::Node& u : nodeIDs() ) {
      for ( const InHe& in_e : hyperedgesOf(u) ) {
        ++num_pins;
        bool found = false;
        for ( const Pin& p : pinsOf(in_e.e) ) {
          if ( p.pin == u ) {
            found = true;
            break;
          }
        }
        if ( !found ) {
          LOG << "Node" << u << "is not incident to hyperedge" << in_e.e << "!";
          return false;
        }
      }
    }
    if ( num_pins != numPins() ) {
      LOG << "Some incident hyperedges are missing (" << V(num_pins) << V(numPins()) << ")";
      return false;
    }
    return true;
  }(), "Parallel incidence hyperedge construction failed!");

  _finalized = true;
}


void FlowHypergraphBuilder::resizeHyperedgesAndPins(const size_t num_hyperedges,
                                                    const size_t num_pins) {
  ASSERT(num_hyperedges <= hyperedges.size());
  ASSERT(num_pins <= pins.size());
  hyperedges.resize(num_hyperedges);
  pins.resize(num_pins);
}

bool FlowHypergraphBuilder::verifyParallelConstructedHypergraph() {
  size_t num_pins = 0;
  for ( size_t i = 0; i < numNodes(); ++i ) {
    if ( nodes[i].weight == 0 ) {
      LOG << "Node" << i << "has zero weight!";
      return false;
    }
    num_pins += nodes[i].first_out;
  }
  num_pins += nodes.back().first_out; // sentinel

  if ( num_pins != numPins() ) {
    LOG << "[Node Degrees] Expected number of pins =" << numPins() << ", Actual =" << num_pins;
    return false;
  }

  for ( size_t i = 0; i < pins.size(); ++i ) {
    if ( pins[i].pin == whfc::Node::Invalid() ) {
      LOG << "Pin at index" << i << "not assigned";
      return false;
    }
  }

  size_t previous_end = 0;
  num_pins = 0;
  for ( size_t i = 0; i < hyperedges.size() - 1; ++i ) {
    size_t current_start = hyperedges[i].first_out;
    size_t current_end = hyperedges[i+1].first_out;
    if ( current_end - current_start <= 1 ) {
      LOG << "Hyperedge of size one contained";
      return false;
    }

    if ( current_start != previous_end ) {
      LOG << "Gap or intersection in hyperedge incidence array!";
      return false;
    }
    num_pins += ( current_end - current_start );
    previous_end = current_end;
  }

  if ( num_pins != numPins() ) {
    LOG << "[Edge Sizes] Expected number of pins =" << numPins() << ", Actual =" << num_pins;
    return false;
  }

  return true;
}

// ####################### Common Functions #######################

void FlowHypergraphBuilder::clear() {
  _finalized = false;
  _numPinsAtHyperedgeStart = 0;
  maxHyperedgeCapacity = 0;

  nodes.clear();
  hyperedges.clear();
  pins.clear();
  incident_hyperedges.clear();
  total_node_weight = whfc::NodeWeight(0);

  //sentinels
  nodes.push_back({whfc::InHeIndex(0), whfc::NodeWeight(0)});
  hyperedges.push_back({whfc::PinIndex(0), whfc::Flow(0)});
}

}
