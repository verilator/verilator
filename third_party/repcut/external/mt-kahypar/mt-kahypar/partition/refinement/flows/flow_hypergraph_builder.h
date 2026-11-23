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

#pragma once

#include "repcut_serial.h"

#include <atomic>

#include "WHFC/datastructure/flow_hypergraph.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar {

  class FlowHypergraphBuilder : public whfc::FlowHypergraph {

    using TmpPinRange = mutable_range<vec<Pin>>;

    struct TmpCSRBucket {
      TmpCSRBucket() :
        _hes(),
        _pins(),
        _num_hes(0),
        _global_start_he(0),
        _num_pins(0),
        _global_start_pin_idx(0) { }

      void initialize(const size_t num_hes, const size_t num_pins) {
        _hes.clear();
        _pins.clear();
        _hes.resize(num_hes + 1);
        _pins.resize(num_pins);
        _num_hes = whfc::Hyperedge(0);
        _global_start_he = whfc::Hyperedge(0);
        _num_pins = 0;
        _global_start_pin_idx = 0;
      }

      MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::PinIndex pinCount(const whfc::Hyperedge e) {
        ASSERT(e < repcut_serial::Ref(_num_hes.value()).load(std::memory_order_relaxed));
        return _hes[e + 1].first_out - _hes[e].first_out;
      }

      MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::Flow& capacity(const whfc::Hyperedge e) {
        ASSERT(e < repcut_serial::Ref(_num_hes.value()).load(std::memory_order_relaxed));
        return _hes[e].capacity;
      }

      TmpPinRange pinsOf(const whfc::Hyperedge e) {
        ASSERT(e < repcut_serial::Ref(_num_hes.value()).load(std::memory_order_relaxed));
        return TmpPinRange(_pins.begin() + _hes[e].first_out,
          _pins.begin() + _hes[e + 1].first_out);
      }

      MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::Hyperedge originalHyperedgeID(const whfc::Hyperedge& e) {
        ASSERT(e < repcut_serial::Ref(_num_hes.value()).load(std::memory_order_relaxed));
        return _global_start_he + e;
      }

      void addPin(const whfc::Node u, const size_t pin_idx) {
        ASSERT(pin_idx < _pins.size());
        ASSERT(pin_idx == _num_pins);
        _pins[pin_idx].pin = u;
        ++_num_pins;
      }

      void finishHyperedge(const whfc::Hyperedge he, const whfc::Flow capacity,
                            const size_t pin_start_idx, const size_t pin_end_idx) {
        ASSERT(he == _num_hes);
        ASSERT(static_cast<size_t>(he + 1) < _hes.size());
        ASSERT(pin_end_idx <= _pins.size());
        ASSERT(pin_end_idx == _num_pins);
        _hes[he].capacity = capacity;
        _hes[he].first_out = whfc::PinIndex(pin_start_idx);
        _hes[he + 1].first_out = whfc::PinIndex(pin_end_idx);

        #ifdef KAHYPAR_USE_ASSERTIONS
        // with assertions, the addition needs to be atomic since the value
        // is used in assertions by other threads
        repcut_serial::Ref(_num_hes.value()).fetch_add(1, std::memory_order_relaxed);
        #else
        ++_num_hes;
        #endif
      }

      void finalize() {
        _hes.resize(_num_hes + 1);
        _pins.resize(_num_pins);
      }

      void copyDataToFlowHypergraph(std::vector<FlowHypergraph::HyperedgeData>& hyperedges,
                                    std::vector<FlowHypergraph::Pin>& pins) {
        if ( _num_hes > 0 ) {
          const size_t num_hes = static_cast<size_t>(_num_hes);
          for ( size_t i = 0; i < num_hes; ++i ) {
            _hes[i].first_out += static_cast<whfc::PinIndex::ValueType>(_global_start_pin_idx);
          }
          const size_t he_start = static_cast<size_t>(_global_start_he);
          std::memcpy(hyperedges.data() + he_start,
                      _hes.data(), sizeof(FlowHypergraph::HyperedgeData) * num_hes);
        }
        if ( _num_pins > 0 ) {
          std::memcpy(pins.data() + _global_start_pin_idx,
                      _pins.data(), sizeof(FlowHypergraph::Pin) * _num_pins);
        }
      }

      vec<FlowHypergraph::HyperedgeData> _hes;
      vec<FlowHypergraph::Pin> _pins;
      whfc::Hyperedge _num_hes;
      whfc::Hyperedge _global_start_he;
      size_t _num_pins;
      size_t _global_start_pin_idx;
    };

  public:
    using Base = whfc::FlowHypergraph;

    FlowHypergraphBuilder() :
      Base(),
      _finalized(false),
      _numPinsAtHyperedgeStart(0),
      _tmp_csr_buckets(),
      _inc_he_pos() {
      clear();
    }

    explicit FlowHypergraphBuilder(size_t num_nodes) :
      Base(),
      _finalized(false),
      _numPinsAtHyperedgeStart(0),
      _tmp_csr_buckets(),
      _inc_he_pos() {
      reinitialize(num_nodes);
    }

    // ####################### Sequential Construction #######################

    void addNode(const whfc::NodeWeight w) {
      nodes.back().weight = w;
      nodes.push_back({whfc::InHeIndex(0), whfc::NodeWeight(0)});
    }

    void startHyperedge(const whfc::Flow capacity) {
      finishHyperedge();	//finish last hyperedge
      hyperedges.back().capacity = capacity;	//exploit sentinel
      _numPinsAtHyperedgeStart = numPins();
      maxHyperedgeCapacity = std::max(maxHyperedgeCapacity, capacity);
    }

    void addPin(const whfc::Node u) {
      assert(u < numNodes());
      pins.push_back({u, whfc::InHeIndex::Invalid()});
      nodes[u+1].first_out++;
    }

    size_t currentHyperedgeSize() const {
      return numPins() - _numPinsAtHyperedgeStart;
    }

    void removeCurrentHyperedge() {
      while (numPins() > _numPinsAtHyperedgeStart) {
        removeLastPin();
      }
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::Flow& capacity(const whfc::Hyperedge e) {
      ASSERT(e < hyperedges.size());
      return hyperedges[e].capacity;
    }

    void finalize();

    // ####################### Parallel Construction #######################

    void allocateNodes(const size_t num_nodes) {
      nodes.assign(num_nodes + 1, NodeData { whfc::InHeIndex(0), whfc::NodeWeight(0) });
    }

    void resizeNodes(const size_t num_nodes) {
      ASSERT(num_nodes <= numNodes());
      nodes.resize(num_nodes + 1);
    }

    void allocateHyperedgesAndPins(const size_t num_hyperedges,
                                   const size_t num_pins);

    void setNumCSRBuckets(const size_t num_buckets) {
      _tmp_csr_buckets.resize(num_buckets);
    }

    void initializeCSRBucket(const size_t bucket, const size_t num_hes, const size_t num_pins) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      _tmp_csr_buckets[bucket].initialize(num_hes, num_pins);
    }

    void finalizeCSRBucket(const size_t bucket) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      _tmp_csr_buckets[bucket].finalize();
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::PinIndex tmpPinCount(const size_t bucket, const whfc::Hyperedge e) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      return _tmp_csr_buckets[bucket].pinCount(e);
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::Flow& capacity(const size_t bucket, const whfc::Hyperedge e) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      return _tmp_csr_buckets[bucket].capacity(e);
    }

    TmpPinRange tmpPinsOf(const size_t bucket, const whfc::Hyperedge e) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      return _tmp_csr_buckets[bucket].pinsOf(e);
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE whfc::Hyperedge originalHyperedgeID(const size_t bucket, const whfc::Hyperedge& e) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      return _tmp_csr_buckets[bucket].originalHyperedgeID(e);
    }

    void addPin(const whfc::Node u, const size_t bucket, const size_t pin_idx) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      ASSERT(static_cast<size_t>(u) < numNodes());
      _tmp_csr_buckets[bucket].addPin(u, pin_idx);
      repcut_serial::Ref(nodes[u + 1].first_out.value()).fetch_add(1, std::memory_order_relaxed);
    }

    void finishHyperedge(const whfc::Hyperedge he, const whfc::Flow capacity,
                         const size_t bucket, const size_t pin_start_idx, const size_t pin_end_idx) {
      ASSERT(bucket < _tmp_csr_buckets.size());
      _tmp_csr_buckets[bucket].finishHyperedge(he, capacity, pin_start_idx, pin_end_idx);
    }

    void finalizeHyperedges();

    void finalizeParallel();

    // ####################### Common Functions #######################

    void clear();

    void reinitialize(size_t num_nodes) {
      clear();
      nodes.resize(num_nodes + 1);
    }

    void shrink_to_fit() {
      nodes.shrink_to_fit();
      hyperedges.shrink_to_fit();
      pins.shrink_to_fit();
      incident_hyperedges.shrink_to_fit();
    }

  private:

    // ####################### Sequential Construction #######################

    void removeLastPin() {
      nodes[ pins.back().pin + 1 ].first_out--;
      pins.pop_back();
    }

    bool finishHyperedge();

    // ####################### Parallel Construction #######################

    void resizeHyperedgesAndPins(const size_t num_hyperedges,
                                 const size_t num_pins);

    bool verifyParallelConstructedHypergraph();

    bool _finalized;
    size_t _numPinsAtHyperedgeStart;

    vec<TmpCSRBucket> _tmp_csr_buckets;
    vec<uint32_t> _inc_he_pos;
  };
}
