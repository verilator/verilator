/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#pragma once

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

template<typename TypeTraits>
class LargeHyperedgeRemover {

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  LargeHyperedgeRemover(const Context& context) :
    _context(context),
    _removed_hes(),
    _removed_single_pin_hes() { }

  LargeHyperedgeRemover(const LargeHyperedgeRemover&) = delete;
  LargeHyperedgeRemover & operator= (const LargeHyperedgeRemover &) = delete;

  LargeHyperedgeRemover(LargeHyperedgeRemover&&) = delete;
  LargeHyperedgeRemover & operator= (LargeHyperedgeRemover &&) = delete;

  // ! Removes single pin and large hyperedges from the hypergraph
  // ! Returns the number of removed large hyperedges.
  HypernodeID removeSinglePinAndLargeHyperedges(Hypergraph& hypergraph) {
    HypernodeID num_removed_large_hyperedges = 0;
    if constexpr ( !Hypergraph::is_graph ) {
      for ( const HyperedgeID& he : hypergraph.edges() ) {
        ASSERT(hypergraph.edgeSize(he) > 0);
        if ( hypergraph.edgeSize(he) == 1 ) {
          hypergraph.removeEdge(he);
          _removed_single_pin_hes.push_back(he);
        } else if ( hypergraph.edgeSize(he) > largeHyperedgeThreshold() ) {
          hypergraph.removeLargeEdge(he);
          _removed_hes.push_back(he);
          ++num_removed_large_hyperedges;
        }
      }
      std::reverse(_removed_hes.begin(), _removed_hes.end());
    }
    return num_removed_large_hyperedges;
  }

  // ! Before we start a v-cycle, we reset the hypergraph data structure.
  // ! This causes that all removed hyperedges in the dynamic hypergraph are
  // ! reinserted to the incident nets of each vertex. By simply calling this
  // ! function, we remove all large hyperedges again.
  void removeLargeHyperedgesInNLevelVCycle(Hypergraph& hypergraph) {
    for ( const HyperedgeID& he : _removed_hes ) {
      hypergraph.enableHyperedge(he);
      hypergraph.removeLargeEdge(he);
    }
    for ( const HyperedgeID& he : _removed_single_pin_hes ) {
      hypergraph.enableHyperedge(he);
      hypergraph.removeEdge(he);
    }
  }

  // ! Restores all previously removed large hyperedges
  void restoreSinglePinAndLargeHyperedges(PartitionedHypergraph& hypergraph) {
    HyperedgeWeight delta = 0;
    for ( const HyperedgeID& he : _removed_hes ) {
      hypergraph.restoreLargeEdge(he);
      delta += metrics::contribution(hypergraph, he, _context.partition.objective);
    }
    for ( const HyperedgeID& he : _removed_single_pin_hes ) {
      hypergraph.restoreSinglePinEdge(he);
    }

    if ( _context.partition.enable_logging && _context.partition.verbose_logging && delta > 0 ) {
      LOG << RED << "Restoring of" << _removed_hes.size() << "large hyperedges (|e| >"
          << largeHyperedgeThreshold() << ") increased" << _context.partition.objective
          << "by" << delta << END;
    }
  }

  HypernodeID largeHyperedgeThreshold() const {
    return std::max(
      _context.partition.large_hyperedge_size_threshold,
      _context.partition.smallest_large_he_size_threshold);
  }

  void reset() {
    _removed_hes.clear();
    _removed_single_pin_hes.clear();
  }

 private:
  const Context& _context;
  parallel::scalable_vector<HypernodeID> _removed_hes;
  parallel::scalable_vector<HypernodeID> _removed_single_pin_hes;
};

}  // namespace mt_kahypar
