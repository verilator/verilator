/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2025 Daniel Seemaier <daniel.seemaier@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 *all copies or substantial portions of the Software.
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

#include "kahypar-resources/meta/mandatory.h"

#include "include/mtkahypartypes.h"

#include "mt-kahypar/datastructures/partitioned_hypergraph.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/coarsening/i_coarsener.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_coarsener_base.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

template <class TypeTraits = Mandatory>
class DoNothingCoarsener final : public ICoarsener {
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using Hypergraph = typename TypeTraits::Hypergraph;

public:
  DoNothingCoarsener(mt_kahypar_hypergraph_t hypergraph,
                     const Context & /* context */,
                     uncoarsening_data_t *uncoarseningData)
      : _hg(utils::cast<Hypergraph>(hypergraph)),
        _uncoarseningData(
            uncoarsening::to_reference<TypeTraits>(uncoarseningData)) {}

  DoNothingCoarsener(const DoNothingCoarsener &) = delete;
  DoNothingCoarsener(DoNothingCoarsener &&) = delete;
  DoNothingCoarsener &operator=(const DoNothingCoarsener &) = delete;
  DoNothingCoarsener &operator=(DoNothingCoarsener &&) = delete;

  void disableRandomization() const {}

private:
  virtual void initializeImpl() final {}

  virtual bool shouldNotTerminateImpl() const final { return false; }

  virtual bool coarseningPassImpl() final { return false; }

  virtual void terminateImpl() { _uncoarseningData.finalizeCoarsening(); }

  virtual HypernodeID currentNumberOfNodesImpl() const final {
    return _hg.initialNumNodes();
  }

  mt_kahypar_hypergraph_t coarsestHypergraphImpl() final {
    return mt_kahypar_hypergraph_t{
        reinterpret_cast<mt_kahypar_hypergraph_s *>(&_hg), Hypergraph::TYPE};
  }

  mt_kahypar_partitioned_hypergraph_t
  coarsestPartitionedHypergraphImpl() final {
    return mt_kahypar_partitioned_hypergraph_t{
        reinterpret_cast<mt_kahypar_partitioned_hypergraph_s *>(
            _uncoarseningData.partitioned_hg.get()),
        PartitionedHypergraph::TYPE};
  }

  Hypergraph &_hg;
  UncoarseningData<TypeTraits> &_uncoarseningData;
};

} // namespace mt_kahypar
