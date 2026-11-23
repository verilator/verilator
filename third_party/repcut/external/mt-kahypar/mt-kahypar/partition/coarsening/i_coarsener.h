/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2014 Sebastian Schlag <sebastian.schlag@kit.edu>
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

#include <string>

#include "include/mtkahypartypes.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/coarsening/coarsening_commons.h"

namespace mt_kahypar {

class ICoarsener {

 public:
  ICoarsener(const ICoarsener&) = delete;
  ICoarsener(ICoarsener&&) = delete;
  ICoarsener & operator= (const ICoarsener &) = delete;
  ICoarsener & operator= (ICoarsener &&) = delete;

  void coarsen() {
    initialize();
    bool should_continue = true;
    // Coarsening algorithms proceed in passes where each pass computes a clustering
    // of the nodes and subsequently contracts it. Each pass induces one level of the
    // hierarchy. The coarsening algorithms proceeds until the number of nodes equals
    // a predefined contraction limit (!shouldNotTerminate) or the number of nodes could
    // not be significantly reduced within one coarsening pass (should_continue).
    while ( shouldNotTerminate() && should_continue ) {
      should_continue = coarseningPass();
    }
    terminate();
  }

  void initialize() {
    initializeImpl();
  }

  bool shouldNotTerminate() const {
    return shouldNotTerminateImpl();
  }

  bool coarseningPass() {
    return coarseningPassImpl();
  }

  void terminate() {
    terminateImpl();
  }

  HypernodeID currentNumberOfNodes() const {
    return currentNumberOfNodesImpl();
  }

  mt_kahypar_hypergraph_t coarsestHypergraph() {
    return coarsestHypergraphImpl();
  }

  mt_kahypar_partitioned_hypergraph_t coarsestPartitionedHypergraph() {
    return coarsestPartitionedHypergraphImpl();
  }

  virtual ~ICoarsener() = default;

 protected:
  ICoarsener() = default;

 private:
  virtual void initializeImpl() = 0;
  virtual bool shouldNotTerminateImpl() const = 0;
  virtual bool coarseningPassImpl() = 0;
  virtual void terminateImpl() = 0;
  virtual HypernodeID currentNumberOfNodesImpl() const = 0;
  virtual mt_kahypar_hypergraph_t coarsestHypergraphImpl() = 0;
  virtual mt_kahypar_partitioned_hypergraph_t coarsestPartitionedHypergraphImpl() = 0;
};

}  // namespace kahypar
