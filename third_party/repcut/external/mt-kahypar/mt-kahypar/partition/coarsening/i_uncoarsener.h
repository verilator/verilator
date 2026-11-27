/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Noah Wahl <noah.wahl@student.kit.edu>
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

#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"

namespace mt_kahypar {

template<typename TypeTraits>
class IUncoarsener {

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  public:
    IUncoarsener(const IUncoarsener&) = delete;
    IUncoarsener(IUncoarsener&&) = delete;
    IUncoarsener & operator= (const IUncoarsener &) = delete;
    IUncoarsener & operator= (IUncoarsener &&) = delete;

    PartitionedHypergraph&& uncoarsen() {
      initialize();

      while ( !isTopLevel() ) {
        projectToNextLevelAndRefine();
      }

      rebalancing();

      return movePartitionedHypergraph();
    }

    void initialize() {
      initializeImpl();
    }

    bool isTopLevel() const {
      return isTopLevelImpl();
    }

    void projectToNextLevelAndRefine() {
      projectToNextLevelAndRefineImpl();
    }

    void refine() {
      refineImpl();
    }

    void rebalancing() {
      rebalancingImpl();
    }

    gain_cache_t getGainCache() {
      return getGainCacheImpl();
    }

    HyperedgeWeight getObjective() const {
      return getObjectiveImpl();
    }

    void updateMetrics() {
      updateMetricsImpl();
    }

    PartitionedHypergraph& currentPartitionedHypergraph() {
      return currentPartitionedHypergraphImpl();
    }

    HypernodeID currentNumberOfNodes() const {
      return currentNumberOfNodesImpl();
    }

    PartitionedHypergraph&& movePartitionedHypergraph() {
      return movePartitionedHypergraphImpl();
    }

    virtual ~IUncoarsener() = default;

  protected:
    IUncoarsener() = default;

  private:
    virtual void initializeImpl() = 0;
    virtual bool isTopLevelImpl() const = 0;
    virtual void projectToNextLevelAndRefineImpl() = 0;
    virtual void refineImpl() = 0;
    virtual void rebalancingImpl() = 0;
    virtual gain_cache_t getGainCacheImpl() = 0;
    virtual HyperedgeWeight getObjectiveImpl() const = 0;
    virtual void updateMetricsImpl() = 0;
    virtual PartitionedHypergraph& currentPartitionedHypergraphImpl() = 0;
    virtual HypernodeID currentNumberOfNodesImpl() const = 0;
    virtual PartitionedHypergraph&& movePartitionedHypergraphImpl() = 0;
  };
}
