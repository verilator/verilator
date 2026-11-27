/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "kahypar-resources/meta/typelist.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_gain_cache.h"
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_gain_cache.h"
#endif
#ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
#include "mt-kahypar/partition/refinement/gains/cut_for_graphs/cut_gain_cache_for_graphs.h"
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_gain_cache_for_graphs.h"
#endif
#endif
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

struct gain_cache_s;
typedef struct  {
  gain_cache_s* gain_cache;
  GainPolicy type;
} gain_cache_t;

class GainCachePtr {

 public:
  template<typename F>
  static auto applyWithConcreteGainCache(F function, gain_cache_t gain_cache) {
    switch(gain_cache.type) {
      case GainPolicy::cut:
        return function(cast<CutGainCache>(gain_cache));
      case GainPolicy::km1:
        return function(cast<Km1GainCache>(gain_cache));
      case GainPolicy::soed:
      #ifdef KAHYPAR_ENABLE_SOED_METRIC
        return function(cast<SoedGainCache>(gain_cache));
      #endif
      case GainPolicy::steiner_tree:
      #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
        return function(cast<SteinerTreeGainCache>(gain_cache));
      #endif
      case GainPolicy::cut_for_graphs:
      #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
        return function(cast<GraphCutGainCache>(gain_cache));
      #endif
      case GainPolicy::steiner_tree_for_graphs:
      #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
      #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
        return function(cast<GraphSteinerTreeGainCache>(gain_cache));
      #endif
      #endif
      case GainPolicy::none: break;
    }
    throw InvalidParameterException("No gain policy set");
  }

  template<typename Hypergraph, typename F>
  static auto applyWithConcreteGainCacheForHG(F function, gain_cache_t gain_cache) {
    if constexpr (Hypergraph::is_graph) {
      switch(gain_cache.type) {
        #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
        case GainPolicy::cut_for_graphs:
          return function(cast<GraphCutGainCache>(gain_cache));
        #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
        case GainPolicy::steiner_tree_for_graphs:
          return function(cast<GraphSteinerTreeGainCache>(gain_cache));
        #endif
        #endif
        default: break;
      }
    } else {
      switch(gain_cache.type) {
        case GainPolicy::cut:
          return function(cast<CutGainCache>(gain_cache));
        case GainPolicy::km1:
          return function(cast<Km1GainCache>(gain_cache));
        #ifdef KAHYPAR_ENABLE_SOED_METRIC
        case GainPolicy::soed:
          return function(cast<SoedGainCache>(gain_cache));
        #endif
        #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
        case GainPolicy::steiner_tree:
          return function(cast<SteinerTreeGainCache>(gain_cache));
        #endif
        default: break;
      }
    }
    throw InvalidParameterException("No gain policy set");
  }

  static gain_cache_t constructGainCache(const Context& context) {
    switch(context.partition.gain_policy) {
      case GainPolicy::cut: return constructGainCache<CutGainCache>(context);
      case GainPolicy::km1: return constructGainCache<Km1GainCache>(context);
      #ifdef KAHYPAR_ENABLE_SOED_METRIC
      case GainPolicy::soed: return constructGainCache<SoedGainCache>(context);
      #endif
      #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
      case GainPolicy::steiner_tree: return constructGainCache<SteinerTreeGainCache>(context);
      #endif
      ENABLE_GRAPHS(case GainPolicy::cut_for_graphs: return constructGainCache<GraphCutGainCache>(context);)
      #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
      ENABLE_GRAPHS(case GainPolicy::steiner_tree_for_graphs: return constructGainCache<GraphSteinerTreeGainCache>(context);)
      #endif
      case GainPolicy::none:
        throw InvalidParameterException("No gain policy set");
      default: break;
    }
    return gain_cache_t { nullptr, GainPolicy::none };
  }

  static void deleteGainCache(gain_cache_t gain_cache) {
    if (gain_cache.type != GainPolicy::none) {
      applyWithConcreteGainCache([&](auto& gc) { delete &gc; }, gain_cache);
    }
  }

  template<typename PartitionedHypergraph>
  static void initializeGainCache(const PartitionedHypergraph& partitioned_hg,
                                  gain_cache_t gain_cache) {
    if (gain_cache.type != GainPolicy::none) {
      applyWithConcreteGainCacheForHG<PartitionedHypergraph>([&](auto& gc) {
        gc.initializeGainCache(partitioned_hg);
      }, gain_cache);
    }
  }

  static void resetGainCache(gain_cache_t gain_cache, HypernodeID num_nodes, PartitionID k) {
    if (gain_cache.type != GainPolicy::none) {
      applyWithConcreteGainCache([&](auto& gc) { gc.reset(num_nodes, k); }, gain_cache);
    }
  }

  template<typename PartitionedHypergraph>
  static void uncontract(PartitionedHypergraph& partitioned_hg,
                         const Batch& batch,
                         gain_cache_t gain_cache) {
    if (gain_cache.type != GainPolicy::none) {
      applyWithConcreteGainCacheForHG<PartitionedHypergraph>([&](auto& gc) {
        partitioned_hg.uncontract(batch, gc);
      }, gain_cache);
    }
  }

  template<typename PartitionedHypergraph, typename ParallelHyperedge>
  static void restoreSinglePinAndParallelNets(PartitionedHypergraph& partitioned_hg,
                                              const vec<ParallelHyperedge>& hes_to_restore,
                                              gain_cache_t gain_cache) {
    if (gain_cache.type != GainPolicy::none) {
      applyWithConcreteGainCacheForHG<PartitionedHypergraph>([&](auto& gc) {
        partitioned_hg.restoreSinglePinAndParallelNets(hes_to_restore, gc);
      }, gain_cache);
    }
  }

  template<typename PartitionedHypergraph>
  static bool checkTrackedPartitionInformation(PartitionedHypergraph& partitioned_hg,
                                               gain_cache_t gain_cache) {
    return applyWithConcreteGainCacheForHG<PartitionedHypergraph>([&](auto& gc) {
      return partitioned_hg.checkTrackedPartitionInformation(gc);
    }, gain_cache);
  }

  template<typename GainCache>
  static GainCache& cast(gain_cache_t gain_cache) {
    if ( gain_cache.type != GainCache::TYPE ) {
      std::stringstream ss;
      ss << "Cannot cast " << gain_cache.type << " to " << GainCache::TYPE;
      throw InvalidInputException(ss.str());
    }
    return *reinterpret_cast<GainCache*>(gain_cache.gain_cache);
  }

 private:
  template<typename GainCache>
  static gain_cache_t constructGainCache(const Context& context) {
    return gain_cache_t { reinterpret_cast<gain_cache_s*>(new GainCache(context)), GainCache::TYPE };
  }
};

}  // namespace mt_kahypar
