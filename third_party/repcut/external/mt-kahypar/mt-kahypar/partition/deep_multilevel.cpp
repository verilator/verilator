/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Nikolai Maas <nikolai.maas@student.kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/partition/deep_multilevel.h"

#include <algorithm>
#include <limits>
#include <vector>

#include <tbb/parallel_for.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/multilevel.h"
#include "mt-kahypar/partition/coarsening/coarsening_commons.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_uncoarsener.h"
#ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
#include "mt-kahypar/partition/coarsening/nlevel/nlevel_uncoarsener.h"
#endif
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/partition/refinement/gains/bipartitioning_policy.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/progress_bar.h"
#include "mt-kahypar/io/partitioning_output.h"

namespace mt_kahypar {

namespace {

static constexpr bool enable_heavy_assert = false;
static constexpr bool debug = false;

template<typename TypeTraits>
struct DeepPartitioningResult {
  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  Hypergraph hypergraph;
  PartitionedHypergraph partitioned_hg;
  PartitionID k;
  bool valid = false;
};

struct OriginalHypergraphInfo {

  // The initial allowed imbalance cannot be used for each bipartition as this could result in an
  // imbalanced k-way partition when performing recursive bipartitioning. We therefore adaptively
  // adjust the allowed imbalance for each bipartition individually based on the adaptive imbalance
  // definition described in our papers.
  double computeAdaptiveEpsilon(const HypernodeWeight current_hypergraph_weight,
                                const PartitionID current_k) const {
    if ( current_hypergraph_weight == 0 ) {
      // In recursive bipartitioning, it can happen that a block becomes too light that
      // all nodes of the block fit into one block in a subsequent bipartitioning step.
      // This will create an empty block, which we fix later in a rebalancing step.
      return 0.0;
    } else {
      double base = ceil(static_cast<double>(original_hypergraph_weight) / original_k)
        / ceil(static_cast<double>(current_hypergraph_weight) / current_k)
        * (1.0 + original_epsilon);
      double adaptive_epsilon = std::min(0.99, std::max(std::pow(base, 1.0 /
        ceil(log2(static_cast<double>(current_k)))) - 1.0,0.0));
      return adaptive_epsilon;
    }
  }

  const HypernodeWeight original_hypergraph_weight;
  const PartitionID original_k;
  const double original_epsilon;
};

// During uncoarsening in the deep multilevel scheme, we recursively bipartition each block of the
// partition until we reach the desired number of blocks. The recursive bipartitioning tree (RBTree)
// contains for each partition information in how many blocks we have to further bipartition each block,
// the range of block IDs in the final partition of each block, and the perfectly balanced and maximum
// allowed block weight for each block.
class RBTree {

 public:
  explicit RBTree(const Context& context) :
    _contraction_limit_multiplier(context.coarsening.contraction_limit_multiplier),
    _desired_blocks(),
    _target_blocks(),
    _perfectly_balanced_weights(),
    _max_part_weights(),
    _partition_to_level() {
    _desired_blocks.emplace_back();
    _desired_blocks[0].push_back(context.partition.k);
    _target_blocks.emplace_back();
    _target_blocks[0].push_back(0);
    _target_blocks[0].push_back(context.partition.k);
    _perfectly_balanced_weights.emplace_back();
    _perfectly_balanced_weights[0].push_back(
      std::accumulate(context.partition.perfect_balance_part_weights.cbegin(),
        context.partition.perfect_balance_part_weights.cend(), 0));
    _max_part_weights.emplace_back();
    _max_part_weights[0].push_back(
      std::accumulate(context.partition.max_part_weights.cbegin(),
        context.partition.max_part_weights.cend(), 0));
    precomputeRBTree(context);
  }

  PartitionID nextK(const PartitionID k) const {
    const PartitionID original_k = _desired_blocks[0][0];
    if ( k < original_k && k != kInvalidPartition ) {
      ASSERT(_partition_to_level.count(k) > 0);
      const size_t level = _partition_to_level.at(k);
      if ( level + 1 < _desired_blocks.size() ) {
        return _desired_blocks[level + 1].size();
      } else {
        return original_k;
      }
    } else {
      return kInvalidPartition;
    }
  }

  PartitionID desiredNumberOfBlocks(const PartitionID current_k,
                                    const PartitionID block) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    ASSERT(block < current_k);
    return _desired_blocks[_partition_to_level.at(current_k)][block];
  }

  std::pair<PartitionID, PartitionID> targetBlocksInFinalPartition(const PartitionID current_k,
                                                                   const PartitionID block) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    ASSERT(block < current_k);
    const vec<PartitionID>& target_blocks =
      _target_blocks[_partition_to_level.at(current_k)];
    return std::make_pair(target_blocks[block], target_blocks[block + 1]);
  }

  HypernodeWeight perfectlyBalancedWeight(const PartitionID current_k,
                                          const PartitionID block) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    ASSERT(block < current_k);
    return _perfectly_balanced_weights[_partition_to_level.at(current_k)][block];
  }

  const std::vector<HypernodeWeight>& perfectlyBalancedWeightVector(const PartitionID current_k) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    return _perfectly_balanced_weights[_partition_to_level.at(current_k)];
  }

  HypernodeWeight maxPartWeight(const PartitionID current_k,
                                const PartitionID block) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    ASSERT(block < current_k);
    return _max_part_weights[_partition_to_level.at(current_k)][block];
  }

  const std::vector<HypernodeWeight>& maxPartWeightVector(const PartitionID current_k) const {
    ASSERT(_partition_to_level.count(current_k) > 0);
    return _max_part_weights[_partition_to_level.at(current_k)];
  }

  PartitionID get_maximum_number_of_blocks(const HypernodeID current_num_nodes) const {
    const int num_levels = _desired_blocks.size();
    for ( int i = num_levels - 1; i >= 0; --i ) {
      const PartitionID k = _desired_blocks[i].size();
      if ( current_num_nodes >= k * _contraction_limit_multiplier ) {
        return k;
      }
    }
    return _desired_blocks.back().size();
  }

  void printRBTree() const {
    for ( size_t level = 0; level < _desired_blocks.size(); ++level ) {
      std::cout << "Level " << (level + 1) << std::endl;
      for ( size_t i = 0; i <  _desired_blocks[level].size(); ++i) {
        std::cout << "(" << _desired_blocks[level][i]
                  << ", [" << _target_blocks[level][i] << "," << _target_blocks[level][i + 1] << "]"
                  << ", " << _perfectly_balanced_weights[level][i]
                  << ", " << _max_part_weights[level][i] << ") ";
      }
      std::cout << std::endl;
    }
  }

 private:
  void precomputeRBTree(const Context& context) {
    auto add_block = [&](const PartitionID k) {
      const PartitionID start = _target_blocks.back().back();
      _desired_blocks.back().push_back(k);
      _target_blocks.back().push_back(start + k);
      const HypernodeWeight perfect_part_weight = std::accumulate(
        context.partition.perfect_balance_part_weights.cbegin() + start,
        context.partition.perfect_balance_part_weights.cbegin() + start + k, 0);
      const HypernodeWeight max_part_weight = std::accumulate(
        context.partition.max_part_weights.cbegin() + start,
        context.partition.max_part_weights.cbegin() + start + k, 0);
      _perfectly_balanced_weights.back().push_back(perfect_part_weight);
      _max_part_weights.back().push_back(max_part_weight);
    };

    int cur_level = 0;
    bool should_continue = true;
    // Simulates recursive bipartitioning
    while ( should_continue ) {
      should_continue = false;
      _desired_blocks.emplace_back();
      _target_blocks.emplace_back();
      _target_blocks.back().push_back(0);
      _perfectly_balanced_weights.emplace_back();
      _max_part_weights.emplace_back();
      for ( size_t i = 0; i < _desired_blocks[cur_level].size(); ++i ) {
        const PartitionID k = _desired_blocks[cur_level][i];
        if ( k > 1 ) {
          const PartitionID k0 = k / 2 + (k % 2);
          const PartitionID k1 = k / 2;
          add_block(k0);
          add_block(k1);
          should_continue |= ( k0 > 1 || k1 > 1 );
        } else {
          add_block(1);
        }
      }
      ++cur_level;
    }

    for ( size_t i = 0; i < _desired_blocks.size(); ++i ) {
      _partition_to_level[_desired_blocks[i].size()] = i;
    }
  }

  const HypernodeID _contraction_limit_multiplier;
  vec<vec<PartitionID>> _desired_blocks;
  vec<vec<PartitionID>> _target_blocks;
  vec<std::vector<HypernodeWeight>> _perfectly_balanced_weights;
  vec<std::vector<HypernodeWeight>> _max_part_weights;
  std::unordered_map<PartitionID, size_t> _partition_to_level;
};

bool disableTimerAndStats(const Context& context) {
  const bool was_enabled_before =
    utils::Utilities::instance().getTimer(context.utility_id).isEnabled();
  if ( context.type == ContextType::main ) {
    utils::Utilities& utils = utils::Utilities::instance();
    parallel::MemoryPool::instance().deactivate_unused_memory_allocations();
    utils.getTimer(context.utility_id).disable();
    utils.getStats(context.utility_id).disable();
  }
  return was_enabled_before;
}

void enableTimerAndStats(const Context& context, const bool was_enabled_before) {
  if ( context.type == ContextType::main && was_enabled_before ) {
    utils::Utilities& utils = utils::Utilities::instance();
    parallel::MemoryPool::instance().activate_unused_memory_allocations();
    utils.getTimer(context.utility_id).enable();
    utils.getStats(context.utility_id).enable();
  }
}

Context setupBipartitioningContext(const Context& context,
                                   const OriginalHypergraphInfo& info,
                                   const PartitionID start_k,
                                   const PartitionID end_k,
                                   const HypernodeWeight total_weight,
                                   const bool is_graph) {
  ASSERT(end_k - start_k >= 2);
  Context b_context(context);

  b_context.partition.k = 2;
  b_context.partition.objective = Objective::cut;
  b_context.partition.gain_policy = is_graph ? GainPolicy::cut_for_graphs : GainPolicy::cut;
  b_context.partition.enable_logging = false;
  b_context.initial_partitioning.mode = Mode::direct;
  b_context.type = ContextType::initial_partitioning;

  if ( b_context.coarsening.deep_ml_contraction_limit_multiplier ==
       std::numeric_limits<HypernodeID>::max() ) {
    b_context.coarsening.deep_ml_contraction_limit_multiplier =
      b_context.coarsening.contraction_limit_multiplier;
  }
  b_context.coarsening.contraction_limit_multiplier =
    b_context.coarsening.deep_ml_contraction_limit_multiplier;
  b_context.refinement = b_context.initial_partitioning.refinement;

  // Setup Part Weights
  const PartitionID k = end_k - start_k;
  const PartitionID k0 = k / 2 + (k % 2 != 0 ? 1 : 0);
  const PartitionID k1 = k / 2;
  ASSERT(k0 + k1 == k);
  if ( context.partition.use_individual_part_weights ) {
    const HypernodeWeight max_part_weights_sum = std::accumulate(
      context.partition.max_part_weights.cbegin() + start_k, context.partition.max_part_weights.cbegin() + end_k, 0);
    const double weight_fraction = total_weight / static_cast<double>(max_part_weights_sum);
    ASSERT(weight_fraction <= 1.0);
    b_context.partition.perfect_balance_part_weights.clear();
    b_context.partition.max_part_weights.clear();
    HypernodeWeight perfect_weight_p0 = 0;
    for ( PartitionID i = start_k; i < start_k + k0; ++i ) {
      perfect_weight_p0 += ceil(weight_fraction * context.partition.max_part_weights[i]);
    }
    HypernodeWeight perfect_weight_p1 = 0;
    for ( PartitionID i = start_k + k0; i < end_k; ++i ) {
      perfect_weight_p1 += ceil(weight_fraction * context.partition.max_part_weights[i]);
    }
    // In the case of individual part weights, the usual adaptive epsilon formula is not applicable because it
    // assumes equal part weights. However, by observing that ceil(current_weight / current_k) is the current
    // perfect part weight and (1 + epsilon)ceil(original_weight / original_k) is the maximum part weight,
    // we can derive an equivalent formula using the sum of the perfect part weights and the sum of the
    // maximum part weights.
    // Note that the sum of the perfect part weights might be unequal to the hypergraph weight due to rounding.
    // Thus, we need to use the former instead of using the hypergraph weight directly, as otherwise it could
    // happen that (1 + epsilon)perfect_part_weight > max_part_weight because of rounding issues.
    const double base = max_part_weights_sum / static_cast<double>(perfect_weight_p0 + perfect_weight_p1);
    b_context.partition.epsilon = total_weight == 0 ? 0 :
      std::min(0.99, std::max(std::pow(base, 1.0 / ceil(log2(static_cast<double>(k)))) - 1.0,0.0));
    b_context.partition.perfect_balance_part_weights.push_back(perfect_weight_p0);
    b_context.partition.perfect_balance_part_weights.push_back(perfect_weight_p1);
    b_context.partition.max_part_weights.push_back(
            round((1 + b_context.partition.epsilon) * perfect_weight_p0));
    b_context.partition.max_part_weights.push_back(
            round((1 + b_context.partition.epsilon) * perfect_weight_p1));
  } else {
    b_context.partition.epsilon = info.computeAdaptiveEpsilon(total_weight, k);

    b_context.partition.perfect_balance_part_weights.clear();
    b_context.partition.max_part_weights.clear();
    b_context.partition.perfect_balance_part_weights.push_back(
            std::ceil(k0 / static_cast<double>(k) * static_cast<double>(total_weight)));
    b_context.partition.perfect_balance_part_weights.push_back(
            std::ceil(k1 / static_cast<double>(k) * static_cast<double>(total_weight)));
    b_context.partition.max_part_weights.push_back(
            (1 + b_context.partition.epsilon) * b_context.partition.perfect_balance_part_weights[0]);
    b_context.partition.max_part_weights.push_back(
            (1 + b_context.partition.epsilon) * b_context.partition.perfect_balance_part_weights[1]);
  }
  b_context.setupContractionLimit(total_weight);
  b_context.setupThreadsPerFlowSearch();

  return b_context;
}

Context setupDeepMultilevelRecursionContext(const Context& context,
                                            const size_t num_threads) {
  Context r_context(context);

  r_context.type = ContextType::initial_partitioning;
  r_context.partition.enable_logging = false;

  const double thread_reduction_factor = static_cast<double>(num_threads) / context.shared_memory.num_threads;
  r_context.shared_memory.num_threads = num_threads;
  r_context.shared_memory.degree_of_parallelism *= thread_reduction_factor;
  r_context.initial_partitioning.runs = std::max(
    std::ceil(static_cast<double>(context.initial_partitioning.runs) *
      thread_reduction_factor), 1.0);

  return r_context;
}

bool usesAdaptiveWeightOfNonCutEdges(const Context& context) {
  return BipartitioningPolicy::nonCutEdgeMultiplier(context.partition.gain_policy) != 1;
}

template<typename Hypergraph>
void adaptWeightsOfNonCutEdges(Hypergraph& hg,
                                const vec<uint8_t>& already_cut,
                                const GainPolicy gain_policy) {
  const HyperedgeWeight multiplier = BipartitioningPolicy::nonCutEdgeMultiplier(gain_policy);
  if ( multiplier != 1 ) {
    ASSERT(static_cast<size_t>(hg.initialNumEdges()) <= already_cut.size());
    hg.doParallelForAllEdges([&](const HyperedgeID& he) {
      if ( !already_cut[he] ) {
        hg.setEdgeWeight(he, multiplier * hg.edgeWeight(he));
      }
    });
  }
}

template<typename PartitionedHypergraph>
void printInitialPartitioningResult(const PartitionedHypergraph& partitioned_hg,
                                    const Context& context,
                                    const PartitionID k,
                                    const RBTree& rb_tree) {
  if ( context.partition.enable_logging ) {
    Context m_context(context);
    m_context.partition.k = k;
    m_context.partition.perfect_balance_part_weights = rb_tree.perfectlyBalancedWeightVector(m_context.partition.k);
    m_context.partition.max_part_weights = rb_tree.maxPartWeightVector(m_context.partition.k);
    io::printPartitioningResults(partitioned_hg, m_context, "Initial Partitioning Results:");
  }
}

template<typename PartitionedHypergraph>
bool is_balanced(const PartitionedHypergraph& partitioned_hg,
                 const PartitionID k,
                 const RBTree& rb_tree) {
  bool isBalanced = true;
  for ( PartitionID i = 0; i < k; ++i ) {
    isBalanced = isBalanced && partitioned_hg.partWeight(i) <= rb_tree.maxPartWeight(k, i);
  }
  return isBalanced;
}

template<typename TypeTraits>
const DeepPartitioningResult<TypeTraits>& select_best_partition(
  const vec<DeepPartitioningResult<TypeTraits>>& partitions,
  const Context& context,
  const PartitionID k,
  const RBTree& rb_tree) {
  vec<HyperedgeWeight> objectives(partitions.size(), 0);
  vec<bool> isBalanced(partitions.size(), false);

  // Compute objective value and perform balance check for each partition
  tbb::task_group tg;
  for ( size_t i = 0; i < partitions.size(); ++i ) {
    tg.run([&, i] {
      objectives[i] = metrics::quality(
        partitions[i].partitioned_hg, context);
      isBalanced[i] = is_balanced(partitions[i].partitioned_hg, k, rb_tree);
    });
  }
  tg.wait();

  // We try to choose a balanced partition with the best objective value
  size_t best_idx = 0;
  for ( size_t i = 1; i < partitions.size(); ++i ) {
    if ( ( isBalanced[i] && !isBalanced[best_idx] ) ||
         ( ( ( !isBalanced[i] && !isBalanced[best_idx] ) ||
             ( isBalanced[i] && isBalanced[best_idx] ) ) &&
           objectives[i] < objectives[best_idx] ) ) {
      best_idx = i;
    }
  }

  return partitions[best_idx];
}

template<typename TypeTraits>
DeepPartitioningResult<TypeTraits> bipartition_block(typename TypeTraits::Hypergraph&& hg,
                                                     const Context& context,
                                                     const OriginalHypergraphInfo& info,
                                                     const PartitionID start_k,
                                                     const PartitionID end_k) {
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  DeepPartitioningResult<TypeTraits> bipartition;
  bipartition.hypergraph = std::move(hg);
  bipartition.valid = true;

  if ( bipartition.hypergraph.initialNumNodes() > 0 ) {
    // Bipartition block
    Context b_context = setupBipartitioningContext(
      context, info, start_k, end_k, bipartition.hypergraph.totalWeight(), PartitionedHypergraph::is_graph);
    bipartition.partitioned_hg = Multilevel<TypeTraits>::partition(
      bipartition.hypergraph, b_context);
  } else {
    bipartition.partitioned_hg = PartitionedHypergraph(2, bipartition.hypergraph, parallel_tag_t());
  }

  return bipartition;
}

template<typename TypeTraits, typename GainCache>
void apply_bipartitions_to_hypergraph(typename TypeTraits::PartitionedHypergraph& partitioned_hg,
                                      GainCache& gain_cache,
                                      const vec<HypernodeID>& mapping,
                                      const vec<DeepPartitioningResult<TypeTraits>>& bipartitions,
                                      const vec<PartitionID>& block_ranges) {
  partitioned_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    const PartitionID from = partitioned_hg.partID(hn);
    ASSERT(static_cast<size_t>(from) < bipartitions.size());
    PartitionID to = kInvalidPartition;
    const DeepPartitioningResult<TypeTraits>& bipartition = bipartitions[from];
    if ( bipartition.valid ) {
      ASSERT(static_cast<size_t>(hn) < mapping.size());
      const HypernodeID mapped_hn = mapping[hn];
      to = bipartition.partitioned_hg.partID(mapped_hn) == 0 ?
        block_ranges[from] : block_ranges[from] + 1;
    } else {
      to = block_ranges[from];
    }

    ASSERT(to > kInvalidPartition && to < block_ranges.back());
    if ( from != to ) {
      if ( gain_cache.isInitialized() ) {
        partitioned_hg.changeNodePart(gain_cache, hn, from, to);
      } else {
        partitioned_hg.changeNodePartNoSync(hn, from, to);
      }
    }
  });
  partitioned_hg.resetEdgeSynchronization();

  if ( GainCache::invalidates_entries && gain_cache.isInitialized() ) {
    partitioned_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
      gain_cache.recomputeInvalidTerms(partitioned_hg, hn);
    });
  }

  HEAVY_REFINEMENT_ASSERT(partitioned_hg.checkTrackedPartitionInformation(gain_cache));
}

template<typename TypeTraits>
void apply_bipartitions_to_hypergraph(typename TypeTraits::PartitionedHypergraph& partitioned_hg,
                                      gain_cache_t gain_cache,
                                      const vec<HypernodeID>& mapping,
                                      const vec<DeepPartitioningResult<TypeTraits>>& bipartitions,
                                      const vec<PartitionID>& block_ranges) {
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  GainCachePtr::applyWithConcreteGainCacheForHG<PartitionedHypergraph>([&](auto& gain_cache) {
    apply_bipartitions_to_hypergraph<TypeTraits>(partitioned_hg,gain_cache, mapping, bipartitions, block_ranges);
  }, gain_cache);
}

template<typename TypeTraits>
void bipartition_each_block(typename TypeTraits::PartitionedHypergraph& partitioned_hg,
                            const Context& context,
                            gain_cache_t gain_cache,
                            const OriginalHypergraphInfo& info,
                            const RBTree& rb_tree,
                            vec<uint8_t>& already_cut,
                            const PartitionID current_k,
                            const HyperedgeWeight current_objective,
                            const bool progress_bar_enabled) {
  using Hypergraph = typename TypeTraits::Hypergraph;
  utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
  // Extract all blocks of hypergraph
  timer.start_timer("extract_blocks", "Extract Blocks");
  const bool cut_net_splitting =
    BipartitioningPolicy::useCutNetSplitting(context.partition.gain_policy);
  if ( !already_cut.empty() ) {
    ASSERT(static_cast<size_t>(partitioned_hg.initialNumEdges()) <= already_cut.size());
    partitioned_hg.doParallelForAllEdges([&](const HyperedgeID he) {
      already_cut[he] = partitioned_hg.connectivity(he) > 1;
    });
  }
  auto extracted_blocks = partitioned_hg.extractAllBlocks(current_k, !already_cut.empty() ?
    &already_cut : nullptr, cut_net_splitting, context.preprocessing.stable_construction_of_incident_edges);
  vec<Hypergraph> hypergraphs(current_k);
  for ( PartitionID block = 0; block < current_k; ++block ) {
    hypergraphs[block] = std::move(extracted_blocks.first[block].hg);
  }
  const vec<HypernodeID>& mapping = extracted_blocks.second;
  timer.stop_timer("extract_blocks");

  timer.start_timer("bipartition_blocks", "Bipartition Blocks");
  const bool was_enabled_before = disableTimerAndStats(context); // n-level disables timer
  utils::ProgressBar progress(current_k, current_objective, progress_bar_enabled);
  vec<DeepPartitioningResult<TypeTraits>> bipartitions(current_k);
  vec<PartitionID> block_ranges(1, 0);
  tbb::task_group tg;
  for ( PartitionID block = 0; block < current_k; ++block ) {
    // The recursive bipartitioning tree stores for each block of the current partition
    // the number of blocks in which we have to further bipartition the corresponding block
    // recursively. This is important for computing the adjusted imbalance factor to ensure
    // that the final k-way partition is balanced.
    const PartitionID desired_blocks = rb_tree.desiredNumberOfBlocks(current_k, block);
    if ( desired_blocks > 1 ) {
      // Spawn a task that bipartitions the corresponding block
      tg.run([&, block] {
        const auto target_blocks = rb_tree.targetBlocksInFinalPartition(current_k, block);
        adaptWeightsOfNonCutEdges(hypergraphs[block],
          extracted_blocks.first[block].already_cut, context.partition.gain_policy);
        bipartitions[block] = bipartition_block<TypeTraits>(std::move(hypergraphs[block]), context,
          info, target_blocks.first, target_blocks.second);
        bipartitions[block].partitioned_hg.setHypergraph(bipartitions[block].hypergraph);
        progress.addToObjective(progress_bar_enabled ?
          metrics::quality(bipartitions[block].partitioned_hg, Objective::cut) : 0 );
        progress += 1;
      });
      block_ranges.push_back(block_ranges.back() + 2);
    } else {
      // No further bipartitions required for the corresponding block
      bipartitions[block].valid = false;
      block_ranges.push_back(block_ranges.back() + 1);
      progress += 1;
    }
  }
  tg.wait();
  enableTimerAndStats(context, was_enabled_before);
  timer.stop_timer("bipartition_blocks");

  timer.start_timer("apply_bipartitions", "Apply Bipartition");
  apply_bipartitions_to_hypergraph(partitioned_hg, gain_cache, mapping, bipartitions, block_ranges);
  timer.stop_timer("apply_bipartitions");

  ASSERT([&] {
    HyperedgeWeight expected_objective = current_objective;
    for ( PartitionID block = 0; block < current_k; ++block ) {
      const PartitionID desired_blocks = rb_tree.desiredNumberOfBlocks(current_k, block);
      if ( desired_blocks > 1 ) {
        expected_objective += metrics::quality(
          bipartitions[block].partitioned_hg, Objective::cut);
      }
    }
    if ( expected_objective != metrics::quality(partitioned_hg, context) ) {
      LOG << V(expected_objective) << V(metrics::quality(partitioned_hg, context));
      return false;
    }
    return true;
  }(), "Cut of extracted blocks does not sum up to current objective");

  timer.start_timer("free_hypergraphs", "Free Hypergraphs");
  tbb::parallel_for(UL(0), bipartitions.size(), [&](const size_t i) {
    DeepPartitioningResult<TypeTraits> tmp_res;
    tmp_res = std::move(bipartitions[i]);
  });
  timer.stop_timer("free_hypergraphs");
}

template<typename TypeTraits>
DeepPartitioningResult<TypeTraits> deep_multilevel_recursion(const typename TypeTraits::Hypergraph& hypergraph,
                                                             const Context& context,
                                                             const OriginalHypergraphInfo& info,
                                                             const RBTree& rb_tree,
                                                             const size_t num_threads);

template<typename TypeTraits>
PartitionID deep_multilevel_partitioning(typename TypeTraits::PartitionedHypergraph& partitioned_hg,
                                         const Context& c,
                                         const OriginalHypergraphInfo& info,
                                         const RBTree& rb_tree) {
  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  Hypergraph& hypergraph = partitioned_hg.hypergraph();
  Context context(c);

  // ################## COARSENING ##################
  mt_kahypar::io::printCoarseningBanner(context);

  // We change the contraction limit to 2C nodes which is the contraction limit where traditional
  // multilevel partitioning bipartitions the smallest hypergraph into two blocks.
  const HypernodeID contraction_limit_for_bipartitioning = 2 * context.coarsening.contraction_limit_multiplier;
  context.coarsening.contraction_limit = contraction_limit_for_bipartitioning;
  PartitionID actual_k = std::max(std::min(static_cast<HypernodeID>(context.partition.k),
    partitioned_hg.initialNumNodes() / context.coarsening.contraction_limit_multiplier), ID(2));
  auto adapt_max_allowed_node_weight = [&](const HypernodeID current_num_nodes, bool& should_continue) {
    // In case our actual k is not two, we check if the current number of nodes is smaller
    // than k * contraction_limit. If so, we increase the maximum allowed node weight.
    while ( ( current_num_nodes <= actual_k * context.coarsening.contraction_limit ||
              !should_continue ) && actual_k > 2 ) {
      actual_k = std::max(actual_k / 2, 2);
      const double hypernode_weight_fraction = context.coarsening.max_allowed_weight_multiplier /
          static_cast<double>(actual_k * context.coarsening.contraction_limit_multiplier);
      context.coarsening.max_allowed_node_weight = std::ceil(hypernode_weight_fraction * hypergraph.totalWeight());
      should_continue = true;
      DBG << "Set max allowed node weight to" << context.coarsening.max_allowed_node_weight
          << "( Current Number of Nodes =" << current_num_nodes << ")";
    }
  };

  const bool nlevel = context.isNLevelPartitioning();
  UncoarseningData<TypeTraits> uncoarseningData(nlevel, hypergraph, context);
  uncoarseningData.setPartitionedHypergraph(std::move(partitioned_hg));

  utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
  bool no_further_contractions_possible = true;
  bool should_continue = true;
  adapt_max_allowed_node_weight(hypergraph.initialNumNodes(), should_continue);
  timer.start_timer("coarsening", "Coarsening");
  {
    std::unique_ptr<ICoarsener> coarsener = CoarsenerFactory::getInstance().createObject(
      context.coarsening.algorithm, utils::hypergraph_cast(hypergraph),
      context, uncoarsening::to_pointer(uncoarseningData));

    // Perform coarsening
    coarsener->initialize();
    int pass_nr = 1;
    // Coarsening proceeds until we reach the contraction limit (!shouldNotTerminate()) or
    // no further contractions are possible (should_continue)
    while ( coarsener->shouldNotTerminate() && should_continue ) {
      DBG << "Coarsening Pass" << pass_nr
          << "- Number of Nodes =" << coarsener->currentNumberOfNodes()
          << "- Number of HEs =" << (nlevel ? 0 :
             utils::cast<Hypergraph>(coarsener->coarsestHypergraph()).initialNumEdges())
          << "- Number of Pins =" << (nlevel ? 0 :
             utils::cast<Hypergraph>(coarsener->coarsestHypergraph()).initialNumPins());

      // In the coarsening phase, we maintain the invariant that t threads process a hypergraph with
      // at least t * C nodes (C = contraction_limit_for_bipartitioning). If this invariant is violated,
      // we terminate coarsening and call the deep multilevel scheme recursively in parallel with the
      // appropriate number of threads to restore the invariant.
      const HypernodeID current_num_nodes = coarsener->currentNumberOfNodes();
      if (  context.partition.perform_parallel_recursion_in_deep_multilevel &&
            current_num_nodes < context.shared_memory.num_threads * contraction_limit_for_bipartitioning ) {
        no_further_contractions_possible = false;
        break;
      }

      should_continue = coarsener->coarseningPass();
      adapt_max_allowed_node_weight(coarsener->currentNumberOfNodes(), should_continue);
      ++pass_nr;
    }
    coarsener->terminate();


    if (context.partition.enable_logging) {
      mt_kahypar_hypergraph_t coarsestHypergraph = coarsener->coarsestHypergraph();
      mt_kahypar::io::printHypergraphInfo(
        utils::cast<Hypergraph>(coarsestHypergraph), context,
        "Coarsened Hypergraph", context.partition.show_memory_consumption);
    }
  }
  timer.stop_timer("coarsening");

  // ################## Initial Partitioning ##################
  io::printInitialPartitioningBanner(context);
  timer.start_timer("initial_partitioning", "Initial Partitioning");
  const bool was_enabled_before = disableTimerAndStats(context);
  PartitionedHypergraph& coarsest_phg = uncoarseningData.coarsestPartitionedHypergraph();
  PartitionID current_k = kInvalidPartition;
  if ( no_further_contractions_possible ) {
    DBG << "Smallest Hypergraph"
        << "- Number of Nodes =" << coarsest_phg.initialNumNodes()
        << "- Number of HEs =" << coarsest_phg.initialNumEdges()
        << "- Number of Pins =" << coarsest_phg.initialNumPins();

    // If we reach the contraction limit, we bipartition the smallest hypergraph
    // and continue with uncoarsening.
    const auto target_blocks = rb_tree.targetBlocksInFinalPartition(1, 0);
    Context b_context = setupBipartitioningContext(
      context, info, target_blocks.first, target_blocks.second,
      hypergraph.totalWeight(), Hypergraph::is_graph);
    Multilevel<TypeTraits>::partition(coarsest_phg, b_context);
    current_k = 2;

    DBG << BOLD << "Peform Initial Bipartitioning" << END
        << "- Objective =" << metrics::quality(coarsest_phg, b_context)
        << "- Imbalance =" << metrics::imbalance(coarsest_phg, b_context)
        << "- Epsilon =" << b_context.partition.epsilon;
  } else {
    // If we do not reach the contraction limit, then the invariant that t threads
    // work on a hypergraph with at least t * C nodes is violated. To restore the
    // invariant, we call the deep multilevel scheme recursively in parallel. Each
    // recursive call is initialized with the appropriate number of threads. After
    // returning from the recursion, we continue uncoarsening with the best partition
    // from the recursive calls.

    // Determine the number of parallel recursive calls and the number of threads
    // used for each recursive call.
    const Hypergraph& coarsest_hg = coarsest_phg.hypergraph();
    const HypernodeID current_num_nodes = coarsest_hg.initialNumNodes();
    size_t num_threads_per_recursion = std::max(current_num_nodes,
      contraction_limit_for_bipartitioning ) / contraction_limit_for_bipartitioning;
    const size_t num_parallel_calls = context.shared_memory.num_threads / num_threads_per_recursion +
      (context.shared_memory.num_threads % num_threads_per_recursion != 0);
    num_threads_per_recursion = context.shared_memory.num_threads / num_parallel_calls +
      (context.shared_memory.num_threads % num_parallel_calls != 0);


    DBG << BOLD << "Perform Parallel Recursion" << END
        << "- Num. Nodes =" << current_num_nodes
        << "- Parallel Calls =" << num_parallel_calls
        << "- Threads Per Call =" << num_threads_per_recursion
        << "- k =" << rb_tree.get_maximum_number_of_blocks(current_num_nodes);

    // Call deep multilevel scheme recursively
    tbb::task_group tg;
    vec<DeepPartitioningResult<TypeTraits>> results(num_parallel_calls);
    for ( size_t i = 0; i < num_parallel_calls; ++i ) {
      tg.run([&, i] {
        const size_t num_threads = std::min(num_threads_per_recursion,
          context.shared_memory.num_threads - i * num_threads_per_recursion);
        results[i] = deep_multilevel_recursion<TypeTraits>(coarsest_hg, context, info, rb_tree, num_threads);
        results[i].partitioned_hg.setHypergraph(results[i].hypergraph);
      });
    }
    tg.wait();

    ASSERT([&] {
      const PartitionID expected_k = results[0].k;
      for ( size_t i = 1; i < num_parallel_calls; ++i ) {
        if ( expected_k != results[i].k ) return false;
      }
      return true;
    }(), "Not all hypergraphs from recursion are partitioned into the same number of blocks!");
    current_k = results[0].k;

    // Apply best bipartition from the recursive calls to the current hypergraph
    const DeepPartitioningResult<TypeTraits>& best = select_best_partition(results, context, current_k, rb_tree);
    const PartitionedHypergraph& best_phg = best.partitioned_hg;
    coarsest_phg.doParallelForAllNodes([&](const HypernodeID& hn) {
      const PartitionID block = best_phg.partID(hn);
      coarsest_phg.setOnlyNodePart(hn, block);
    });
    coarsest_phg.initializePartition();

    DBG << BOLD << "Best Partition from Recursive Calls" << END
        << "- Objective =" << metrics::quality(coarsest_phg, context)
        << "- isBalanced =" << std::boolalpha << is_balanced(coarsest_phg, current_k, rb_tree);
  }
  ASSERT(current_k != kInvalidPartition);

  printInitialPartitioningResult(coarsest_phg, context, current_k, rb_tree);
  if ( context.partition.enable_logging && context.partition.verbose_logging ) {
    utils::Utilities::instance().getInitialPartitioningStats(
      context.utility_id).printInitialPartitioningStats();
  }
  enableTimerAndStats(context, was_enabled_before);
  timer.stop_timer("initial_partitioning");

  // ################## UNCOARSENING ##################
  io::printLocalSearchBanner(context);
  timer.start_timer("refinement", "Refinement");
  const bool progress_bar_enabled = context.partition.enable_logging &&
    context.partition.enable_progress_bar && !debug;
  context.partition.enable_progress_bar = false;
  std::unique_ptr<IUncoarsener<TypeTraits>> uncoarsener(nullptr);
  if (uncoarseningData.nlevel) {
    #ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
      uncoarsener = std::make_unique<NLevelUncoarsener<TypeTraits>>(
        hypergraph, context, uncoarseningData, nullptr);
    #else
      throw InvalidParameterException("NLevel features are deactivated.");
    #endif
  } else {
    uncoarsener = std::make_unique<MultilevelUncoarsener<TypeTraits>>(
      hypergraph, context, uncoarseningData, nullptr);
  }
  uncoarsener->initialize();

  // Determine the current number of blocks (k), the number of blocks in which the
  // hypergraph should be partitioned next (k'), and the contraction limit at which we
  // have to partition the hypergraph into k' blocks (k' * C).
  const PartitionID final_k = context.partition.k;
  PartitionID next_k = kInvalidPartition;
  HypernodeID contraction_limit_for_rb = std::numeric_limits<HypernodeID>::max();
  auto adapt_contraction_limit_for_recursive_bipartitioning = [&](const PartitionID k) {
    current_k = k;
    next_k = rb_tree.nextK(current_k);
    contraction_limit_for_rb = next_k != kInvalidPartition ?
      next_k * context.coarsening.contraction_limit_multiplier :
      std::numeric_limits<HypernodeID>::max();
    context.partition.k = current_k;
    context.partition.perfect_balance_part_weights = rb_tree.perfectlyBalancedWeightVector(current_k);
    context.partition.max_part_weights = rb_tree.maxPartWeightVector(current_k);
    context.setupThreadsPerFlowSearch();
    uncoarsener->updateMetrics();
  };
  adapt_contraction_limit_for_recursive_bipartitioning(current_k);

  // Start uncoarsening
  vec<uint8_t> already_cut(usesAdaptiveWeightOfNonCutEdges(context) ?
    partitioned_hg.initialNumEdges() : 0, 0);
  while ( !uncoarsener->isTopLevel() ) {
    // In the uncoarsening phase, we recursively bipartition each block when
    // the number of nodes gets larger than k' * C.
    while ( uncoarsener->currentNumberOfNodes() >= contraction_limit_for_rb ) {
      PartitionedHypergraph& current_phg = uncoarsener->currentPartitionedHypergraph();
      if ( context.partition.enable_logging && context.partition.verbose_logging && context.type == ContextType::main ) {
        LOG << "Extend number of blocks from" << current_k << "to" << next_k
            << "( Current Number of Nodes =" << current_phg.initialNumNodes() << ")";
      }
      timer.start_timer("bipartitioning", "Bipartitioning");
      bipartition_each_block<TypeTraits>(current_phg, context, uncoarsener->getGainCache(),
        info, rb_tree, already_cut, current_k, uncoarsener->getObjective(), progress_bar_enabled);
      timer.stop_timer("bipartitioning");

      DBG << "Increase number of blocks from" << current_k << "to" << next_k
          << "( Number of Nodes =" << current_phg.initialNumNodes()
          << "- Objective =" << metrics::quality(current_phg, context)
          << "- isBalanced =" << std::boolalpha << is_balanced(current_phg, next_k, rb_tree);

      adapt_contraction_limit_for_recursive_bipartitioning(next_k);
      // Improve partition
      const HyperedgeWeight obj_before = uncoarsener->getObjective();
      uncoarsener->refine();
      const HyperedgeWeight obj_after = uncoarsener->getObjective();
      if ( context.partition.enable_logging && context.partition.verbose_logging && context.type == ContextType::main ) {
        LOG << "Refinement improved" << context.partition.objective
            << "from" << obj_before << "to" << obj_after
            << "( Improvement =" << ((double(obj_before) / obj_after - 1.0) * 100.0) << "% )\n";
      }
    }

    // Perform next uncontraction step and improve solution
    const HyperedgeWeight obj_before = uncoarsener->getObjective();
    uncoarsener->projectToNextLevelAndRefine();
    const HyperedgeWeight obj_after = uncoarsener->getObjective();
    if ( context.partition.enable_logging && context.partition.verbose_logging && context.type == ContextType::main ) {
      LOG << "Refinement after projecting partition to next level improved"
          << context.partition.objective << "from" << obj_before << "to" << obj_after
          << "( Improvement =" << ((double(obj_before) / obj_after - 1.0) * 100.0) << "% )\n";
    }
  }

  // Top-Level Bipartitioning
  // Note that in case we reach the input hypergraph (ContextType::main) and
  // we still did not reach the desired number of blocks, we recursively bipartition
  // each block until the number of blocks equals the desired number of blocks.
  while ( uncoarsener->currentNumberOfNodes() >= contraction_limit_for_rb ||
          ( context.type == ContextType::main && current_k != final_k ) ) {
    PartitionedHypergraph& current_phg = uncoarsener->currentPartitionedHypergraph();
    if ( context.partition.enable_logging && context.partition.verbose_logging && context.type == ContextType::main ) {
      LOG << "Extend number of blocks from" << current_k << "to" << next_k
          << "( Current Number of Nodes =" << current_phg.initialNumNodes() << ")";
    }
    timer.start_timer("bipartitioning", "Bipartitioning");
    bipartition_each_block<TypeTraits>(current_phg, context, uncoarsener->getGainCache(),
      info, rb_tree, already_cut, current_k, uncoarsener->getObjective(), progress_bar_enabled);
    timer.stop_timer("bipartitioning");

    DBG << "Increase number of blocks from" << current_k << "to" << next_k
        << "( Num Nodes =" << current_phg.initialNumNodes()
        << "- Objective =" << metrics::quality(current_phg, context)
        << "- isBalanced =" << std::boolalpha << is_balanced(current_phg, next_k, rb_tree);

    adapt_contraction_limit_for_recursive_bipartitioning(next_k);
    // Improve partition
    const HyperedgeWeight obj_before = uncoarsener->getObjective();
    uncoarsener->refine();
    const HyperedgeWeight obj_after = uncoarsener->getObjective();
    if ( context.partition.enable_logging && context.partition.verbose_logging && context.type == ContextType::main ) {
      LOG << "Refinement improved" << context.partition.objective
          << "from" << obj_before << "to" << obj_after
          << "( Improvement =" << ((double(obj_before) / obj_after - 1.0) * 100.0) << "% )\n";
    }
  }

  if ( context.type == ContextType::main ) {
    // The choice of the maximum allowed node weight and adaptive imbalance ratio should
    // ensure that we find on each level a balanced partition for unweighted inputs. Thus,
    // we do not use rebalancing on each level as in the original deep multilevel algorithm.
    uncoarsener->rebalancing();
  }

  partitioned_hg = uncoarsener->movePartitionedHypergraph();

  io::printPartitioningResults(partitioned_hg, context, "Local Search Results:");
  timer.stop_timer("refinement");

  return current_k;
}

template<typename TypeTraits>
DeepPartitioningResult<TypeTraits> deep_multilevel_recursion(const typename TypeTraits::Hypergraph& hypergraph,
                                                             const Context& context,
                                                             const OriginalHypergraphInfo& info,
                                                             const RBTree& rb_tree,
                                                             const size_t num_threads) {
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  DeepPartitioningResult<TypeTraits> result;
  Context r_context = setupDeepMultilevelRecursionContext(context, num_threads);
  r_context.partition.k = rb_tree.get_maximum_number_of_blocks(hypergraph.initialNumNodes());
  r_context.partition.perfect_balance_part_weights = rb_tree.perfectlyBalancedWeightVector(r_context.partition.k);
  r_context.partition.max_part_weights = rb_tree.maxPartWeightVector(r_context.partition.k);
  // Copy hypergraph
  result.hypergraph = hypergraph.copy(parallel_tag_t());
  result.partitioned_hg = PartitionedHypergraph(
    r_context.partition.k, result.hypergraph, parallel_tag_t());
  result.valid = true;

  // Recursively call deep multilevel partitioning
  result.k = deep_multilevel_partitioning<TypeTraits>(result.partitioned_hg, r_context, info, rb_tree);

  return result;
}

}

template<typename TypeTraits>
typename TypeTraits::PartitionedHypergraph DeepMultilevel<TypeTraits>::partition(
  Hypergraph& hypergraph, const Context& context) {
  // TODO: Memory for partitioned hypergraph is not available at this point
  PartitionedHypergraph partitioned_hypergraph(
    context.partition.k, hypergraph, parallel_tag_t());
  partition(partitioned_hypergraph, context);
  return partitioned_hypergraph;
}

template<typename TypeTraits>
void DeepMultilevel<TypeTraits>::partition(PartitionedHypergraph& hypergraph, const Context& context) {
  RBTree rb_tree(context);
  deep_multilevel_partitioning<TypeTraits>(hypergraph, context,
    OriginalHypergraphInfo { hypergraph.totalWeight(),
      context.partition.k, context.partition.epsilon }, rb_tree);
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(DeepMultilevel)

} // namepace mt_kahypar
