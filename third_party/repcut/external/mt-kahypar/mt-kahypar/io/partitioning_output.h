/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#pragma once

#include "mt-kahypar/partition/context.h"

namespace mt_kahypar::io {
  void printStripe();
  void printBanner();
  void printContext(const Context& context);
  void printMemoryPoolConsumption(const Context& context);
  void printCoarseningBanner(const Context& context);
  void printInitialPartitioningBanner(const Context& context);
  void printLocalSearchBanner(const Context& context);
  void printVCycleBanner(const Context& context, const size_t vcycle_num);
  void printDeepMultilevelBanner(const Context& context);
  void printTopLevelPreprocessingBanner(const Context& context);

  template<typename PartitionedHypergraph>
  void printCutMatrix(const PartitionedHypergraph& hypergraph);
  template<typename Hypergraph>
  void printHypergraphInfo(const Hypergraph& hypergraph,
                           const Context& context,
                           const std::string& name,
                           const bool show_memory_consumption);
  template<typename PartitionedHypergraph>
  void printPartitioningResults(const PartitionedHypergraph& hypergraph,
                                const Context& context,
                                const std::string& description);
  template<typename PartitionedHypergraph>
  void printPartitioningResults(const PartitionedHypergraph& hypergraph,
                                const Context& context,
                                const std::chrono::duration<double>& elapsed_seconds);
  template<typename PartitionedHypergraph>
  void printPartWeightsAndSizes(const PartitionedHypergraph& hypergraph, const Context& context);
  template<typename Hypergraph>
  void printFixedVertexPartWeights(const Hypergraph& hypergraph, const Context& context);
  template<typename Hypergraph>
  void printInputInformation(const Context& context, const Hypergraph& hypergraph);
  template<typename Hypergraph>
  void printCommunityInformation(const Hypergraph& hypergraph, const Context& context);
}  // namespace mt_kahypar::io
