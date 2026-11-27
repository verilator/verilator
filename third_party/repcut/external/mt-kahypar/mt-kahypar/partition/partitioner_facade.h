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

#include "include/mtkahypartypes.h"

#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

// Forward Declaration
class TargetGraph;

class PartitionerFacade {
 public:
  // ! Partition the hypergraph into a predefined number of blocks
  static mt_kahypar_partitioned_hypergraph_t partition(mt_kahypar_hypergraph_t hypergraph,
                                                       Context& context,
                                                       TargetGraph* target_graph = nullptr);

  // ! Improves a given partition
  static void improve(mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                      Context& context,
                      TargetGraph* target_graph = nullptr);

  // ! Prints timings and metrics to output
  static void printPartitioningResults(const mt_kahypar_partitioned_hypergraph_t phg,
                                       const Context& context,
                                       const std::chrono::duration<double>& elapsed_seconds);

  // ! Prints timings and metrics in CSV file format
  static std::string serializeCSV(const mt_kahypar_partitioned_hypergraph_t phg,
                                  const Context& context,
                                  const std::chrono::duration<double>& elapsed_seconds);

  // ! Prints timings and metrics as a RESULT line parsable by SQL Plot Tools
  // ! https://github.com/bingmann/sqlplot-tools
  static std::string serializeResultLine(const mt_kahypar_partitioned_hypergraph_t phg,
                                         const Context& context,
                                         const std::chrono::duration<double>& elapsed_seconds);

  // ! Writes the partition to the corresponding file
  static void writePartitionFile(const mt_kahypar_partitioned_hypergraph_t phg,
                                 const std::string& filename);
};

}  // namespace mt_kahypar
