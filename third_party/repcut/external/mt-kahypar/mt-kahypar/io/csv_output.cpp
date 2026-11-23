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

#include "csv_output.h"

#include <sstream>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/utils/initial_partitioning_stats.h"
#include "mt-kahypar/utils/stats.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/utilities.h"

namespace mt_kahypar::io::csv {

  std::string header() {
    return "algorithm,threads,graph,k,seed,epsilon,imbalance,"
           "objective,km1,cut,initial_km1,partitionTime,fmTime,lpTime,coarseningTime,ipTime,preprocessingTime"
           "\n";
  }

  template<typename PartitionedHypergraph>
  std::string serialize(const PartitionedHypergraph& phg,
                        const Context& context,
                        const std::chrono::duration<double>& elapsed_seconds) {
    const char sep = ',';
    std::stringstream s;

    s << context.algorithm_name;
    if (context.algorithm_name == "MT-KaHyPar") {
      if (context.partition.preset_file.find("fast") != std::string::npos) {
        s << "-Fast";
      } else if (context.partition.preset_file.find("quality") != std::string::npos) {
        s << "-Eco";
      }
    }
    s << sep;

    s << context.shared_memory.num_threads << sep;
    s << context.partition.graph_filename.substr(context.partition.graph_filename.find_last_of('/') + 1) << sep;
    s << context.partition.k << sep;
    s << context.partition.seed << sep;

    s << context.partition.epsilon << sep;
    s << metrics::imbalance(phg, context).imbalance_value << sep;

    s << context.partition.objective << sep;
    s << metrics::quality(phg, Objective::km1) << sep;
    s << metrics::quality(phg, Objective::cut) << sep;
    s << context.initial_km1 << sep;
    s << elapsed_seconds.count() << sep;

    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.showDetailedTimings(context.partition.show_detailed_timings);
    s << (timer.get("fm") + timer.get("initialize_fm_refiner"))<< sep;
    s << (timer.get("label_propagation") + timer.get("initialize_lp_refiner")) << sep;
    s << timer.get("coarsening") << sep;
    s << timer.get("initial_partitioning") << sep;
    s << timer.get("preprocessing");

    return s.str();
  }

  namespace {
  #define SERIALIZE(X) std::string serialize(const X& phg,                                          \
                                             const Context& context,                                \
                                             const std::chrono::duration<double>& elapsed_seconds)
  }

  INSTANTIATE_FUNC_WITH_PARTITIONED_HG(SERIALIZE)
}