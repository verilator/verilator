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

#include <cstdint>
#include <vector>

#include <tbb/parallel_reduce.h>
#include <tbb/blocked_range.h>

#include "mt-kahypar/macros.h"

namespace mt_kahypar {
namespace utils {

template<typename T>
double parallel_stdev(const std::vector<T>& data, const double avg, const size_t n) {
    return std::sqrt(tbb::parallel_reduce(
            tbb::blocked_range<size_t>(UL(0), data.size()), 0.0,
            [&](const tbb::blocked_range<size_t>& range, double init) -> double {
            double tmp_stdev = init;
            for ( size_t i = range.begin(); i < range.end(); ++i ) {
                tmp_stdev += (data[i] - avg) * (data[i] - avg);
            }
            return tmp_stdev;
            }, std::plus<double>()) / ( n- 1 ));
}

template<typename T>
double parallel_avg(const std::vector<T>& data, const size_t n) {
    return tbb::parallel_reduce(
            tbb::blocked_range<size_t>(UL(0), data.size()), 0.0,
            [&](const tbb::blocked_range<size_t>& range, double init) -> double {
            double tmp_avg = init;
            for ( size_t i = range.begin(); i < range.end(); ++i ) {
                tmp_avg += static_cast<double>(data[i]);
            }
            return tmp_avg;
            }, std::plus<double>()) / static_cast<double>(n);
}

template<typename Hypergraph>
static inline double avgHyperedgeDegree(const Hypergraph& hypergraph) {
    if (Hypergraph::is_graph) {
        return 2;
    }
    return static_cast<double>(hypergraph.initialNumPins()) / hypergraph.initialNumEdges();
}

template<typename Hypergraph>
static inline double avgHypernodeDegree(const Hypergraph& hypergraph) {
    return static_cast<double>(hypergraph.initialNumPins()) / hypergraph.initialNumNodes();
}

} // namespace utils
} // namespace mt_kahypar
