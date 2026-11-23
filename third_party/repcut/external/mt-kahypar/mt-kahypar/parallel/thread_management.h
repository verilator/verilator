/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <stddef.h>

namespace mt_kahypar {
namespace parallel {

#ifdef KAHYPAR_DISABLE_HWLOC
static constexpr bool provides_hardware_information = false;
#else
static constexpr bool provides_hardware_information = true;
#endif

// ! Initialize TBB with specified number of threads
void initialize_tbb(const size_t num_threads);

// ! Terminate TBB
void terminate_tbb();

// ! Get number of available threads
int total_number_of_threads();

// ! Get number of actually available CPUs
size_t num_hardware_cpus();

// ! Get number of available numa nodes
int num_used_numa_nodes();

// ! Set membind policy to interleaved allocations on used NUMA nodes
void activate_interleaved_membind_policy();

}  // namespace parallel
}  // namespace mt_kahypar
