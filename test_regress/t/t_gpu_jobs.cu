// DESCRIPTION: Verilator: GPU DPI functions for t_gpu_jobs
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated_gpu_device.h"

#include <cstdlib>

static __device__ int* g_seeds = nullptr;

static int seedOf(const char* argp) {
    return argp && *argp ? std::atoi(argp + std::strlen("+seed=")) : 1;
}

extern "C" size_t vlGpuDpiCopyBytes() { return sizeof(int); }

extern "C" void vlGpuDpiCopyInit(int copy, int n) {
    static int* s_seedsp = nullptr;
    if (!s_seedsp) {
        cudaMalloc(reinterpret_cast<void**>(&s_seedsp), sizeof(int) * n);
        cudaMemcpyToSymbol(g_seeds, &s_seedsp, sizeof(s_seedsp));
    }
    const int seed = seedOf(VerilatedGpu::jobPlusArg(copy, "seed="));
    cudaMemcpy(s_seedsp + copy, &seed, sizeof(seed), cudaMemcpyHostToDevice);
}

__device__ void job_seed(VlGpuDpiCtx ctx, IData& result) { result = g_seeds[ctx.m_copy]; }

extern "C" int job_seed() { return seedOf(Verilated::commandArgsPlusMatch("seed=")); }
