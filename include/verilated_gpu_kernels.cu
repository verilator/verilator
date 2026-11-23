// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief GPU runtime: device kernels
///
//=============================================================================

#include "verilated_gpu.h"
#include "verilated_gpu_device.h"

#include <cuda_runtime.h>

static __global__ void vlGpuProbeKernel(int* outp) { *outp = 1; }

extern "C" int vlGpuProbe() {
    int* devp = nullptr;
    if (cudaMalloc(&devp, sizeof(int)) != cudaSuccess) return -1;
    vlGpuProbeKernel<<<1, 1>>>(devp);
    int host = 0;
    const cudaError_t err = cudaMemcpy(&host, devp, sizeof(int), cudaMemcpyDeviceToHost);
    cudaFree(devp);
    if (err != cudaSuccess) return -2;
    return host == 1 ? 0 : -3;
}

static __global__ void vlGpuScatterKernel(const uint8_t* aosp, uint8_t* soap, int n, int copy,
                                          const VlGpuCopy* tablep, int count, size_t stride,
                                          int mode) {
    const int member = blockIdx.x;
    if (member >= count) return;
    const VlGpuCopy entry = tablep[member];
    const uint8_t* const fromp = aosp + entry.m_state;
    const int first = copy < 0 ? 0 : copy;
    const int last = copy < 0 ? n : copy + 1;
    for (int i = first + threadIdx.x; i < last; i += blockDim.x) {
        const size_t copy = static_cast<size_t>(i);
        uint8_t* const top
            = mode == 1   ? soap + copy * stride + entry.m_state
              : mode == 2 ? soap + (copy / VL_GPU_LAYOUT_GROUP) * VL_GPU_LAYOUT_GROUP * stride
                                + VL_GPU_LAYOUT_GROUP * entry.m_state
                                + (copy % VL_GPU_LAYOUT_GROUP) * entry.m_size
                          : soap + static_cast<size_t>(n) * entry.m_state + copy * entry.m_size;
        for (size_t b = 0; b < entry.m_size; ++b) top[b] = fromp[b];
    }
}

extern "C" int vlGpuScatter(const void* aosp, void* soap, int n, int copy, const void* tablep,
                            int count, size_t stride, int mode) {
    if (count <= 0) return 0;
    vlGpuScatterKernel<<<count, 128>>>(static_cast<const uint8_t*>(aosp),
                                       static_cast<uint8_t*>(soap), n, copy,
                                       static_cast<const VlGpuCopy*>(tablep), count, stride, mode);
    return cudaDeviceSynchronize() == cudaSuccess ? 0 : -1;
}

__device__ unsigned int vlGpuDeferPending = 0;
__device__ uint64_t vlGpuNow = 0;

extern "C" int vlGpuNowWrite(uint64_t now) {
    return cudaMemcpyToSymbol(vlGpuNow, &now, sizeof(now)) == cudaSuccess ? 0 : -1;
}

extern "C" int vlGpuNowRead(uint64_t* nowp) {
    return cudaMemcpyFromSymbol(nowp, vlGpuNow, sizeof(*nowp)) == cudaSuccess ? 0 : -1;
}
__device__ VlGpuAssertCtl vlGpuAssertCtlState;

extern "C" int vlGpuAssertCtlUpload(const void* ctlp) {
    return cudaMemcpyToSymbol(vlGpuAssertCtlState, ctlp, sizeof(VlGpuAssertCtl)) == cudaSuccess
               ? 0
               : -1;
}

static __global__ void vlGpuCheckKernel(const uint8_t* soap, int n, const VlGpuCopy* tablep,
                                        int count, uint8_t* leaderp, unsigned int* statusp,
                                        int check, int leader, const uint8_t* activep) {
    const int member = blockIdx.x;
    if (member >= count) return;
    const VlGpuCopy entry = tablep[member];
    const uint8_t* const basep = soap + static_cast<size_t>(n) * entry.m_state;
    const uint8_t* const firstp = basep + static_cast<size_t>(leader) * entry.m_size;
    if (threadIdx.x == 0) {
        for (size_t b = 0; b < entry.m_size; ++b) leaderp[entry.m_state + b] = firstp[b];
    }
    for (int i = threadIdx.x; check && i < n; i += blockDim.x) {
        if (i == leader || !activep[i]) continue;
        const uint8_t* const cp = basep + static_cast<size_t>(i) * entry.m_size;
        for (size_t b = 0; b < entry.m_size; ++b) {
            if (cp[b] != firstp[b]) {
                atomicOr(&statusp[1], 1U);
                atomicMin(&statusp[2], static_cast<unsigned int>(i));
                break;
            }
        }
    }
    if (member == 0 && threadIdx.x == 0) statusp[0] = vlGpuDeferPending;
}

extern "C" int vlGpuBroadcastAsync(const void* aosp, void* soap, int n, const void* tablep,
                                   int count) {
    if (count <= 0) return 0;
    vlGpuScatterKernel<<<count, 128>>>(static_cast<const uint8_t*>(aosp),
                                       static_cast<uint8_t*>(soap), n, -1,
                                       static_cast<const VlGpuCopy*>(tablep), count, 0, 0);
    return cudaGetLastError() == cudaSuccess ? 0 : -1;
}

static __global__ void vlGpuStatusInit(unsigned int* statusp) {
    statusp[0] = 0;
    statusp[1] = 0;
    statusp[2] = 0xffffffffU;
}

extern "C" int vlGpuCheckAsync(const void* soap, int n, const void* tablep, int count,
                               void* leaderp, void* statusp, int check, int leader,
                               const void* activep) {
    vlGpuStatusInit<<<1, 1>>>(static_cast<unsigned int*>(statusp));
    if (count > 0) {
        vlGpuCheckKernel<<<count, 128>>>(
            static_cast<const uint8_t*>(soap), n, static_cast<const VlGpuCopy*>(tablep), count,
            static_cast<uint8_t*>(leaderp), static_cast<unsigned int*>(statusp), check, leader,
            static_cast<const uint8_t*>(activep));
    } else {
        unsigned int pending = 0;
        if (cudaMemcpyFromSymbol(&pending, vlGpuDeferPending, sizeof(pending)) != cudaSuccess)
            return -1;
        if (cudaMemcpy(statusp, &pending, sizeof(pending), cudaMemcpyHostToDevice) != cudaSuccess)
            return -1;
    }
    return cudaGetLastError() == cudaSuccess ? 0 : -1;
}

extern "C" int vlGpuDeferPendingReset() {
    const unsigned int zero = 0;
    return cudaMemcpyToSymbol(vlGpuDeferPending, &zero, sizeof(zero)) == cudaSuccess ? 0 : -1;
}
