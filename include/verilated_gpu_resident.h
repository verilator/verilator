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
/// \brief GPU runtime: resident scheduler kernel
///
//=============================================================================

#ifndef VERILATOR_VERILATED_GPU_RESIDENT_H_
#define VERILATOR_VERILATED_GPU_RESIDENT_H_

#include "verilated_gpu_device.h"
#include "verilated_gpu_resident_ctl.h"

#include <cooperative_groups.h>

#include <cuda/atomic>

extern __device__ uint64_t vlGpuNow;
static __device__ uint32_t* vlGpuFlowFlags = nullptr;

namespace vlgpures {

namespace cg = cooperative_groups;

__device__ __forceinline__ uint64_t globalTimer() {
    uint64_t t;
    asm volatile("mov.u64 %0, %%globaltimer;" : "=l"(t));
    return t;
}

template <typename T_Model>
class Driver final {
    cg::grid_group m_grid;  // Cooperative grid, for grid-wide barriers
    uint8_t* const m_basep;  // GPU state of all copies
    const int m_n;  // Number of copies
    const uint8_t* const m_activep;  // Per copy: slot holds a running job
    VlGpuResidentCtl* const m_ctlp;  // Control block shared with the host
    const int m_tid;  // Global thread index
    const int m_threads;  // Threads in the grid
    const int m_ctlBlocks;  // Blocks that run the scheduler for copies
    const int m_ctlThreads;  // Threads in those blocks
    uint32_t m_k = 0;  // Rotation counter of the flag reduction slots
    uint32_t m_kMin = 0;  // Rotation counter of the time reduction slots

    __device__ VlGpuView view(int i) const {
#if defined(VL_GPU_LAYOUT_AOS)
        return VlGpuView{m_basep + static_cast<size_t>(i) * T_Model::STRIDE,
                         static_cast<uint32_t>(m_n), static_cast<uint32_t>(i)};
#elif defined(VL_GPU_LAYOUT_AOSOA)
        return VlGpuView{m_basep
                             + static_cast<size_t>(i / VL_GPU_LAYOUT_GROUP) * VL_GPU_LAYOUT_GROUP
                                   * T_Model::STRIDE,
                         static_cast<uint32_t>(m_n), static_cast<uint32_t>(i)};
#else
        return VlGpuView{m_basep, static_cast<uint32_t>(m_n), static_cast<uint32_t>(i)};
#endif
    }

    __device__ bool hasWorkers() const { return m_ctlBlocks < static_cast<int>(gridDim.x); }

    __device__ void ctlSync() {
        if (!hasWorkers()) {
            m_grid.sync();
            return;
        }
        if (m_ctlBlocks == 1) {
            __syncthreads();
            return;
        }
        __syncthreads();
        if (threadIdx.x == 0) {
            volatile uint32_t* const genp = &m_ctlp->m_barGen;
            const uint32_t gen = *genp;
            __threadfence();
            if (atomicAdd(&m_ctlp->m_barCount, 1U) == static_cast<uint32_t>(m_ctlBlocks - 1)) {
                m_ctlp->m_barCount = 0;
                __threadfence();
                atomicAdd(&m_ctlp->m_barGen, 1U);
            } else {
                while (*genp == gen) __nanosleep(32);
            }
            __threadfence();
        }
        __syncthreads();
    }

    static constexpr uint32_t CMD_EXIT = ~0U;

    __device__ void runCommand(uint32_t cmd) {
        const int graph = static_cast<int>(cmd & 0xffffU);
        if ((cmd >> 16) == 1U) {
            runGraphFlow(graph);
        } else {
            runGraph(graph);
        }
    }

    __device__ void postCommand(uint32_t cmd) {
        __threadfence();
        ctlSync();
        if (m_tid == 0) {
            m_ctlp->m_cmd = cmd;
            cuda::atomic_ref<uint32_t, cuda::thread_scope_device> gen{m_ctlp->m_cmdGen};
            gen.fetch_add(1U, cuda::memory_order_release);
        }
    }

    __device__ void dispatchGraph(int graph, bool flow) {
        const uint32_t cmd = static_cast<uint32_t>(graph) | ((flow ? 1U : 2U) << 16);
        if (hasWorkers()) postCommand(cmd);
        runCommand(cmd);
    }

    __device__ void workerLoop() {
        __shared__ uint32_t s_cmd;
        uint32_t seen = 0;
        for (;;) {
            if (threadIdx.x == 0) {
                cuda::atomic_ref<uint32_t, cuda::thread_scope_device> gen{m_ctlp->m_cmdGen};
                while (gen.load(cuda::memory_order_acquire) == seen) __nanosleep(64);
                s_cmd = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_cmd);
            }
            __syncthreads();
            const uint32_t cmd = s_cmd;
            ++seen;
            __syncthreads();
            if (cmd == CMD_EXIT) return;
            runCommand(cmd);
        }
    }

    __device__ uint32_t gridOr(uint32_t mine) {
        const uint32_t slot = m_k % 3;
        if (mine) atomicOr(&m_ctlp->m_flags[slot], mine);
        ctlSync();
        const uint32_t result = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_flags[slot]);
        if (m_tid == 0) {
            m_ctlp->m_flags[(m_k + 2) % 3] = 0;
            m_ctlp->m_counts[(m_k + 2) % 3] = 0;
        }
        ++m_k;
        return result;
    }

    __device__ uint32_t gridOrCount(uint32_t mine, uint32_t count, uint32_t& total) {
        const uint32_t slot = m_k % 3;
        if (mine) atomicOr(&m_ctlp->m_flags[slot], mine);
        if (count) atomicAdd(&m_ctlp->m_counts[slot], count);
        ctlSync();
        const uint32_t result = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_flags[slot]);
        total = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_counts[slot]);
        if (m_tid == 0) {
            m_ctlp->m_flags[(m_k + 2) % 3] = 0;
            m_ctlp->m_counts[(m_k + 2) % 3] = 0;
        }
        ++m_k;
        return result;
    }

    __device__ uint64_t gridMin(uint64_t mine) {
        const uint32_t slot = m_kMin % 3;
        if (mine != ~0ULL) {
            atomicMin(reinterpret_cast<unsigned long long*>(&m_ctlp->m_reduce[slot]),
                      static_cast<unsigned long long>(mine));
        }
        ctlSync();
        const uint64_t result = *reinterpret_cast<volatile uint64_t*>(&m_ctlp->m_reduce[slot]);
        if (m_tid == 0) m_ctlp->m_reduce[(m_kMin + 2) % 3] = ~0ULL;
        ++m_kMin;
        return result;
    }

    __device__ uint32_t* runFlags(int loop) const {
        return m_ctlp->m_runp + static_cast<size_t>(loop) * m_n;
    }
    __device__ uint32_t* iterCounts(int loop) const {
        return m_ctlp->m_iterp + static_cast<size_t>(loop) * m_n;
    }

    __device__ void runGraph(int graph) {
        const uint64_t start = m_tid == 0 ? globalTimer() : 0;
        uint64_t levelStart = start;
        const uint32_t tag = static_cast<uint32_t>(graph) + 1U;
        const int levels = T_Model::graphLevels(graph);
        for (int level = 0; level < levels; ++level) {
            const int size = T_Model::levelSize(graph, level);
            const int warpsPerTask = (m_n + 31) / 32;
            const long totalWarps = static_cast<long>(size) * warpsPerTask;
            const int lane = m_tid & 31;
            for (long w = m_tid >> 5; w < totalWarps; w += m_threads >> 5) {
                const int task = static_cast<int>(w / warpsPerTask);
                const int i = static_cast<int>(w % warpsPerTask) * 32 + lane;
                if (i < m_n && m_ctlp->m_wantp[i] == tag) {
                    T_Model::runTask(graph, level, task, view(i));
                }
            }
            m_grid.sync();
            if (m_tid == 0 && level < 64) {
                const uint64_t t = globalTimer();
                m_ctlp->m_levelNs[level] += t - levelStart;
                levelStart = t;
            }
        }
        if (m_tid == 0) {
            m_ctlp->m_profGraphNs += globalTimer() - start;
            ++m_ctlp->m_profGraphRuns;
        }
    }

    __device__ uint64_t gridMinStop(uint64_t mine, bool stop) {
        const uint32_t slot = m_kMin % 3;
        const uint32_t fslot = m_k % 3;
        if (mine != ~0ULL) {
            atomicMin(reinterpret_cast<unsigned long long*>(&m_ctlp->m_reduce[slot]),
                      static_cast<unsigned long long>(mine));
        }
        if (stop) atomicOr(&m_ctlp->m_flags[fslot], 1U);
        ctlSync();
        const uint64_t result = *reinterpret_cast<volatile uint64_t*>(&m_ctlp->m_reduce[slot]);
        const uint32_t stopped = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_flags[fslot]);
        if (m_tid == 0) {
            m_ctlp->m_reduce[(m_kMin + 2) % 3] = ~0ULL;
            m_ctlp->m_flags[(m_k + 2) % 3] = 0;
            m_ctlp->m_counts[(m_k + 2) % 3] = 0;
        }
        ++m_kMin;
        ++m_k;
        return stopped ? ~1ULL : result;
    }

    __device__ void runGraphFlow(int graph) {
        const uint64_t start = m_tid == 0 ? globalTimer() : 0;
        const uint32_t tag = static_cast<uint32_t>(graph) + 1U;
        const uint32_t epoch = *reinterpret_cast<volatile uint32_t*>(&m_ctlp->m_epoch[graph]) + 1U;
        const int tasks = T_Model::graphTasks(graph);
        const int groups = (m_n + 31) / 32;
        uint32_t* const flagsp
            = vlGpuFlowFlags + static_cast<size_t>(T_Model::taskBase(graph)) * groups;
        const int lane = m_tid & 31;
        const long warps = m_threads >> 5;
        const long items = static_cast<long>(tasks) * groups;
        for (long w = m_tid >> 5; w < items; w += warps) {
            const int task = static_cast<int>(w / groups);
            const int group = static_cast<int>(w % groups);
            const uint32_t* beginp = nullptr;
            const uint32_t* endp = nullptr;
            T_Model::preds(graph, task, beginp, endp);
            for (const uint32_t* pp = beginp; pp != endp; ++pp) {
                cuda::atomic_ref<uint32_t, cuda::thread_scope_device> flag{
                    flagsp[static_cast<size_t>(*pp) * groups + group]};
                while (flag.load(cuda::memory_order_relaxed) != epoch) __nanosleep(20);
            }
            if (beginp != endp)
                cuda::atomic_thread_fence(cuda::memory_order_acquire, cuda::thread_scope_device);
            const int i = group * 32 + lane;
            if (i < m_n && m_ctlp->m_wantp[i] == tag) T_Model::runFlat(graph, task, view(i));
            __syncwarp();
            if (lane == 0) {
                cuda::atomic_ref<uint32_t, cuda::thread_scope_device> flag{
                    flagsp[static_cast<size_t>(task) * groups + group]};
                flag.store(epoch, cuda::memory_order_release);
            }
        }
        m_grid.sync();
        if (m_tid == 0) {
            m_ctlp->m_epoch[graph] = epoch;
            m_ctlp->m_profGraphNs += globalTimer() - start;
            ++m_ctlp->m_profGraphRuns;
        }
    }

    __device__ void runGraphSeq(int graph) {
        const uint64_t start = m_tid == 0 ? globalTimer() : 0;
        const uint32_t tag = static_cast<uint32_t>(graph) + 1U;
        for (int i = m_tid; i < m_n; i += m_ctlThreads) {
            if (m_ctlp->m_wantp[i] == tag) T_Model::runSeq(graph, view(i));
        }
        if (m_tid == 0) {
            m_ctlp->m_profGraphNs += globalTimer() - start;
            ++m_ctlp->m_profGraphRuns;
            ++m_ctlp->m_profSeqRuns;
        }
    }

    static constexpr uint32_t SEQ_SHIFT = 16;
    static constexpr bool SEQ_ENABLED = T_Model::GRAPHS <= 16;
    static constexpr uint32_t GRAPH_MASK = SEQ_ENABLED ? (1U << SEQ_SHIFT) - 1U : 0x7fffffffU;

    __device__ static uint32_t suspendBits(uint32_t susp, const VlGpuView& v) {
        uint32_t result = 1U << (susp - 1U);
        if (!SEQ_ENABLED) return result;
        if (susp > 15U || !T_Model::seqOk(static_cast<int>(susp - 1U), v)) {
            result |= 1U << (SEQ_SHIFT + ((susp - 1U) & 15U));
        }
        return result;
    }

    template <typename T_Fn>
    __device__ bool callRegion(uint32_t* runp, T_Fn fn, int region = 7) {
        const uint64_t regionStart = m_tid == 0 ? globalTimer() : 0;
        const uint64_t graphBefore = m_tid == 0 ? m_ctlp->m_profGraphNs : 0;
        bool mineTrue = false;
        uint32_t bits = 0;
        uint32_t wanting = 0;
        for (int i = m_tid; i < m_n; i += m_ctlThreads) {
            if (!runp[i]) continue;
            const VlGpuView v = view(i);
            const bool r = fn(v);
            const uint32_t susp = T_Model::takeSuspend(v);
            if (susp) {
                m_ctlp->m_wantp[i] = susp;
                ++wanting;
                bits |= suspendBits(susp, v);
            } else {
                runp[i] = r ? 1U : 0U;
                mineTrue |= r;
            }
        }
        constexpr uint32_t TRUE_BIT = 1U << 31;
        uint32_t total = 0;
        bits = gridOrCount(bits | (mineTrue ? TRUE_BIT : 0U), wanting, total);
        bool anyTrue = (bits & TRUE_BIT) != 0;
        bits &= ~TRUE_BIT;
        while (bits & GRAPH_MASK) {
            for (int graph = 0; graph < T_Model::GRAPHS; ++graph) {
                if (!(bits & (1U << graph))) continue;
                if (SEQ_ENABLED && graph < 15 && !m_ctlp->m_noSeq
                    && !(bits & (1U << (SEQ_SHIFT + graph)))) {
                    runGraphSeq(graph);
                } else {
                    dispatchGraph(graph, !(m_ctlp->m_levelMode || total >= m_ctlp->m_flowMax));
                }
            }
            uint32_t again = 0;
            wanting = 0;
            for (int i = m_tid; i < m_n; i += m_ctlThreads) {
                if (!m_ctlp->m_wantp[i]) continue;
                m_ctlp->m_wantp[i] = 0;
                const VlGpuView v = view(i);
                const bool r = fn(v);
                const uint32_t susp = T_Model::takeSuspend(v);
                if (susp) {
                    m_ctlp->m_wantp[i] = susp;
                    ++wanting;
                    again |= suspendBits(susp, v);
                } else {
                    runp[i] = r ? 1U : 0U;
                    mineTrue |= r;
                }
            }
            bits = gridOrCount(again | (mineTrue ? TRUE_BIT : 0U), wanting, total);
            anyTrue = anyTrue || (bits & TRUE_BIT) != 0;
            bits &= ~TRUE_BIT;
        }
        if (m_tid == 0) {
            m_ctlp->m_regionNs[region]
                += globalTimer() - regionStart - (m_ctlp->m_profGraphNs - graphBefore);
            ++m_ctlp->m_regionCalls[region];
        }
        return anyTrue;
    }

    __device__ void enterLoop(int loop, const uint32_t* outerp) {
        uint32_t* const runp = runFlags(loop);
        uint32_t* const iterp = iterCounts(loop);
        for (int i = m_tid; i < m_n; i += m_ctlThreads) {
            runp[i] = outerp[i];
            iterp[i] = 0;
        }
    }

    __device__ void countIteration(int loop) {
        uint32_t* const runp = runFlags(loop);
        uint32_t* const iterp = iterCounts(loop);
        for (int i = m_tid; i < m_n; i += m_ctlThreads) {
            if (!runp[i]) continue;
            if (++iterp[i] > m_ctlp->m_convergeLimit) {
                m_ctlp->m_errorp[i] = VL_GPU_ERR_CONVERGE;
                runp[i] = 0;
            }
        }
    }

    template <int T_Loop>
    __device__ void loop(const uint32_t* outerp) {
        if constexpr (T_Model::trivialLoop(T_Loop)) {
            if constexpr (T_Loop > 1) loop<T_Loop - 1>(outerp);
            return;
        }
        enterLoop(T_Loop, outerp);
        uint32_t* const runp = runFlags(T_Loop);
        bool again;
        do {
            countIteration(T_Loop);
            if constexpr (T_Loop > 1) loop<T_Loop - 1>(runp);
            again = callRegion(
                runp,
                [](const VlGpuView& v) {
                    if constexpr (T_Loop == 5) return T_Model::evalReact(v);
                    if constexpr (T_Loop == 4) return T_Model::evalObs(v);
                    if constexpr (T_Loop == 3) return T_Model::evalNba(v);
                    if constexpr (T_Loop == 2) return T_Model::evalInact(v);
                    return T_Model::evalAct(v);
                },
                T_Loop);
        } while (again);
    }

    __device__ void icoLoop() {
        enterLoop(0, m_ctlp->m_steppingp);
        uint32_t* const runp = runFlags(0);
        bool first = true;
        bool again;
        do {
            countIteration(0);
            const bool isFirst = first;
            again = callRegion(
                runp, [isFirst](const VlGpuView& v) { return T_Model::evalIco(v, isFirst); }, 0);
            first = false;
        } while (again);
    }

public:
    __device__ Driver(uint8_t* basep, int n, const uint8_t* activep, VlGpuResidentCtl* ctlp)
        : m_grid{cg::this_grid()}
        , m_basep{basep}
        , m_n{n}
        , m_activep{activep}
        , m_ctlp{ctlp}
        , m_tid{static_cast<int>(blockIdx.x * blockDim.x + threadIdx.x)}
        , m_threads{static_cast<int>(gridDim.x * blockDim.x)}
        , m_ctlBlocks{ctlBlocks(n, ctlp)}
        , m_ctlThreads{m_ctlBlocks * static_cast<int>(blockDim.x)} {}

    __device__ static int ctlBlocks(int n, const VlGpuResidentCtl* ctlp) {
        const int grid = static_cast<int>(gridDim.x);
        if (ctlp->m_noSplit) return grid;
        const int need = (n + static_cast<int>(blockDim.x) - 1) / static_cast<int>(blockDim.x);
        return need < 1 ? 1 : need > grid ? grid : need;
    }

    __device__ void run() {
        if (m_tid == 0) {
            for (int s = 0; s < 3; ++s) {
                m_ctlp->m_flags[s] = 0;
                m_ctlp->m_counts[s] = 0;
                m_ctlp->m_reduce[s] = ~0ULL;
            }
            m_ctlp->m_cmdGen = 0;
            m_ctlp->m_barGen = 0;
            m_ctlp->m_barCount = 0;
        }
        m_grid.sync();
        if (static_cast<int>(blockIdx.x) >= m_ctlBlocks) {
            workerLoop();
            return;
        }
        runControl();
        if (hasWorkers()) postCommand(CMD_EXIT);
    }

    __device__ void runControl() {
        const uint64_t sliceStart = globalTimer();
        for (;;) {
            const bool overTime = m_tid == 0 && m_ctlp->m_sliceNs
                                  && globalTimer() - sliceStart > m_ctlp->m_sliceNs;
            uint64_t mine = ~0ULL;
            for (int i = m_tid; i < m_n; i += m_ctlThreads) {
                const VlGpuView v = view(i);
                uint64_t t = ~0ULL;
                if (m_activep[i] && !m_ctlp->m_errorp[i] && !T_Model::finished(v)) {
                    t = T_Model::nextTime(v);
                    if (t != ~0ULL) t += T_Model::timeBase(v);
                    if (T_Model::forkOverflow(v)) {
                        m_ctlp->m_errorp[i] = VL_GPU_ERR_FORK_OVERFLOW;
                        t = ~0ULL;
                    }
                }
                m_ctlp->m_nextp[i] = t;
                if (t < mine) mine = t;
            }
            const uint64_t now = gridMinStop(mine, overTime);
            if (now == ~1ULL) return;
            if (now != ~0ULL && now > m_ctlp->m_stopTime) {
                if (m_tid == 0) m_ctlp->m_done = 1;
                return;
            }
            if (now == ~0ULL) {
                if (m_tid == 0) m_ctlp->m_done = 1;
                return;
            }
            vlGpuNow = now;
            const uint64_t stepStart = m_tid == 0 ? globalTimer() : 0;
            for (int i = m_tid; i < m_n; i += m_ctlThreads) {
                const bool stepping = m_ctlp->m_nextp[i] == now;
                m_ctlp->m_steppingp[i] = stepping ? 1U : 0U;
                if (stepping) T_Model::evalSample(view(i));
            }
            if (m_tid == 0) {
                if (m_ctlp->m_stepTimesp && m_ctlp->m_steps < m_ctlp->m_stepTimesMax) {
                    m_ctlp->m_stepTimesp[m_ctlp->m_steps] = now;
                }
                ++m_ctlp->m_steps;
            }
            icoLoop();
            loop<5>(m_ctlp->m_steppingp);
            for (int i = m_tid; i < m_n; i += m_ctlThreads) {
                if (m_ctlp->m_steppingp[i]) T_Model::evalPostponed(view(i));
            }
            if (m_tid == 0) m_ctlp->m_profStepNs += globalTimer() - stepStart;
        }
    }
};

}  // namespace vlgpures

template <typename T_Model>
__global__ void vlGpuResidentKernel(uint8_t* basep, int n, const uint8_t* activep,
                                    VlGpuResidentCtl* ctlp) {
    vlgpures::Driver<T_Model> driver{basep, n, activep, ctlp};
    driver.run();
}

#endif
