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
/// \brief GPU runtime: host side
///
//=============================================================================

#ifndef VERILATOR_VERILATED_GPU_H_
#define VERILATOR_VERILATED_GPU_H_

#include "verilatedos.h"

#include <cstddef>
#include <cstdint>
#include <cstdio>

class VerilatedContext;

#ifndef VL_GPU_LAYOUT_GROUP
#define VL_GPU_LAYOUT_GROUP 32
#endif

struct VlGpuCopy final {
    size_t m_root;  // Offset of the member in the host model
    size_t m_state;  // Offset of the member in the GPU state struct
    size_t m_size;  // Size of the member in bytes
};

#ifndef VL_GPU_DEFER_BYTES
#define VL_GPU_DEFER_BYTES 65536
#endif

struct VlGpuDeferBuf final {
    static constexpr uint32_t SIZE = VL_GPU_DEFER_BYTES;
    uint32_t m_used;  // Bytes of records in m_data
    uint32_t m_overflow;  // Nonzero if records were dropped for lack of space
    uint8_t m_data[SIZE];
};

struct VlGpuAssertCtl final {
    static constexpr int SLOTS = 32;
    uint32_t m_on;  // Enabled assertion types
    uint32_t m_passVacuous;  // Types whose vacuous passes are reported
    uint32_t m_passNonvacuous;  // Types whose nonvacuous passes are reported
    uint32_t m_failOn;  // Types whose failures are reported
    uint32_t m_kill[SLOTS];
};

class VerilatedGpu final {
public:
    using ReplayFn = void (*)(int id, void* userp);

    static void init(VerilatedContext* contextp) VL_MT_UNSAFE;
    static int device() VL_MT_SAFE;
    static void* deviceAlloc(size_t bytes) VL_MT_UNSAFE;
    static void copyToDevice(void* devp, const void* hostp, size_t bytes) VL_MT_UNSAFE;
    static void copyToHost(void* hostp, const void* devp, size_t bytes) VL_MT_UNSAFE;
    static void synchronize(const char* what) VL_MT_UNSAFE;
    static void deferReset(VlGpuDeferBuf& buf) VL_MT_SAFE;
    static void copyIn(const VlGpuCopy* tablep, const void* rootp, void* statep) VL_MT_SAFE;
    static void copyOut(const VlGpuCopy* tablep, const void* statep, void* rootp) VL_MT_SAFE;
    static void replay(const VlGpuDeferBuf& buf, ReplayFn fn, void* userp) VL_MT_UNSAFE;
    static int batch() VL_MT_SAFE;
    static int currentCopy() VL_MT_SAFE;
    static void* hostAlloc(size_t bytes) VL_MT_UNSAFE;
    static void uploadBroadcast(void* devp, size_t stride, const void* srcp, size_t bytes, int n,
                                void* stagep) VL_MT_UNSAFE;
    static void downloadGather(void* dstp, const void* devp, size_t stride, size_t bytes,
                               int n) VL_MT_UNSAFE;
    static void checkDivergence(const void* stagep, size_t prefixBytes, size_t compareBytes,
                                int n) VL_MT_UNSAFE;
    static void replayBatch(const void* stagep, size_t prefixBytes, size_t deferOffset,
                            const void* devp, size_t stride, int n, ReplayFn fn,
                            void* userp) VL_MT_UNSAFE;
    static void soaBroadcast(const VlGpuCopy* tablep, const void* aosp, void* stagep,
                             int n) VL_MT_SAFE;
    static void soaCheck(const VlGpuCopy* tablep, const void* stagep, int n) VL_MT_UNSAFE;
    static void soaExtract(const VlGpuCopy* tablep, const void* stagep, int n, int copy,
                           void* aosp) VL_MT_SAFE;
    static void soaDeferReset(void* devp, size_t deferOffset, int n) VL_MT_UNSAFE;
    static void soaReplay(const void* devp, size_t deferOffset, int n, ReplayFn fn,
                          void* userp) VL_MT_UNSAFE;
    static void dpiCopyInit(int n) VL_MT_UNSAFE;
    static const char* jobPlusArg(int copy, const char* prefixp) VL_MT_UNSAFE;
    static const char* jobName(int copy) VL_MT_UNSAFE;
    static int jobArgCount(int copy) VL_MT_UNSAFE;
    static const char* jobArg(int copy, int index) VL_MT_UNSAFE;
    static const uint8_t* activeDevice(int n) VL_MT_UNSAFE;
    static int leaderCopy() VL_MT_SAFE;
    static void soaPreLaunch(void* devp, int n, size_t deferOffset, const void* aosp,
                             const VlGpuCopy* sharedp) VL_MT_UNSAFE;
    static bool soaPostLaunch(void* devp, int n, size_t deferOffset, void* aosp,
                              const VlGpuCopy* sharedp) VL_MT_UNSAFE;
    static void soaReplayPending(void* devp, size_t deferOffset, int n, ReplayFn fn,
                                 void* userp) VL_MT_UNSAFE;
    static void soaUploadAll(void* devp, int n, int copy, const void* aosp, size_t stride,
                             const VlGpuCopy* sharedp, const VlGpuCopy* devicep) VL_MT_UNSAFE;
    static const uint8_t* replayCursor() VL_MT_UNSAFE;
    static void assertCtlSync() VL_MT_UNSAFE;
    static bool residentEnabled() VL_MT_SAFE;
    static bool hostDumpDue(uint64_t time) VL_MT_UNSAFE;
    static const char* dumpPath() VL_MT_SAFE;
    static void dumpState(const char* pathp, const void* statep, size_t bytes,
                          const VlGpuCopy* sharedp, const char* const* sharedNamesp,
                          const VlGpuCopy* devicep, const char* const* deviceNamesp) VL_MT_UNSAFE;
    static void hostStep(uint64_t time) VL_MT_UNSAFE;
    using ResidentLaunchFn = int (*)(void* basep, int n, const void* activep, void* ctlp);
    static int residentSlots(size_t stride, size_t kernelStack) VL_MT_UNSAFE;
    static void residentRun(void* devp, int n,
                            const struct VlGpuResidentModel& model) VL_MT_UNSAFE;
    static void failCopy(int copy, const char* messagep) VL_MT_UNSAFE;
    static void checkpointWrite(FILE* fp, const void* datap, size_t bytes) VL_MT_UNSAFE;
    static void checkpointRead(FILE* fp, void* datap, size_t bytes) VL_MT_UNSAFE;
    static void checkpointWriteDevice(FILE* fp, const void* devp, size_t bytes) VL_MT_UNSAFE;
    static void checkpointReadDevice(FILE* fp, void* devp, size_t bytes) VL_MT_UNSAFE;
    static bool resuming() VL_MT_UNSAFE;
    static size_t stateBytes(size_t stride, int n) VL_MT_UNSAFE;
};

struct VlGpuResidentModel final {
    size_t m_stride = 0;  // Size of one copy's state
    size_t m_deferOffset = 0;  // Offset of the output buffer in the state
    size_t m_finishOffset = 0;  // Offset of the $finish flag in the state
    size_t m_tbaseOffset = 0;  // Offset of the copy's time base in the state
    size_t m_fatalOffset = 0;  // Offset of the fatal error code in the state
    const char* const* m_fatalMsgsp = nullptr;
    uint32_t m_fatalCount = 0;  // Number of entries in m_fatalMsgsp
    const VlGpuCopy* m_sharedp = nullptr;  // Members shared with the host model
    const VlGpuCopy* m_devicep = nullptr;  // Members used only on the GPU
    const void* m_snapshotp = nullptr;  // State after initialization, copied to new copies
    uint32_t m_convergeLimit = 0;  // Region iterations before a copy fails to converge
    VerilatedGpu::ResidentLaunchFn m_launch = nullptr;  // Launches the resident kernel
    VerilatedGpu::ReplayFn m_replay = nullptr;  // Replays one deferred output record
    void* m_userp = nullptr;  // Host model passed to m_replay
    const char* const* m_sharedNamesp = nullptr;
    const char* const* m_deviceNamesp = nullptr;
};

extern "C" int vlGpuProbe();
extern "C" size_t vlGpuDpiCopyBytes() __attribute__((weak));
extern "C" void vlGpuDpiCopyInit(int copy, int n) __attribute__((weak));
extern "C" void vlGpuDpiCheckpointSave(FILE* fp, int n) __attribute__((weak));
extern "C" void vlGpuDpiCheckpointLoad(FILE* fp, int n) __attribute__((weak));

#endif
