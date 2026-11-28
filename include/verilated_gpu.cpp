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

#include "verilated_gpu.h"

#include "verilated.h"
#include "verilated_gpu_resident_ctl.h"

#include <algorithm>
#include <chrono>
#include <cinttypes>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cuda_runtime_api.h>
#include <fcntl.h>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unistd.h>
#include <vector>

namespace {
void recordPlusarg(const char* prefixp);
int s_gpuDevice = -1;
VerilatedContext* s_contextp = nullptr;
bool s_residentReplay = false;
uint64_t s_replayTimeBase = 0;
const uint8_t* s_replayCursor = nullptr;

struct GpuProfile final {
    bool m_enabled
        = std::getenv("VERILATOR_GPU_PROFILE") != nullptr;  // VERILATOR_GPU_PROFILE is set
    uint64_t m_launches = 0;  // Kernel launches
    uint64_t m_uploadBytes = 0;  // Bytes copied to the GPU
    uint64_t m_downloadBytes = 0;  // Bytes copied from the GPU
    double m_kernelSec = 0;  // Time in kernels
    double m_uploadSec = 0;  // Time copying to the GPU
    double m_downloadSec = 0;  // Time copying from the GPU
    double m_replaySec = 0;  // Time replaying deferred output
    std::chrono::steady_clock::time_point m_start
        = std::chrono::steady_clock::now();  // Start of the run
    ~GpuProfile() {
        if (!m_enabled) return;
        const double total
            = std::chrono::duration<double>(std::chrono::steady_clock::now() - m_start).count();
        std::fprintf(stderr,
                     "GPU profile: %" PRIu64 " launches, kernel %.3f s, upload %.3f s (%" PRIu64
                     " B), "
                     "download %.3f s (%" PRIu64 " B), replay %.3f s, total %.3f s\n",
                     static_cast<uint64_t>(m_launches), m_kernelSec, m_uploadSec,
                     static_cast<uint64_t>(m_uploadBytes), m_downloadSec,
                     static_cast<uint64_t>(m_downloadBytes), m_replaySec, total);
    }
};
GpuProfile s_profile;

double secondsSince(std::chrono::steady_clock::time_point start) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

void gpuFatal(const std::string& msg) { VL_FATAL_MT("", 0, "", ("GPU: " + msg).c_str()); }

void gpuCheck(cudaError_t err, const char* what) {
    if (err != cudaSuccess) gpuFatal(std::string{what} + ": " + cudaGetErrorString(err));
}

size_t& layoutStrideRef() {
    static size_t s_stride = 0;
    return s_stride;
}

int& layoutModeRef() {
    static int s_mode = 0;
    return s_mode;
}

size_t layoutStride() { return layoutStrideRef(); }
int layoutMode() { return layoutModeRef(); }

uint8_t* memberAt(void* basep, int n, int i, size_t offset, size_t size) {
    uint8_t* const p = static_cast<uint8_t*>(basep);
    const size_t s = layoutStride();
    const size_t copy = static_cast<size_t>(i);
    switch (layoutMode()) {
    case 1: return p + copy * s + offset;
    case 2: {
        constexpr size_t G = VL_GPU_LAYOUT_GROUP;
        return p + (copy / G) * G * s + G * offset + (copy % G) * size;
    }
    default: return p + static_cast<size_t>(n) * offset + copy * size;
    }
}

void memberRows(void* hostp, size_t rowBytes, void* basep, int n, size_t offset, size_t size) {
    uint8_t* const top = static_cast<uint8_t*>(hostp);
    if (layoutMode() == 2) {
        for (int g = 0; g * VL_GPU_LAYOUT_GROUP < n; ++g) {
            const int rows = std::min(VL_GPU_LAYOUT_GROUP, n - g * VL_GPU_LAYOUT_GROUP);
            gpuCheck(cudaMemcpy2D(top + static_cast<size_t>(g) * VL_GPU_LAYOUT_GROUP * rowBytes,
                                  rowBytes,
                                  memberAt(basep, n, g * VL_GPU_LAYOUT_GROUP, offset, size), size,
                                  rowBytes, rows, cudaMemcpyDeviceToHost),
                     "cudaMemcpy2D member");
        }
        return;
    }
    const size_t pitch = layoutMode() == 1 ? layoutStride() : size;
    gpuCheck(cudaMemcpy2D(top, rowBytes, memberAt(basep, n, 0, offset, size), pitch, rowBytes, n,
                          cudaMemcpyDeviceToHost),
             "cudaMemcpy2D member");
}

void memberRowsZero(void* basep, int n, size_t offset, size_t size, size_t rowBytes) {
    if (layoutMode() == 2) {
        for (int g = 0; g * VL_GPU_LAYOUT_GROUP < n; ++g) {
            const int rows = std::min(VL_GPU_LAYOUT_GROUP, n - g * VL_GPU_LAYOUT_GROUP);
            gpuCheck(cudaMemset2D(memberAt(basep, n, g * VL_GPU_LAYOUT_GROUP, offset, size), size,
                                  0, rowBytes, rows),
                     "cudaMemset2D member");
        }
        return;
    }
    const size_t pitch = layoutMode() == 1 ? layoutStride() : size;
    gpuCheck(cudaMemset2D(memberAt(basep, n, 0, offset, size), pitch, 0, rowBytes, n),
             "cudaMemset2D member");
}

void memberRead(void* hostp, void* basep, int n, size_t offset, size_t size) {
    memberRows(hostp, size, basep, n, offset, size);
}

}  // namespace

void VerilatedGpu::init(VerilatedContext* contextp) {
    if (s_gpuDevice >= 0) return;
    s_contextp = contextp;
    contextp->m_plusargReadCb = &recordPlusarg;
    int count = 0;
    gpuCheck(cudaGetDeviceCount(&count), "cudaGetDeviceCount");
    if (count < 1) gpuFatal("no CUDA device found");
    gpuCheck(cudaSetDevice(0), "cudaSetDevice");
    gpuCheck(cudaSetDeviceFlags(cudaDeviceScheduleBlockingSync | cudaDeviceLmemResizeToMax),
             "cudaSetDeviceFlags");
    const char* const stackEnvp = std::getenv("VERILATOR_GPU_STACK");
    const size_t stack = stackEnvp ? std::strtoull(stackEnvp, nullptr, 0) : 16384;
    gpuCheck(cudaDeviceSetLimit(cudaLimitStackSize, stack), "cudaDeviceSetLimit");
    const int probe = vlGpuProbe();
    if (probe != 0) gpuFatal("kernel launch probe failed (code " + std::to_string(probe) + ")");
    s_gpuDevice = 0;
}

int VerilatedGpu::device() { return s_gpuDevice; }

void* VerilatedGpu::deviceAlloc(size_t bytes) {
    void* devp = nullptr;
    gpuCheck(cudaMalloc(&devp, bytes), "cudaMalloc");
    gpuCheck(cudaMemset(devp, 0, bytes), "cudaMemset");
    return devp;
}

void VerilatedGpu::copyToDevice(void* devp, const void* hostp, size_t bytes) {
    const auto start = std::chrono::steady_clock::now();
    gpuCheck(cudaMemcpy(devp, hostp, bytes, cudaMemcpyHostToDevice), "cudaMemcpy to device");
    if (s_profile.m_enabled) {
        s_profile.m_uploadSec += secondsSince(start);
        s_profile.m_uploadBytes += bytes;
    }
}

void VerilatedGpu::copyToHost(void* hostp, const void* devp, size_t bytes) {
    const auto start = std::chrono::steady_clock::now();
    gpuCheck(cudaMemcpy(hostp, devp, bytes, cudaMemcpyDeviceToHost), "cudaMemcpy to host");
    if (s_profile.m_enabled) {
        s_profile.m_downloadSec += secondsSince(start);
        s_profile.m_downloadBytes += bytes;
    }
}

void VerilatedGpu::synchronize(const char* what) {
    const auto start = std::chrono::steady_clock::now();
    gpuCheck(cudaGetLastError(), what);
    if (!s_profile.m_enabled) return;
    gpuCheck(cudaDeviceSynchronize(), what);
    if (s_profile.m_enabled) {
        s_profile.m_kernelSec += secondsSince(start);
        ++s_profile.m_launches;
    }
}

void VerilatedGpu::copyIn(const VlGpuCopy* tablep, const void* rootp, void* statep) {
    const uint8_t* const fromp = static_cast<const uint8_t*>(rootp);
    uint8_t* const top = static_cast<uint8_t*>(statep);
    for (const VlGpuCopy* cp = tablep; cp->m_size; ++cp) {
        std::memcpy(top + cp->m_state, fromp + cp->m_root, cp->m_size);
    }
}

void VerilatedGpu::copyOut(const VlGpuCopy* tablep, const void* statep, void* rootp) {
    const uint8_t* const fromp = static_cast<const uint8_t*>(statep);
    uint8_t* const top = static_cast<uint8_t*>(rootp);
    for (const VlGpuCopy* cp = tablep; cp->m_size; ++cp) {
        std::memcpy(top + cp->m_root, fromp + cp->m_state, cp->m_size);
    }
}

void VerilatedGpu::deferReset(VlGpuDeferBuf& buf) {
    buf.m_used = 0;
    buf.m_overflow = 0;
}

void VerilatedGpu::replay(const VlGpuDeferBuf& buf, ReplayFn fn, void* userp) {
    if (!buf.m_used) return;
    const auto start = std::chrono::steady_clock::now();
    struct Timer final {
        std::chrono::steady_clock::time_point m_start;  // Start of this replay
        ~Timer() {
            if (s_profile.m_enabled) s_profile.m_replaySec += secondsSince(m_start);
        }
    } timer{start};
    uint32_t pos = 0;
    while (pos + 16 <= buf.m_used) {
        uint32_t id = 0;
        uint32_t bytes = 0;
        uint64_t time = 0;
        std::memcpy(&id, buf.m_data + pos, 4);
        std::memcpy(&bytes, buf.m_data + pos + 4, 4);
        std::memcpy(&time, buf.m_data + pos + 8, 8);
        if (s_residentReplay) Verilated::threadContextp()->time(time - s_replayTimeBase);
        s_replayCursor = buf.m_data + pos + 16;
        if (id == 0xffffffffU) {
            std::fwrite(s_replayCursor, 1, bytes, stdout);
            std::fflush(stdout);
        } else {
            fn(static_cast<int>(id), userp);
        }
        pos += 16 + ((bytes + 3U) & ~3U);
    }
    s_replayCursor = nullptr;
}

const uint8_t* VerilatedGpu::replayCursor() { return s_replayCursor; }

namespace {
int s_currentCopy = 0;
}

namespace {
std::vector<uint8_t> s_active;
uint8_t* s_activeDevp = nullptr;
int s_leader = 0;

void gpuDeactivate(int copy) {
    if (copy < 0 || copy >= static_cast<int>(s_active.size())) return;
    s_active[copy] = 0;
    if (s_activeDevp) {
        const uint8_t zero = 0;
        gpuCheck(cudaMemcpy(s_activeDevp + copy, &zero, 1, cudaMemcpyHostToDevice),
                 "cudaMemcpy active");
    }
    while (s_leader + 1 < static_cast<int>(s_active.size()) && !s_active[s_leader]) ++s_leader;
}

struct GpuJob final {
    std::string m_name;  // Job name, also the log file name
    std::vector<std::string> m_args;  // Arguments of the job
    int m_logFd = -1;  // Log file, -1 once closed
    int m_status = 0;  // 0 running or pending, 1 passed, 2 failed
    uint64_t m_finishTime = 0;  // Simulation time when the job ended
};

void gpuActivate(int copy) {
    if (copy < 0 || copy >= static_cast<int>(s_active.size())) return;
    s_active[copy] = 1;
    if (s_activeDevp) {
        const uint8_t one = 1;
        gpuCheck(cudaMemcpy(s_activeDevp + copy, &one, 1, cudaMemcpyHostToDevice),
                 "cudaMemcpy active");
    }
}

struct GpuBatch final {
    std::vector<GpuJob> m_jobs;  // All jobs of the job file
    std::string m_logDir;  // Directory for logs, summary and checkpoint
    int m_remaining = 0;  // Jobs not yet finished
    int m_savedOut = -1;  // Original stdout, while output goes to a job log
    int m_savedErr = -1;  // Original stderr, while output goes to a job log
    std::vector<int> m_slotJob;  // Per slot: job it runs, -1 for none
    int m_nextJob = 0;  // Next job to start

    int jobOf(int slot) const {
        if (m_slotJob.empty()) {
            return slot >= 0 && slot < static_cast<int>(m_jobs.size()) ? slot : -1;
        }
        return slot >= 0 && slot < static_cast<int>(m_slotJob.size()) ? m_slotJob[slot] : -1;
    }
    void startLog(int job) {
        const int fd = m_jobs[job].m_logFd;
        if (fd < 0) return;
        if (::ftruncate(fd, 0) != 0 || ::lseek(fd, 0, SEEK_SET) != 0) {
            gpuFatal("cannot reset the log of " + m_jobs[job].m_name);
        }
    }
    void initSlots(int n) {
        m_slotJob.assign(n, -1);
        const int jobs = static_cast<int>(m_jobs.size());
        for (int i = 0; i < n && i < jobs; ++i) {
            m_slotJob[i] = i;
            startLog(i);
        }
        m_nextJob = n < jobs ? n : jobs;
    }
    bool pending() const { return m_nextJob < static_cast<int>(m_jobs.size()); }
    int assign(int slot) {
        if (!pending()) return -1;
        m_slotJob[slot] = m_nextJob++;
        startLog(m_slotJob[slot]);
        return m_slotJob[slot];
    }
    uint64_t hash() const {
        uint64_t h = 1469598103934665603ULL;
        const auto mix = [&h](const std::string& text) {
            for (const char c : text) h = (h ^ static_cast<uint8_t>(c)) * 1099511628211ULL;
            h = (h ^ 0xffU) * 1099511628211ULL;
        };
        for (const GpuJob& job : m_jobs) {
            mix(job.m_name);
            for (const std::string& arg : job.m_args) mix(arg);
        }
        return h;
    }
    void message(int slot, const std::string& text) {
        const int job = jobOf(slot);
        if (job < 0 || m_jobs[job].m_logFd < 0) {
            std::fputs(text.c_str(), stderr);
            return;
        }
        const ssize_t written = ::write(m_jobs[job].m_logFd, text.data(), text.size());
        (void)written;
    }

    GpuBatch() {
        const char* const filep = std::getenv("VERILATOR_GPU_JOBS");
        if (!filep) return;
        std::ifstream in{filep};
        if (!in) gpuFatal(std::string{"cannot open job file "} + filep);
        const char* const dirp = std::getenv("VERILATOR_GPU_LOGDIR");
        m_logDir = dirp ? dirp : ".";
        std::string line;
        while (std::getline(in, line)) {
            std::istringstream words{line};
            GpuJob job;
            if (!(words >> job.m_name) || job.m_name[0] == '#') continue;
            std::string arg;
            while (words >> arg) job.m_args.push_back(arg);
            const std::string logName = m_logDir + "/" + job.m_name + ".log";
            job.m_logFd = ::open(logName.c_str(), O_WRONLY | O_CREAT, 0644);
            if (job.m_logFd < 0) gpuFatal("cannot create " + logName);
            m_jobs.push_back(std::move(job));
        }
        if (m_jobs.empty()) gpuFatal(std::string{"no jobs in "} + filep);
        m_remaining = static_cast<int>(m_jobs.size());
        m_savedOut = ::dup(1);
        m_savedErr = ::dup(2);
    }
    bool active() const { return !m_jobs.empty(); }
    void redirect(int copy) {
        std::fflush(stdout);
        std::fflush(stderr);
        const int job = jobOf(copy);
        if (job < 0 || m_jobs[job].m_logFd < 0) return;
        ::dup2(m_jobs[job].m_logFd, 1);
        ::dup2(m_jobs[job].m_logFd, 2);
    }
    void restore() {
        std::fflush(stdout);
        std::fflush(stderr);
        ::dup2(m_savedOut, 1);
        ::dup2(m_savedErr, 2);
    }
    void finished(int copy, bool error) {
        const int jobIndex = jobOf(copy);
        if (jobIndex < 0) return;
        if (!m_slotJob.empty()) m_slotJob[copy] = -1;
        GpuJob& job = m_jobs[jobIndex];
        if (job.m_status) return;
        job.m_status = error ? 2 : 1;
        gpuDeactivate(copy);
        job.m_finishTime = Verilated::threadContextp()->time();
        ::close(job.m_logFd);
        job.m_logFd = -1;
        if (--m_remaining == 0) writeSummary();
    }
    void writeSummary() {
        const std::string name = m_logDir + "/gpu_batch_summary.txt";
        FILE* const fp = std::fopen(name.c_str(), "w");
        for (const GpuJob& job : m_jobs) {
            const char* const statep = job.m_status == 1   ? "PASS"
                                       : job.m_status == 2 ? "FAIL"
                                                           : "RUNNING";
            if (fp) {
                std::fprintf(fp, "%s %s %" PRIu64 "\n", job.m_name.c_str(), statep,
                             static_cast<uint64_t>(job.m_finishTime));
            }
        }
        if (fp) std::fclose(fp);
    }
};

GpuBatch& gpuBatch() {
    static GpuBatch s_batch;
    return s_batch;
}

struct GpuCheckpointHeader final {
    char m_magic[8];
    uint64_t m_stride;  // State size and layout, must match on resume
    int32_t m_n;  // Number of slots
    int32_t m_jobs;  // Number of jobs
    uint64_t m_jobsHash;  // Hash of the job list, must match on resume
    uint64_t m_now;  // GPU time when saved
    uint64_t m_refills;  // Refills so far, for statistics
    uint64_t m_harvested;  // Finished copies so far, for statistics
};

constexpr char GPU_CHECKPOINT_MAGIC[8] = {'V', 'L', 'G', 'P', 'U', 'C', 'K', '2'};

std::string checkpointPath() { return gpuBatch().m_logDir + "/gpu_checkpoint.bin"; }

double checkpointInterval() {
    const char* const envp = std::getenv("VERILATOR_GPU_CHECKPOINT_SEC");
    return envp && gpuBatch().active() ? std::strtod(envp, nullptr) : 0.0;
}

bool checkpointPeek(GpuCheckpointHeader& header) {
    const std::string path = checkpointPath();
    FILE* const fp = std::fopen(path.c_str(), "rb");
    if (!fp) return false;
    const bool ok = std::fread(&header, sizeof(header), 1, fp) == 1
                    && std::memcmp(header.m_magic, GPU_CHECKPOINT_MAGIC, 8) == 0;
    std::fclose(fp);
    return ok;
}

}  // namespace

int VerilatedGpu::batch() {
    static const int s_batch = [] {
        if (gpuBatch().active()) {
            Verilated::threadContextp()->fatalOnError(false);
            return static_cast<int>(gpuBatch().m_jobs.size());
        }
        const char* const envp = std::getenv("VERILATOR_GPU_BATCH");
        const int n = envp ? std::atoi(envp) : 1;
        return n > 0 ? n : 1;
    }();
    return s_batch;
}

const char* VerilatedGpu::jobPlusArg(int copy, const char* prefixp) {
    GpuBatch& b = gpuBatch();
    const std::string want = std::string{"+"} + prefixp;
    const int job = b.active() ? b.jobOf(copy) : -1;
    if (job >= 0) {
        for (const std::string& arg : b.m_jobs[job].m_args) {
            if (arg.compare(0, want.size(), want) == 0) return arg.c_str();
        }
    }
    return Verilated::threadContextp()->commandArgsPlusMatch(prefixp);
}

const uint8_t* VerilatedGpu::activeDevice(int n) {
    if (!s_activeDevp) {
        s_active.assign(n, 1);
        s_activeDevp = static_cast<uint8_t*>(deviceAlloc(n));
        copyToDevice(s_activeDevp, s_active.data(), n);
    }
    return s_activeDevp;
}

int VerilatedGpu::leaderCopy() { return s_leader; }

const char* VerilatedGpu::jobName(int copy) {
    GpuBatch& b = gpuBatch();
    const int job = b.active() ? b.jobOf(copy) : -1;
    if (job >= 0) return b.m_jobs[job].m_name.c_str();
    return "";
}

int VerilatedGpu::currentCopy() { return s_currentCopy; }

int VerilatedGpu::jobArgCount(int copy) {
    GpuBatch& b = gpuBatch();
    const int job = b.active() ? b.jobOf(copy) : -1;
    return job >= 0 ? static_cast<int>(b.m_jobs[job].m_args.size()) : -1;
}

const char* VerilatedGpu::jobArg(int copy, int index) {
    GpuBatch& b = gpuBatch();
    const int job = b.active() ? b.jobOf(copy) : -1;
    if (job < 0 || index < 0 || index >= static_cast<int>(b.m_jobs[job].m_args.size())) {
        return "";
    }
    return b.m_jobs[job].m_args[index].c_str();
}

void* VerilatedGpu::hostAlloc(size_t bytes) {
    void* hostp = nullptr;
    gpuCheck(cudaMallocHost(&hostp, bytes), "cudaMallocHost");
    return hostp;
}

void VerilatedGpu::uploadBroadcast(void* devp, size_t stride, const void* srcp, size_t bytes,
                                   int n, void* stagep) {
    const auto start = std::chrono::steady_clock::now();
    uint8_t* const sp = static_cast<uint8_t*>(stagep);
    for (int i = 0; i < n; ++i) std::memcpy(sp + i * bytes, srcp, bytes);
    gpuCheck(cudaMemcpy2D(devp, stride, sp, bytes, bytes, n, cudaMemcpyHostToDevice),
             "cudaMemcpy2D to device");
    if (s_profile.m_enabled) {
        s_profile.m_uploadSec += secondsSince(start);
        s_profile.m_uploadBytes += bytes * n;
    }
}

void VerilatedGpu::downloadGather(void* dstp, const void* devp, size_t stride, size_t bytes,
                                  int n) {
    const auto start = std::chrono::steady_clock::now();
    gpuCheck(cudaMemcpy2D(dstp, bytes, devp, stride, bytes, n, cudaMemcpyDeviceToHost),
             "cudaMemcpy2D to host");
    if (s_profile.m_enabled) {
        s_profile.m_downloadSec += secondsSince(start);
        s_profile.m_downloadBytes += bytes * n;
    }
}

void VerilatedGpu::checkDivergence(const void* stagep, size_t prefixBytes, size_t compareBytes,
                                   int n) {
    const uint8_t* const sp = static_cast<const uint8_t*>(stagep);
    for (int i = 1; i < n; ++i) {
        const uint8_t* const cp = sp + i * prefixBytes;
        if (std::memcmp(cp, sp, compareBytes) == 0) continue;
        size_t off = 0;
        while (off < compareBytes && cp[off] == sp[off]) ++off;
        gpuFatal("batch copy " + std::to_string(i)
                 + " diverged from copy 0 in shared state at byte " + std::to_string(off));
    }
}

void VerilatedGpu::replayBatch(const void* stagep, size_t prefixBytes, size_t deferOffset,
                               const void* devp, size_t stride, int n, ReplayFn fn, void* userp) {
    static VlGpuDeferBuf* const s_bufp = new VlGpuDeferBuf{};
    const uint8_t* const sp = static_cast<const uint8_t*>(stagep);
    for (int i = 0; i < n; ++i) {
        const VlGpuDeferBuf* const hdrp
            = reinterpret_cast<const VlGpuDeferBuf*>(sp + i * prefixBytes + deferOffset);
        if (hdrp->m_overflow)
            gpuFatal("deferred statement buffer overflow in copy " + std::to_string(i));
        if (!hdrp->m_used) continue;
        s_bufp->m_used = hdrp->m_used;
        s_bufp->m_overflow = 0;
        copyToHost(s_bufp->m_data,
                   static_cast<const uint8_t*>(devp) + i * stride + deferOffset
                       + offsetof(VlGpuDeferBuf, m_data),
                   hdrp->m_used);
        s_currentCopy = i;
        replay(*s_bufp, fn, userp);
    }
    s_currentCopy = 0;
}

extern "C" int vlGpuScatter(const void* aosp, void* soap, int n, int copy, const void* tablep,
                            int count, size_t stride, int mode);

void VerilatedGpu::soaBroadcast(const VlGpuCopy* tablep, const void* aosp, void* stagep, int n) {
    const uint8_t* const fromp = static_cast<const uint8_t*>(aosp);
    uint8_t* const sp = static_cast<uint8_t*>(stagep);
    for (const VlGpuCopy* cp = tablep; cp->m_size; ++cp) {
        uint8_t* top = sp + static_cast<size_t>(n) * cp->m_state;
        for (int i = 0; i < n; ++i, top += cp->m_size)
            std::memcpy(top, fromp + cp->m_state, cp->m_size);
    }
}

void VerilatedGpu::soaCheck(const VlGpuCopy* tablep, const void* stagep, int n) {
    const uint8_t* const sp = static_cast<const uint8_t*>(stagep);
    for (const VlGpuCopy* cp = tablep; cp->m_size; ++cp) {
        const uint8_t* const firstp = sp + static_cast<size_t>(n) * cp->m_state;
        for (int i = 1; i < n; ++i) {
            if (std::memcmp(firstp + i * cp->m_size, firstp, cp->m_size) != 0) {
                gpuFatal("batch copy " + std::to_string(i)
                         + " diverged from copy 0 in shared state at offset "
                         + std::to_string(cp->m_state));
            }
        }
    }
}

void VerilatedGpu::soaExtract(const VlGpuCopy* tablep, const void* stagep, int n, int copy,
                              void* aosp) {
    const uint8_t* const sp = static_cast<const uint8_t*>(stagep);
    uint8_t* const top = static_cast<uint8_t*>(aosp);
    for (const VlGpuCopy* cp = tablep; cp->m_size; ++cp) {
        std::memcpy(top + cp->m_state,
                    sp + static_cast<size_t>(n) * cp->m_state
                        + static_cast<size_t>(copy) * cp->m_size,
                    cp->m_size);
    }
}

void VerilatedGpu::soaDeferReset(void* devp, size_t deferOffset, int n) {
    memberRowsZero(devp, n, deferOffset, sizeof(VlGpuDeferBuf), offsetof(VlGpuDeferBuf, m_data));
}

void VerilatedGpu::soaReplay(const void* devp, size_t deferOffset, int n, ReplayFn fn,
                             void* userp) {
    static std::vector<uint32_t> s_headers;
    static VlGpuDeferBuf* const s_bufp = new VlGpuDeferBuf{};
    s_headers.resize(2 * static_cast<size_t>(n));
    const uint8_t* const basep
        = static_cast<const uint8_t*>(devp) + static_cast<size_t>(n) * deferOffset;
    const auto start = std::chrono::steady_clock::now();
    gpuCheck(cudaMemcpy2D(s_headers.data(), 8, basep, sizeof(VlGpuDeferBuf), 8, n,
                          cudaMemcpyDeviceToHost),
             "cudaMemcpy2D defer headers");
    if (s_profile.m_enabled) {
        s_profile.m_downloadSec += secondsSince(start);
        s_profile.m_downloadBytes += 8 * static_cast<uint64_t>(n);
    }
    for (int i = 0; i < n; ++i) {
        const uint32_t used = s_headers[2 * i];
        const bool overflow = s_headers[2 * i + 1] != 0;
        if (!used && !overflow) continue;
        GpuBatch& b = gpuBatch();
        if (b.active() && (b.jobOf(i) < 0 || b.m_jobs[b.jobOf(i)].m_status)) continue;
        s_bufp->m_used = used;
        s_bufp->m_overflow = 0;
        copyToHost(s_bufp->m_data,
                   basep + static_cast<size_t>(i) * sizeof(VlGpuDeferBuf)
                       + offsetof(VlGpuDeferBuf, m_data),
                   used);
        s_currentCopy = i;
        if (b.active()) b.redirect(i);
        replay(*s_bufp, fn, userp);
        if (overflow) {
            std::fprintf(stderr, "%%Error: GPU output buffer overflow; rebuild with a larger "
                                 "--gpu-output-bytes\n");
            std::fflush(stderr);
        }
        if (b.active()) {
            b.restore();
            VerilatedContext* const contextp = Verilated::threadContextp();
            if (overflow) {
                b.finished(i, true);
                contextp->gotFinish(false);
                contextp->gotError(false);
                contextp->errorCount(0);
            } else if (contextp->gotFinish()) {
                b.finished(i, contextp->gotError());
                contextp->gotFinish(false);
                contextp->gotError(false);
                contextp->errorCount(0);
            }
        }
    }
    s_currentCopy = 0;
    if (gpuBatch().active() && gpuBatch().m_remaining == 0) {
        Verilated::threadContextp()->gotFinish(true);
    }
}

void VerilatedGpu::soaUploadAll(void* devp, int n, int copy, const void* aosp, size_t stride,
                                const VlGpuCopy* sharedp, const VlGpuCopy* devicep) {
    static void* s_aosDevp = nullptr;
    static void* s_tableDevp = nullptr;
    static int s_tableCount = 0;
    if (!s_aosDevp) {
        s_aosDevp = deviceAlloc(stride);
        std::vector<VlGpuCopy> table;
        for (const VlGpuCopy* cp = sharedp; cp->m_size; ++cp) table.push_back(*cp);
        for (const VlGpuCopy* cp = devicep; cp->m_size; ++cp) table.push_back(*cp);
        s_tableCount = static_cast<int>(table.size());
        s_tableDevp = deviceAlloc(sizeof(VlGpuCopy) * (table.size() + 1));
        copyToDevice(s_tableDevp, table.data(), sizeof(VlGpuCopy) * table.size());
    }
    copyToDevice(s_aosDevp, aosp, stride);
    if (vlGpuScatter(s_aosDevp, devp, n, copy, s_tableDevp, s_tableCount, layoutStride(),
                     layoutMode())
        != 0) {
        gpuFatal("state scatter kernel failed");
    }
}

extern "C" int vlGpuBroadcastAsync(const void* aosp, void* soap, int n, const void* tablep,
                                   int count);
extern "C" int vlGpuCheckAsync(const void* soap, int n, const void* tablep, int count,
                               void* leaderp, void* statusp, int check, int leader,
                               const void* activep);
extern "C" int vlGpuDeferPendingReset();

namespace {
struct GpuDeviceTable final {
    void* m_devp = nullptr;  // Table in GPU memory
    int m_count = 0;  // Entries in the table
};

const GpuDeviceTable& deviceTable(const VlGpuCopy* tablep) {
    static std::map<const VlGpuCopy*, GpuDeviceTable> s_tables;
    GpuDeviceTable& entry = s_tables[tablep];
    if (!entry.m_devp) {
        int count = 0;
        while (tablep[count].m_size) ++count;
        entry.m_count = count;
        entry.m_devp = VerilatedGpu::deviceAlloc(sizeof(VlGpuCopy) * (count + 1));
        if (count) VerilatedGpu::copyToDevice(entry.m_devp, tablep, sizeof(VlGpuCopy) * count);
    }
    return entry;
}
}  // namespace

namespace {
std::vector<uint8_t>& gpuDeviceShadow() {
    static std::vector<uint8_t> s_shadow;
    return s_shadow;
}
}  // namespace

void VerilatedGpu::soaPreLaunch(void* devp, int n, size_t deferOffset, const void* aosp,
                                const VlGpuCopy* sharedp) {
#if defined(VL_GPU_LAYOUT_AOS) || defined(VL_GPU_LAYOUT_AOSOA)
    gpuFatal("this GPU state layout needs resident mode");
#endif
    static void* const s_leaderInp = deviceAlloc(deferOffset + 1);
    std::vector<uint8_t>& shadow = gpuDeviceShadow();
    if (shadow.size() == deferOffset && std::memcmp(shadow.data(), aosp, deferOffset) == 0) {
        return;
    }
    const GpuDeviceTable& table = deviceTable(sharedp);
    copyToDevice(s_leaderInp, aosp, deferOffset);
    if (vlGpuBroadcastAsync(s_leaderInp, devp, n, table.m_devp, table.m_count) != 0) {
        gpuFatal("broadcast kernel failed");
    }
}

bool VerilatedGpu::soaPostLaunch(void* devp, int n, size_t deferOffset, void* aosp,
                                 const VlGpuCopy* sharedp) {
    constexpr size_t statusBytes = 16;
    static uint8_t* const s_outp
        = static_cast<uint8_t*>(deviceAlloc(statusBytes + deferOffset + 1));
    static uint8_t* const s_hostp
        = static_cast<uint8_t*>(hostAlloc(statusBytes + deferOffset + 1));
    static const int s_checkEvery = [] {
        const char* const envp = std::getenv("VERILATOR_GPU_CHECK_EVERY");
        const int every = envp ? std::atoi(envp) : 64;
        return every > 0 ? every : 1;
    }();
    static uint64_t s_launch = 0;
    const int check = (n > 1 && (s_launch++ % s_checkEvery) == 0) ? 1 : 0;
    const GpuDeviceTable& table = deviceTable(sharedp);
    if (vlGpuCheckAsync(devp, n, table.m_devp, table.m_count, s_outp + statusBytes, s_outp, check,
                        leaderCopy(), activeDevice(n))
        != 0) {
        gpuFatal("check kernel failed");
    }
    copyToHost(s_hostp, s_outp, statusBytes + deferOffset);
    unsigned int status[3];
    std::memcpy(status, s_hostp, sizeof(status));
    std::memcpy(aosp, s_hostp + statusBytes, deferOffset);
    std::vector<uint8_t>& shadow = gpuDeviceShadow();
    shadow.assign(s_hostp + statusBytes, s_hostp + statusBytes + deferOffset);
    if (status[1]) {
        gpuFatal("batch copy " + std::to_string(status[2])
                 + " diverged from copy 0 in shared state");
    }
    return status[0] != 0;
}

void VerilatedGpu::soaReplayPending(void* devp, size_t deferOffset, int n, ReplayFn fn,
                                    void* userp) {
    soaReplay(devp, deferOffset, n, fn, userp);
    soaDeferReset(devp, deferOffset, n);
    if (vlGpuDeferPendingReset() != 0) gpuFatal("deferred counter reset failed");
}

void VerilatedGpu::dpiCopyInit(int n) {
    if (!vlGpuDpiCopyInit) return;
    for (int i = 0; i < n; ++i) {
        s_currentCopy = i;
        vlGpuDpiCopyInit(i, n);
    }
    s_currentCopy = 0;
}

extern "C" int vlGpuAssertCtlUpload(const void* ctlp);

void VerilatedGpu::assertCtlSync() {
    static_assert(VerilatedContext::ASSERT_CONTROL_SLOT_COUNT <= VlGpuAssertCtl::SLOTS,
                  "assertion control slots exceed the GPU mirror");
    static_assert(VerilatedContext::ASSERT_DIRECTIVE_TYPE_MASK_WIDTH == 3,
                  "GPU assertion mask assumes 3 directive bits per type");
    static VlGpuAssertCtl s_last{};
    static bool s_valid = false;
    if (!s_contextp) return;
    const auto& st = s_contextp->m_s;
    VlGpuAssertCtl now{};
    now.m_on = st.m_assertOn.load();
    now.m_passVacuous = st.m_assertPassOnVacuous.load();
    now.m_passNonvacuous = st.m_assertPassOnNonvacuous.load();
    now.m_failOn = st.m_assertFailOn.load();
    for (size_t i = 0; i < VerilatedContext::ASSERT_CONTROL_SLOT_COUNT; ++i) {
        now.m_kill[i] = st.m_assertKill[i].load();
    }
    if (s_valid && std::memcmp(&now, &s_last, sizeof(now)) == 0) return;
    if (vlGpuAssertCtlUpload(&now) != 0) gpuFatal("assertion control upload failed");
    s_last = now;
    s_valid = true;
}

extern "C" int vlGpuNowRead(uint64_t* nowp);
extern "C" int vlGpuNowWrite(uint64_t now);

int VerilatedGpu::residentSlots(size_t stride, size_t kernelStack) {
    const int jobs = batch();
    int slots = jobs;
    if (const char* const envp = std::getenv("VERILATOR_GPU_SLOTS")) {
        const int limit = std::atoi(envp);
        if (limit > 0 && limit < slots) slots = limit;
    }
    if (kernelStack != ~static_cast<size_t>(0) && !std::getenv("VERILATOR_GPU_STACK")) {
        const size_t want = (kernelStack + 1024 + 15) / 16 * 16;
        gpuCheck(cudaDeviceSetLimit(cudaLimitStackSize, want), "cudaDeviceSetLimit");
    }
    size_t freeBytes = 0;
    size_t totalBytes = 0;
    gpuCheck(cudaMemGetInfo(&freeBytes, &totalBytes), "cudaMemGetInfo");
    int sms = 0;
    int threadsPerSm = 0;
    gpuCheck(cudaDeviceGetAttribute(&sms, cudaDevAttrMultiProcessorCount, 0), "attribute");
    gpuCheck(cudaDeviceGetAttribute(&threadsPerSm, cudaDevAttrMaxThreadsPerMultiProcessor, 0),
             "attribute");
    size_t stack = 0;
    gpuCheck(cudaDeviceGetLimit(&stack, cudaLimitStackSize), "cudaDeviceGetLimit");
    const size_t reserve
        = stack * static_cast<size_t>(sms) * static_cast<size_t>(threadsPerSm) + (384ULL << 20);
    const size_t perCopy = stride + (vlGpuDpiCopyBytes ? vlGpuDpiCopyBytes() : 0) + 256;
#ifdef VL_GPU_LAYOUT_AOSOA
    const size_t rounding = static_cast<size_t>(VL_GPU_LAYOUT_GROUP - 1) * stride;
#else
    const size_t rounding = 0;
#endif
    const long fit = freeBytes > reserve + rounding
                         ? static_cast<long>((freeBytes - reserve - rounding) / perCopy)
                         : 1;
    if (fit < slots) slots = static_cast<int>(fit);
    if (slots < 1) slots = 1;
#if defined(VL_GPU_LAYOUT_AOS)
    layoutStrideRef() = stride;
    layoutModeRef() = 1;
#elif defined(VL_GPU_LAYOUT_AOSOA)
    layoutStrideRef() = stride;
    layoutModeRef() = 2;
#endif
    if (resuming()) {
        GpuCheckpointHeader header{};
        checkpointPeek(header);
        if (header.m_stride != (stride | (static_cast<uint64_t>(layoutMode()) << 62))
            || header.m_jobs != jobs || header.m_jobsHash != gpuBatch().hash()) {
            gpuFatal("checkpoint " + checkpointPath() + " does not match this model and job list");
        }
        if (header.m_n > fit) {
            gpuFatal("checkpoint needs " + std::to_string(header.m_n) + " slots but only "
                     + std::to_string(fit) + " fit in GPU memory");
        }
        slots = header.m_n;
        gpuBatch().m_slotJob.assign(slots, -1);
    } else if (gpuBatch().active()) {
        gpuBatch().initSlots(slots);
    }
    if (std::getenv("VERILATOR_GPU_RESIDENT_STATS")) {
        std::fprintf(stderr,
                     "GPU resident: %d jobs, %d slots (%.1f MB per copy, %.0f MB free, "
                     "%zu B stack)\n",
                     jobs, slots, perCopy / 1048576.0, freeBytes / 1048576.0, stack);
    }
    return slots;
}

void VerilatedGpu::failCopy(int copy, const char* messagep) {
    GpuBatch& b = gpuBatch();
    if (!b.active()) gpuFatal(std::string{"copy "} + std::to_string(copy) + ": " + messagep);
    b.message(copy, std::string{"%Error: "} + messagep + "\n");
    b.finished(copy, true);
}

namespace {
std::set<std::string>& hostPlusargs() {
    static std::set<std::string> s_prefixes;
    return s_prefixes;
}

bool jobPlusargsShared(int copy) {
    GpuBatch& b = gpuBatch();
    const int job = b.active() ? b.jobOf(copy) : -1;
    if (job < 0) return true;
    VerilatedContext* const contextp = Verilated::threadContextp();
    for (const std::string& prefix : hostPlusargs()) {
        const std::string want = "+" + prefix;
        for (const std::string& arg : b.m_jobs[job].m_args) {
            if (arg.compare(0, want.size(), want) != 0) continue;
            const char* const sharedp = contextp->commandArgsPlusMatch(prefix.c_str());
            if (arg == (sharedp ? sharedp : "")) continue;
            const std::string msg = "job argument " + arg
                                    + " is read by the design during initialization, which "
                                      "all GPU copies share; give it on the command line or "
                                      "read it in GPU DPI code";
            VerilatedGpu::failCopy(copy, msg.c_str());
            return false;
        }
    }
    return true;
}

void recordPlusarg(const char* prefixp) {
    if (prefixp && *prefixp) hostPlusargs().insert(prefixp);
}

void residentInitCopy(int copy, int n) {
    if (!jobPlusargsShared(copy)) return;
    s_currentCopy = copy;
    if (vlGpuDpiCopyInit) vlGpuDpiCopyInit(copy, n);
    s_currentCopy = 0;
}
}  // namespace

void VerilatedGpu::residentRun(void* devp, int n, const VlGpuResidentModel& model) {
    const auto start = std::chrono::steady_clock::now();
    GpuBatch& b = gpuBatch();
    VerilatedContext* const contextp = Verilated::threadContextp();
    const uint64_t snapshotTime = contextp->time();
    VlGpuResidentCtl ctl{};
    for (uint64_t& v : ctl.m_reduce) v = ~0ULL;
    int timeout = 0;
    gpuCheck(cudaDeviceGetAttribute(&timeout, cudaDevAttrKernelExecTimeout, 0),
             "cudaDeviceGetAttribute");
    const bool refill = b.active() && b.pending();
    const char* const sliceEnvp = std::getenv("VERILATOR_GPU_SLICE_MS");
    const uint64_t sliceMs
        = sliceEnvp ? std::strtoull(sliceEnvp, nullptr, 0) : ((timeout || b.active()) ? 300 : 0);
    ctl.m_sliceNs = sliceMs * 1000000ULL;
    ctl.m_convergeLimit = model.m_convergeLimit;
    ctl.m_levelMode = std::getenv("VERILATOR_GPU_LEVELS") ? 1 : 0;
    ctl.m_noSeq = std::getenv("VERILATOR_GPU_NOSEQ") ? 1 : 0;
    ctl.m_noSplit = std::getenv("VERILATOR_GPU_NOSPLIT") ? 1 : 0;
    const char* const stopEnvp = std::getenv("VERILATOR_GPU_DUMP_TIME");
    ctl.m_stopTime = stopEnvp ? std::strtoull(stopEnvp, nullptr, 0) : ~0ULL;
    const char* const flowEnvp = std::getenv("VERILATOR_GPU_FLOW_MAX");
    ctl.m_flowMax = flowEnvp ? static_cast<uint32_t>(std::strtoul(flowEnvp, nullptr, 0)) : 2048U;
    const size_t loops = static_cast<size_t>(VlGpuResidentCtl::LOOPS) * n;
    const auto zeroed = [](size_t bytes) {
        void* const p = deviceAlloc(bytes);
        gpuCheck(cudaMemset(p, 0, bytes), "cudaMemset");
        return p;
    };
    ctl.m_runp = static_cast<uint32_t*>(zeroed(loops * 4));
    ctl.m_iterp = static_cast<uint32_t*>(zeroed(loops * 4));
    ctl.m_wantp = static_cast<uint32_t*>(zeroed(static_cast<size_t>(n) * 4));
    ctl.m_errorp = static_cast<uint32_t*>(zeroed(static_cast<size_t>(n) * 4));
    ctl.m_steppingp = static_cast<uint32_t*>(zeroed(static_cast<size_t>(n) * 4));
    ctl.m_nextp = static_cast<uint64_t*>(zeroed(static_cast<size_t>(n) * 8));
    const char* const timesEnvp = std::getenv("VERILATOR_GPU_RESIDENT_TIMES");
    if (timesEnvp) {
        ctl.m_stepTimesMax = 1ULL << 22;
        ctl.m_stepTimesp = static_cast<uint64_t*>(zeroed(8 * ctl.m_stepTimesMax));
    }
    VlGpuResidentCtl* const ctlDevp = static_cast<VlGpuResidentCtl*>(deviceAlloc(sizeof(ctl)));
    copyToDevice(ctlDevp, &ctl, sizeof(ctl));
    const void* const activep = activeDevice(n);
    std::vector<uint64_t> timeBase(n, 0);
    std::vector<uint8_t> drainFailed(n, 0);
    GpuCheckpointHeader resumed{};
    if (resuming()) {
        const auto loadStart = std::chrono::steady_clock::now();
        const std::string path = checkpointPath();
        FILE* const fp = std::fopen(path.c_str(), "rb");
        if (!fp) gpuFatal("cannot open " + path);
        checkpointRead(fp, &resumed, sizeof(resumed));
        for (GpuJob& job : b.m_jobs) {
            int32_t status = 0;
            checkpointRead(fp, &status, sizeof(status));
            checkpointRead(fp, &job.m_finishTime, sizeof(job.m_finishTime));
            job.m_status = status;
            if (status && job.m_logFd >= 0) {
                ::close(job.m_logFd);
                job.m_logFd = -1;
            }
        }
        std::vector<int32_t> slotJob(n);
        checkpointRead(fp, slotJob.data(), 4 * static_cast<size_t>(n));
        b.m_slotJob.assign(slotJob.begin(), slotJob.end());
        int32_t counts[2] = {0, 0};
        checkpointRead(fp, counts, sizeof(counts));
        b.m_nextJob = counts[0];
        b.m_remaining = counts[1];
        std::vector<uint8_t> active(n);
        checkpointRead(fp, active.data(), static_cast<size_t>(n));
        for (int slot = 0; slot < n; ++slot) {
            if (active[slot]) {
                gpuActivate(slot);
            } else {
                gpuDeactivate(slot);
            }
            if (b.m_slotJob[slot] >= 0) b.startLog(b.m_slotJob[slot]);
        }
        checkpointRead(fp, timeBase.data(), 8 * static_cast<size_t>(n));
        checkpointReadDevice(fp, devp, stateBytes(model.m_stride, n));
        checkpointReadDevice(fp, ctl.m_errorp, 4 * static_cast<size_t>(n));
        checkpointRead(fp, drainFailed.data(), static_cast<size_t>(n));
        if (vlGpuNowWrite(resumed.m_now) != 0) gpuFatal("cannot set device time");
        if (vlGpuDpiCheckpointLoad) vlGpuDpiCheckpointLoad(fp, n);
        std::fclose(fp);
        int done = 0;
        for (const GpuJob& job : b.m_jobs) done += job.m_status ? 1 : 0;
        std::fprintf(stderr,
                     "GPU resident: resumed from %s at time %" PRIu64
                     ", %d of %zu jobs done, %.1f s\n",
                     path.c_str(), static_cast<uint64_t>(resumed.m_now), done, b.m_jobs.size(),
                     secondsSince(loadStart));
    } else {
        for (int slot = 0; slot < n; ++slot) {
            if (b.active() && b.jobOf(slot) < 0) {
                gpuDeactivate(slot);
                continue;
            }
            residentInitCopy(slot, n);
        }
    }
    std::vector<uint32_t> finishes(n);
    std::vector<uint32_t> errors(n);
    std::vector<uint32_t> fatals(n);
    std::string fatalWhy;
    VlGpuDeferBuf* const bufp = new VlGpuDeferBuf{};
    bool copyAborted = false;
    std::vector<uint32_t> drainHeaders(2 * static_cast<size_t>(n));
    const auto deferAt = [&](int slot) {
        return memberAt(devp, n, slot, model.m_deferOffset, sizeof(VlGpuDeferBuf));
    };
    const auto drain = [&]() {
        memberRows(drainHeaders.data(), 8, devp, n, model.m_deferOffset, sizeof(VlGpuDeferBuf));
        for (int slot = 0; slot < n; ++slot) {
            const uint32_t used = drainHeaders[2 * slot];
            if (used < VlGpuDeferBuf::SIZE / 8) continue;
            if (!s_active.empty() && !s_active[slot]) continue;
            if (b.active() && b.jobOf(slot) < 0) continue;
            uint8_t* const slotDeferp = deferAt(slot);
            bufp->m_used = used;
            bufp->m_overflow = 0;
            copyToHost(bufp->m_data, slotDeferp + offsetof(VlGpuDeferBuf, m_data), used);
            const uint32_t zero = 0;
            copyToDevice(slotDeferp, &zero, sizeof(zero));
            if (b.active()) b.redirect(slot);
            s_currentCopy = slot;
            s_residentReplay = true;
            s_replayTimeBase = timeBase[slot];
            replay(*bufp, model.m_replay, model.m_userp);
            s_residentReplay = false;
            s_replayTimeBase = 0;
            s_currentCopy = 0;
            if (contextp->gotError()) drainFailed[slot] = 1;
            if (b.active()) b.restore();
            contextp->gotError(false);
            contextp->errorCount(0);
        }
    };
    const auto harvest = [&](int slot, const char* whyp, bool abort = true) {
        uint32_t header[2] = {0, 0};
        uint8_t* const slotDeferp = deferAt(slot);
        copyToHost(header, slotDeferp, sizeof(header));
        bufp->m_used = header[0];
        bufp->m_overflow = header[1];
        if (bufp->m_used) {
            copyToHost(bufp->m_data, slotDeferp + offsetof(VlGpuDeferBuf, m_data), bufp->m_used);
        }
        if (b.active()) b.redirect(slot);
        s_currentCopy = slot;
        s_residentReplay = true;
        s_replayTimeBase = timeBase[slot];
        replay(*bufp, model.m_replay, model.m_userp);
        s_residentReplay = false;
        s_replayTimeBase = 0;
        s_currentCopy = 0;
        bool failed = contextp->gotError() || drainFailed[slot];
        drainFailed[slot] = 0;
        if (bufp->m_overflow) {
            std::fprintf(stderr, "%%Error: GPU output buffer overflow; rebuild with a larger "
                                 "--gpu-output-bytes\n");
            failed = true;
            copyAborted = true;
        }
        if (whyp) {
            std::fprintf(stderr, "%%Error: %s\n", whyp);
            failed = true;
            if (abort) copyAborted = true;
        }
        std::fflush(stdout);
        std::fflush(stderr);
        if (b.active()) {
            b.restore();
            b.finished(slot, failed);
            contextp->gotFinish(false);
            contextp->gotError(false);
            contextp->errorCount(0);
        } else {
            gpuDeactivate(slot);
        }
    };
    uint64_t launches = 0;
    uint64_t refills = resumed.m_refills;
    uint64_t harvested = resumed.m_harvested;
    const double checkpointSec = checkpointInterval();
    auto lastCheckpoint = std::chrono::steady_clock::now();
    const auto saveCheckpoint = [&]() {
        const auto saveStart = std::chrono::steady_clock::now();
        const std::string path = checkpointPath();
        const std::string tmp = path + ".tmp";
        FILE* const fp = std::fopen(tmp.c_str(), "wb");
        if (!fp) gpuFatal("cannot create " + tmp);
        GpuCheckpointHeader header{};
        std::memcpy(header.m_magic, GPU_CHECKPOINT_MAGIC, 8);
        header.m_stride = model.m_stride | (static_cast<uint64_t>(layoutMode()) << 62);
        header.m_n = n;
        header.m_jobs = static_cast<int32_t>(b.m_jobs.size());
        header.m_jobsHash = b.hash();
        if (vlGpuNowRead(&header.m_now) != 0) gpuFatal("cannot read device time");
        header.m_refills = refills;
        header.m_harvested = harvested;
        checkpointWrite(fp, &header, sizeof(header));
        for (const GpuJob& job : b.m_jobs) {
            const int32_t status = job.m_status;
            checkpointWrite(fp, &status, sizeof(status));
            checkpointWrite(fp, &job.m_finishTime, sizeof(job.m_finishTime));
        }
        std::vector<int32_t> slotJob(n, -1);
        for (int slot = 0; slot < n; ++slot) slotJob[slot] = b.jobOf(slot);
        checkpointWrite(fp, slotJob.data(), 4 * static_cast<size_t>(n));
        const int32_t counts[2] = {b.m_nextJob, b.m_remaining};
        checkpointWrite(fp, counts, sizeof(counts));
        std::vector<uint8_t> active(n, 1);
        for (int slot = 0; slot < n && !s_active.empty(); ++slot) active[slot] = s_active[slot];
        checkpointWrite(fp, active.data(), static_cast<size_t>(n));
        checkpointWrite(fp, timeBase.data(), 8 * static_cast<size_t>(n));
        checkpointWriteDevice(fp, devp, stateBytes(model.m_stride, n));
        checkpointWriteDevice(fp, ctl.m_errorp, 4 * static_cast<size_t>(n));
        checkpointWrite(fp, drainFailed.data(), static_cast<size_t>(n));
        if (vlGpuDpiCheckpointSave) vlGpuDpiCheckpointSave(fp, n);
        const long bytes = std::ftell(fp);
        if (std::fflush(fp) != 0 || ::fsync(::fileno(fp)) != 0)
            gpuFatal("checkpoint write failed");
        std::fclose(fp);
        if (std::rename(tmp.c_str(), path.c_str()) != 0) gpuFatal("cannot rename " + tmp);
        std::fprintf(stderr, "GPU resident: checkpoint %.2f GB in %.1f s\n", bytes / 1e9,
                     secondsSince(saveStart));
        std::fflush(stderr);
    };
    const bool trace = std::getenv("VERILATOR_GPU_RESIDENT_TRACE") != nullptr;
    const bool progress = std::getenv("VERILATOR_GPU_RESIDENT_STATS") != nullptr;
    auto lastProgress = std::chrono::steady_clock::now();
    for (;;) {
        const auto sliceStart = std::chrono::steady_clock::now();
        if (model.m_launch(devp, n, activep, ctlDevp) != 0) {
            gpuFatal(std::string{"resident kernel launch failed: "}
                     + cudaGetErrorString(cudaGetLastError()));
        }
        gpuCheck(cudaDeviceSynchronize(), "resident kernel");
        ++launches;
        uint32_t done = 0;
        gpuCheck(cudaMemcpy(&done, &ctlDevp->m_done, sizeof(done), cudaMemcpyDeviceToHost),
                 "cudaMemcpy done");
        if (trace) {
            uint64_t sofar = 0;
            gpuCheck(cudaMemcpy(&sofar, &ctlDevp->m_steps, sizeof(sofar), cudaMemcpyDeviceToHost),
                     "cudaMemcpy steps");
            std::fprintf(stderr, "GPU resident slice %" PRIu64 ": %.3f s, %" PRIu64 " steps\n",
                         static_cast<uint64_t>(launches), secondsSince(sliceStart),
                         static_cast<uint64_t>(sofar));
        }
        memberRead(finishes.data(), devp, n, model.m_finishOffset, 4);
        copyToHost(errors.data(), ctl.m_errorp, 4 * static_cast<size_t>(n));
        memberRead(fatals.data(), devp, n, model.m_fatalOffset, 4);
        bool busy = false;
        for (int slot = 0; slot < n; ++slot) {
            if (!s_active.empty() && !s_active[slot]) continue;
            if (b.active() && b.jobOf(slot) < 0) continue;
            if (fatals[slot]) {
                const uint32_t code = fatals[slot];
                fatalWhy
                    = std::string{"GPU copy hit a fatal error: "}
                      + (code <= model.m_fatalCount ? model.m_fatalMsgsp[code - 1] : "unknown");
                harvest(slot, fatalWhy.c_str());
            } else if (errors[slot]) {
                harvest(slot, errors[slot] == VL_GPU_ERR_CONVERGE
                                  ? "GPU copy did not converge"
                                  : "GPU copy ran out of fork slots (raise --gpu-fork-slots)");
            } else if (finishes[slot]) {
                harvest(slot, nullptr);
                ++harvested;
            } else if (done) {
                harvest(slot, "simulation ended without $finish", false);
            } else {
                busy = true;
            }
        }
        drain();
        bool refilled = false;
        if (b.active() && b.pending()) {
            uint64_t globalNow = 0;
            if (vlGpuNowRead(&globalNow) != 0) gpuFatal("cannot read device time");
            for (int slot = 0; slot < n && b.pending(); ++slot) {
                if (b.jobOf(slot) >= 0) continue;
                b.assign(slot);
                soaUploadAll(devp, n, slot, model.m_snapshotp, model.m_stride, model.m_sharedp,
                             model.m_devicep);
                gpuCheck(cudaMemset(deferAt(slot), 0, offsetof(VlGpuDeferBuf, m_data)),
                         "cudaMemset defer");
                timeBase[slot] = globalNow > snapshotTime ? globalNow - snapshotTime : 0;
                copyToDevice(memberAt(devp, n, slot, model.m_tbaseOffset, 8), &timeBase[slot], 8);
                gpuCheck(cudaMemset(ctl.m_errorp + slot, 0, 4), "cudaMemset error");
                gpuCheck(cudaMemset(ctl.m_wantp + slot, 0, 4), "cudaMemset want");
                gpuActivate(slot);
                residentInitCopy(slot, n);
                if (b.jobOf(slot) >= 0) {
                    refilled = true;
                    busy = true;
                    ++refills;
                }
            }
        }
        if (progress && secondsSince(lastProgress) > 30.0) {
            lastProgress = std::chrono::steady_clock::now();
            uint64_t sofar = 0;
            gpuCheck(cudaMemcpy(&sofar, &ctlDevp->m_steps, sizeof(sofar), cudaMemcpyDeviceToHost),
                     "cudaMemcpy steps");
            int running = 0;
            for (int slot = 0; slot < n; ++slot) {
                if (s_active.empty() || s_active[slot]) ++running;
            }
            std::fprintf(stderr,
                         "GPU resident progress: %.0f s, %" PRIu64
                         " finished, %d running, %" PRIu64 " steps\n",
                         secondsSince(start), static_cast<uint64_t>(harvested), running,
                         static_cast<uint64_t>(sofar));
            std::fflush(stderr);
        }
        if (done) {
            if (!refilled) break;
            const uint32_t zero = 0;
            copyToDevice(&ctlDevp->m_done, &zero, sizeof(zero));
        } else if (!busy && !refilled) {
            break;
        }
        if (checkpointSec > 0.0 && secondsSince(lastCheckpoint) > checkpointSec) {
            saveCheckpoint();
            lastCheckpoint = std::chrono::steady_clock::now();
        }
    }
    if (stopEnvp && n == 1) {
        std::vector<uint8_t> state(model.m_stride);
        copyToHost(state.data(), devp, model.m_stride);
        dumpState(dumpPath(), state.data(), model.m_stride, model.m_sharedp, model.m_sharedNamesp,
                  model.m_devicep, model.m_deviceNamesp);
        std::exit(0);
    }
    delete bufp;
    const double gpuSec = secondsSince(start);
    if (s_profile.m_enabled || std::getenv("VERILATOR_GPU_RESIDENT_STATS")) {
        VlGpuResidentCtl fin{};
        gpuCheck(cudaMemcpy(&fin, ctlDevp, sizeof(fin), cudaMemcpyDeviceToHost), "cudaMemcpy ctl");
        std::fprintf(stderr,
                     "GPU resident: %d slots, %" PRIu64 " refills, %" PRIu64
                     " time steps, %" PRIu64 " launches, "
                     "%.3f s; steps %.3f s, graph %.3f s in %" PRIu64 " runs (%" PRIu64
                     " sequential)\n",
                     n, static_cast<uint64_t>(refills), static_cast<uint64_t>(fin.m_steps),
                     static_cast<uint64_t>(launches), gpuSec, fin.m_profStepNs * 1e-9,
                     fin.m_profGraphNs * 1e-9, static_cast<uint64_t>(fin.m_profGraphRuns),
                     static_cast<uint64_t>(fin.m_profSeqRuns));
        std::fprintf(stderr, "GPU resident regions (s/calls):");
        for (int r = 0; r < 8; ++r) {
            if (fin.m_regionCalls[r]) {
                std::fprintf(stderr, " r%d %.3f/%" PRIu64 "", r, fin.m_regionNs[r] * 1e-9,
                             static_cast<uint64_t>(fin.m_regionCalls[r]));
            }
        }
        std::fprintf(stderr, "\n");
        if (timesEnvp) {
            std::vector<uint64_t> times(std::min<uint64_t>(fin.m_steps, ctl.m_stepTimesMax));
            gpuCheck(cudaMemcpy(times.data(), ctl.m_stepTimesp, 8 * times.size(),
                                cudaMemcpyDeviceToHost),
                     "cudaMemcpy step times");
            if (FILE* const fp = std::fopen(timesEnvp, "w")) {
                for (const uint64_t t : times) {
                    std::fprintf(fp, "%" PRIu64 "\n", static_cast<uint64_t>(t));
                }
                std::fclose(fp);
            }
        }
    }
    if (b.active() && b.m_remaining > 0) b.writeSummary();
    if (b.active() && b.m_remaining == 0 && checkpointSec > 0.0) {
        const std::string path = checkpointPath();
        std::remove(path.c_str());
    }
    if (copyAborted && !b.active()) {
        std::fprintf(stderr, "Aborting...\n");
        std::fflush(stderr);
        std::exit(1);
    }
    contextp->gotFinish(true);
}

bool VerilatedGpu::residentEnabled() {
    static const bool s_enabled = [] {
        const char* const envp = std::getenv("VERILATOR_GPU_RESIDENT");
        return !envp || std::atoi(envp) != 0;
    }();
    return s_enabled;
}

void VerilatedGpu::hostStep(uint64_t time) {
    static FILE* const s_fp = [] {
        const char* const envp = std::getenv("VERILATOR_GPU_HOST_TIMES");
        return envp ? std::fopen(envp, "w") : nullptr;
    }();
    if (s_fp) std::fprintf(s_fp, "%" PRIu64 "\n", static_cast<uint64_t>(time));
}

const char* VerilatedGpu::dumpPath() {
    const char* const envp = std::getenv("VERILATOR_GPU_DUMP_FILE");
    return envp ? envp : "gpu_state.bin";
}

bool VerilatedGpu::hostDumpDue(uint64_t time) {
    static const char* const s_envp = std::getenv("VERILATOR_GPU_DUMP_TIME");
    if (!s_envp || residentEnabled()) return false;
    static const uint64_t s_stop = std::strtoull(s_envp, nullptr, 0);
    return time > s_stop;
}

void VerilatedGpu::dumpState(const char* pathp, const void* statep, size_t bytes,
                             const VlGpuCopy* sharedp, const char* const* sharedNamesp,
                             const VlGpuCopy* devicep, const char* const* deviceNamesp) {
    if (FILE* const fp = std::fopen(pathp, "wb")) {
        std::fwrite(statep, 1, bytes, fp);
        std::fclose(fp);
    }
    const std::string mapPath = std::string{pathp} + ".map";
    if (FILE* const fp = std::fopen(mapPath.c_str(), "w")) {
        for (int t = 0; t < 2; ++t) {
            const VlGpuCopy* const tablep = t ? devicep : sharedp;
            const char* const* const namesp = t ? deviceNamesp : sharedNamesp;
            for (int i = 0; tablep && tablep[i].m_size; ++i) {
                std::fprintf(fp, "%zu %zu %s\n", tablep[i].m_state, tablep[i].m_size,
                             namesp ? namesp[i] : "?");
            }
        }
        std::fclose(fp);
    }
}

void VerilatedGpu::checkpointWrite(FILE* fp, const void* datap, size_t bytes) {
    if (bytes && std::fwrite(datap, 1, bytes, fp) != bytes) gpuFatal("checkpoint write failed");
}

void VerilatedGpu::checkpointRead(FILE* fp, void* datap, size_t bytes) {
    if (bytes && std::fread(datap, 1, bytes, fp) != bytes) gpuFatal("checkpoint is truncated");
}

void VerilatedGpu::checkpointWriteDevice(FILE* fp, const void* devp, size_t bytes) {
    constexpr size_t CHUNK = 64ULL << 20;
    std::vector<uint8_t> buf(std::min(bytes, CHUNK));
    for (size_t done = 0; done < bytes;) {
        const size_t len = std::min(CHUNK, bytes - done);
        gpuCheck(cudaMemcpy(buf.data(), static_cast<const uint8_t*>(devp) + done, len,
                            cudaMemcpyDeviceToHost),
                 "cudaMemcpy checkpoint");
        checkpointWrite(fp, buf.data(), len);
        done += len;
    }
}

void VerilatedGpu::checkpointReadDevice(FILE* fp, void* devp, size_t bytes) {
    constexpr size_t CHUNK = 64ULL << 20;
    std::vector<uint8_t> buf(std::min(bytes, CHUNK));
    for (size_t done = 0; done < bytes;) {
        const size_t len = std::min(CHUNK, bytes - done);
        checkpointRead(fp, buf.data(), len);
        gpuCheck(cudaMemcpy(static_cast<uint8_t*>(devp) + done, buf.data(), len,
                            cudaMemcpyHostToDevice),
                 "cudaMemcpy restore");
        done += len;
    }
}

bool VerilatedGpu::resuming() {
    static const bool s_resuming = [] {
        if (!gpuBatch().active() || !std::getenv("VERILATOR_GPU_RESUME")) return false;
        GpuCheckpointHeader header{};
        return checkpointPeek(header);
    }();
    return s_resuming;
}

size_t VerilatedGpu::stateBytes(size_t stride, int n) {
#if defined(VL_GPU_LAYOUT_AOSOA)
    constexpr size_t G = VL_GPU_LAYOUT_GROUP;
    return stride * ((static_cast<size_t>(n) + G - 1) / G * G);
#else
    return stride * static_cast<size_t>(n);
#endif
}
