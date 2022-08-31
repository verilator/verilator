// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated internal common-tracing header
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated tracing routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_TRACE_H_
#define VERILATOR_VERILATED_TRACE_H_

// clang-format off

#include "verilated.h"
#include "verilated_trace_defs.h"

#include <bitset>
#include <condition_variable>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifdef VL_THREADED
# include <deque>
# include <thread>
#endif

// clang-format on

class VlThreadPool;
template <class T_Buffer>
class VerilatedTraceBuffer;
template <class T_Buffer>
class VerilatedTraceOffloadBuffer;

#ifdef VL_THREADED
//=============================================================================
// Offloaded tracing

// A simple synchronized first in first out queue
template <class T>
class VerilatedThreadQueue final {  // LCOV_EXCL_LINE  // lcov bug
private:
    mutable VerilatedMutex m_mutex;  // Protects m_queue
    std::condition_variable_any m_cv;
    std::deque<T> m_queue VL_GUARDED_BY(m_mutex);

public:
    // Put an element at the back of the queue
    void put(T value) VL_MT_SAFE_EXCLUDES(m_mutex) {
        const VerilatedLockGuard lock{m_mutex};
        m_queue.push_back(value);
        m_cv.notify_one();
    }

    // Put an element at the front of the queue
    void put_front(T value) VL_MT_SAFE_EXCLUDES(m_mutex) {
        const VerilatedLockGuard lock{m_mutex};
        m_queue.push_front(value);
        m_cv.notify_one();
    }

    // Get an element from the front of the queue. Blocks if none available
    T get() VL_MT_SAFE_EXCLUDES(m_mutex) {
        VerilatedLockGuard lock{m_mutex};
        m_cv.wait(lock, [this]() VL_REQUIRES(m_mutex) { return !m_queue.empty(); });
        assert(!m_queue.empty());
        T value = m_queue.front();
        m_queue.pop_front();
        return value;
    }

    // Non blocking get
    bool tryGet(T& result) VL_MT_SAFE_EXCLUDES(m_mutex) {
        const VerilatedLockGuard lockGuard{m_mutex};
        if (m_queue.empty()) return false;
        result = m_queue.front();
        m_queue.pop_front();
        return true;
    }
};

// Commands used by thread tracing. Anonymous enum in class, as we want
// it scoped, but we also want the automatic conversion to integer types.
class VerilatedTraceOffloadCommand final {
public:
    // These must all fit in 4 bit at the moment, as the tracing routines
    // pack parameters in the top bits.
    enum : uint8_t {
        CHG_BIT_0 = 0x0,
        CHG_BIT_1 = 0x1,
        CHG_CDATA = 0x2,
        CHG_SDATA = 0x3,
        CHG_IDATA = 0x4,
        CHG_QDATA = 0x5,
        CHG_WDATA = 0x6,
        CHG_DOUBLE = 0x8,
        // TODO: full..
        TIME_CHANGE = 0xc,
        TRACE_BUFFER = 0xd,
        END = 0xe,  // End of buffer
        SHUTDOWN = 0xf  // Shutdown worker thread, also marks end of buffer
    };
};
#endif

//=============================================================================
// VerilatedTraceConfig

// Simple data representing trace configuration required by generated models.
class VerilatedTraceConfig final {
public:
    const bool m_useParallel;  // Use parallel tracing
    const bool m_useOffloading;  // Offloading trace rendering
    const bool m_useFstWriterThread;  // Use the separate FST writer thread

    VerilatedTraceConfig(bool useParallel, bool useOffloading, bool useFstWriterThread)
        : m_useParallel{useParallel}
        , m_useOffloading{useOffloading}
        , m_useFstWriterThread{useFstWriterThread} {}
};

//=============================================================================
// VerilatedTrace

// T_Trace is the format specific subclass of VerilatedTrace.
// T_Buffer is the format specific base class of VerilatedTraceBuffer.
template <class T_Trace, class T_Buffer>
class VerilatedTrace VL_NOT_FINAL {
public:
    using Buffer = VerilatedTraceBuffer<T_Buffer>;
    using OffloadBuffer = VerilatedTraceOffloadBuffer<T_Buffer>;

    //=========================================================================
    // Generic tracing internals

    using initCb_t = void (*)(void*, T_Trace*, uint32_t);  // Type of init callbacks
    using dumpCb_t = void (*)(void*, Buffer*);  // Type of dump callbacks
    using dumpOffloadCb_t = void (*)(void*, OffloadBuffer*);  // Type of offload dump callbacks
    using cleanupCb_t = void (*)(void*, T_Trace*);  // Type of cleanup callbacks

private:
    // Give the buffer (both base and derived) access to the private bits
    friend T_Buffer;
    friend Buffer;
    friend OffloadBuffer;

    struct CallbackRecord {
        // Note: would make these fields const, but some old STL implementations
        // (the one in Ubuntu 14.04 with GCC 4.8.4 in particular) use the
        // assignment operator on inserting into collections, so they don't work
        // with const fields...
        union {  // The callback
            initCb_t m_initCb;
            dumpCb_t m_dumpCb;
            dumpOffloadCb_t m_dumpOffloadCb;
            cleanupCb_t m_cleanupCb;
        };
        void* m_userp;  // The user pointer to pass to the callback (the symbol table)
        CallbackRecord(initCb_t cb, void* userp)
            : m_initCb{cb}
            , m_userp{userp} {}
        CallbackRecord(dumpCb_t cb, void* userp)
            : m_dumpCb{cb}
            , m_userp{userp} {}
        CallbackRecord(dumpOffloadCb_t cb, void* userp)
            : m_dumpOffloadCb{cb}
            , m_userp{userp} {}
        CallbackRecord(cleanupCb_t cb, void* userp)
            : m_cleanupCb{cb}
            , m_userp{userp} {}
    };

    bool m_offload = false;  // Use the offload thread (ignored if !VL_THREADED)
    bool m_parallel = false;  // Use parallel tracing (ignored if !VL_THREADED)

#ifdef VL_THREADED
    struct ParallelWorkerData {
        const dumpCb_t m_cb;  // The callback
        void* const m_userp;  // The use pointer to pass to the callback
        Buffer* const m_bufp;  // The buffer pointer to pass to the callback
        std::atomic<bool> m_ready{false};  // The ready flag
        mutable VerilatedMutex m_mutex;  // Mutex for suspension until ready
        std::condition_variable_any m_cv;  // Condition variable for suspension
        bool m_waiting VL_GUARDED_BY(m_mutex) = false;  // Whether a thread is suspended in wait()

        void wait();

        ParallelWorkerData(dumpCb_t cb, void* userp, Buffer* bufp)
            : m_cb{cb}
            , m_userp{userp}
            , m_bufp{bufp} {}
    };

    // Passed a ParallelWorkerData*, second argument is ignored
    static void parallelWorkerTask(void*, bool);
#endif

protected:
    uint32_t* m_sigs_oldvalp = nullptr;  // Previous value store
    EData* m_sigs_enabledp = nullptr;  // Bit vector of enabled codes (nullptr = all on)
private:
    std::vector<bool> m_sigs_enabledVec;  // Staging for m_sigs_enabledp
    std::vector<CallbackRecord> m_initCbs;  // Routines to initialize tracing
    std::vector<CallbackRecord> m_fullCbs;  // Routines to perform full dump
    std::vector<CallbackRecord> m_fullOffloadCbs;  // Routines to perform offloaded full dump
    std::vector<CallbackRecord> m_chgCbs;  // Routines to perform incremental dump
    std::vector<CallbackRecord> m_chgOffloadCbs;  // Routines to perform offloaded incremental dump
    std::vector<CallbackRecord> m_cleanupCbs;  // Routines to call at the end of dump
    bool m_fullDump = true;  // Whether a full dump is required on the next call to 'dump'
    uint32_t m_nextCode = 0;  // Next code number to assign
    uint32_t m_numSignals = 0;  // Number of distinct signals
    uint32_t m_maxBits = 0;  // Number of bits in the widest signal
    std::vector<std::string> m_namePrefixStack{""};  // Path prefixes to add to signal names
    std::vector<std::pair<int, std::string>> m_dumpvars;  // dumpvar() entries
    char m_scopeEscape = '.';
    double m_timeRes = 1e-9;  // Time resolution (ns/ms etc)
    double m_timeUnit = 1e-0;  // Time units (ns/ms etc)
    uint64_t m_timeLastDump = 0;  // Last time we did a dump
    bool m_didSomeDump = false;  // Did at least one dump (i.e.: m_timeLastDump is valid)
    VerilatedContext* m_contextp = nullptr;  // The context used by the traced models
    std::unordered_set<const VerilatedModel*> m_models;  // The collection of models being traced

    void addCallbackRecord(std::vector<CallbackRecord>& cbVec, CallbackRecord&& cbRec)
        VL_MT_SAFE_EXCLUDES(m_mutex);

    // Equivalent to 'this' but is of the sub-type 'T_Trace*'. Use 'self()->'
    // to access duck-typed functions to avoid a virtual function call.
    T_Trace* self() { return static_cast<T_Trace*>(this); }

    void runCallbacks(const std::vector<CallbackRecord>& cbVec);
    void runOffloadedCallbacks(const std::vector<CallbackRecord>& cbVec);

    // Flush any remaining data for this file
    static void onFlush(void* selfp) VL_MT_UNSAFE_ONE;
    // Close the file on termination
    static void onExit(void* selfp) VL_MT_UNSAFE_ONE;

#ifdef VL_THREADED
    // Number of total offload buffers that have been allocated
    uint32_t m_numOffloadBuffers = 0;
    // Size of offload buffers
    size_t m_offloadBufferSize = 0;
    // Buffers handed to worker for processing
    VerilatedThreadQueue<uint32_t*> m_offloadBuffersToWorker;
    // Buffers returned from worker after processing
    VerilatedThreadQueue<uint32_t*> m_offloadBuffersFromWorker;

protected:
    // Write pointer into current buffer
    uint32_t* m_offloadBufferWritep = nullptr;
    // End of offload buffer
    uint32_t* m_offloadBufferEndp = nullptr;

private:
    // The offload worker thread itself
    std::unique_ptr<std::thread> m_workerThread;

    // Get a new offload buffer that can be populated. May block if none available
    uint32_t* getOffloadBuffer();

    // The function executed by the offload worker thread
    void offloadWorkerThreadMain();

    // Wait until given offload buffer is placed in m_offloadBuffersFromWorker
    void waitForOffloadBuffer(const uint32_t* bufferp);

    // Shut down and join worker, if it's running, otherwise do nothing
    void shutdownOffloadWorker();
#endif

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedTrace);

protected:
    //=========================================================================
    // Internals available to format specific implementations

    mutable VerilatedMutex m_mutex;  // Ensure dump() etc only called from single thread

    uint32_t nextCode() const { return m_nextCode; }
    uint32_t numSignals() const { return m_numSignals; }
    uint32_t maxBits() const { return m_maxBits; }
    void fullDump(bool value) { m_fullDump = value; }

    double timeRes() const { return m_timeRes; }
    double timeUnit() const { return m_timeUnit; }
    std::string timeResStr() const;

    void traceInit() VL_MT_UNSAFE;

    // Declare new signal and return true if enabled
    bool declCode(uint32_t code, const char* namep, uint32_t bits, bool tri);

    // Is this an escape?
    bool isScopeEscape(char c) { return std::isspace(c) || c == m_scopeEscape; }
    // Character that splits scopes.  Note whitespace are ALWAYS escapes.
    char scopeEscape() { return m_scopeEscape; }
    // Prefix to assume in signal declarations
    const std::string& namePrefix() const { return m_namePrefixStack.back(); }

    void closeBase();
    void flushBase();

#ifdef VL_THREADED
    inline bool offload() const { return m_offload; }
    inline bool parallel() const { return m_parallel; }
#else
    static constexpr bool offload() { return false; }
    static constexpr bool parallel() { return false; }
#endif

    //=========================================================================
    // Virtual functions to be provided by the format specific implementation

    // Called when the trace moves forward to a new time point
    virtual void emitTimeChange(uint64_t timeui) = 0;

    // These hooks are called before a full or change based dump is produced.
    // The return value indicates whether to proceed with the dump.
    virtual bool preFullDump() = 0;
    virtual bool preChangeDump() = 0;

    // Trace buffer management
    virtual Buffer* getTraceBuffer() = 0;
    virtual void commitTraceBuffer(Buffer*) = 0;

    // Configure sub-class
    virtual void configure(const VerilatedTraceConfig&) = 0;

public:
    //=========================================================================
    // External interface to client code

    explicit VerilatedTrace();
    ~VerilatedTrace();

    // Set time units (s/ms, defaults to ns)
    void set_time_unit(const char* unitp) VL_MT_SAFE;
    void set_time_unit(const std::string& unit) VL_MT_SAFE;
    // Set time resolution (s/ms, defaults to ns)
    void set_time_resolution(const char* unitp) VL_MT_SAFE;
    void set_time_resolution(const std::string& unit) VL_MT_SAFE;
    // Set variables to dump, using $dumpvars format
    // If level = 0, dump everything and hier is then ignored
    void dumpvars(int level, const std::string& hier) VL_MT_SAFE;

    // Call
    void dump(uint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex);

    //=========================================================================
    // Internal interface to Verilator generated code

    //=========================================================================
    // Non-hot path internal interface to Verilator generated code

    void addModel(VerilatedModel*) VL_MT_SAFE_EXCLUDES(m_mutex);
    void addInitCb(initCb_t cb, void* userp) VL_MT_SAFE;
    void addFullCb(dumpCb_t cb, void* userp) VL_MT_SAFE;
    void addFullCb(dumpOffloadCb_t cb, void* userp) VL_MT_SAFE;
    void addChgCb(dumpCb_t cb, void* userp) VL_MT_SAFE;
    void addChgCb(dumpOffloadCb_t cb, void* userp) VL_MT_SAFE;
    void addCleanupCb(cleanupCb_t cb, void* userp) VL_MT_SAFE;

    void scopeEscape(char flag) { m_scopeEscape = flag; }

    void pushNamePrefix(const std::string&);
    void popNamePrefix(unsigned count = 1);
};

//=============================================================================
// VerilatedTraceBuffer

// T_Buffer is the format specific base class of VerilatedTraceBuffer.
// The format-specific hot-path methods use duck-typing via T_Buffer for performance.
template <class T_Buffer>
class VerilatedTraceBuffer VL_NOT_FINAL : public T_Buffer {
protected:
    // Type of the owner trace file
    using Trace = typename std::remove_cv<
        typename std::remove_reference<decltype(T_Buffer::m_owner)>::type>::type;

    static_assert(std::has_virtual_destructor<T_Buffer>::value, "");
    static_assert(std::is_base_of<VerilatedTrace<Trace, T_Buffer>, Trace>::value, "");

    friend Trace;  // Give the trace file access to the private bits
    friend std::default_delete<VerilatedTraceBuffer<T_Buffer>>;

    uint32_t* const m_sigs_oldvalp;  // Previous value store
    EData* const m_sigs_enabledp;  // Bit vector of enabled codes (nullptr = all on)

    explicit VerilatedTraceBuffer(Trace& owner);
    ~VerilatedTraceBuffer() override = default;

public:
    //=========================================================================
    // Hot path internal interface to Verilator generated code

    // Implementation note: We rely on the following duck-typed implementations
    // in the derived class T_Derived. These emit* functions record a format
    // specific trace entry. Normally one would use pure virtual functions for
    // these here, but we cannot afford dynamic dispatch for calling these as
    // this is very hot code during tracing.

    // duck-typed void emitBit(uint32_t code, CData newval) = 0;
    // duck-typed void emitCData(uint32_t code, CData newval, int bits) = 0;
    // duck-typed void emitSData(uint32_t code, SData newval, int bits) = 0;
    // duck-typed void emitIData(uint32_t code, IData newval, int bits) = 0;
    // duck-typed void emitQData(uint32_t code, QData newval, int bits) = 0;
    // duck-typed void emitWData(uint32_t code, const WData* newvalp, int bits) = 0;
    // duck-typed void emitDouble(uint32_t code, double newval) = 0;

    VL_ATTR_ALWINLINE inline uint32_t* oldp(uint32_t code) { return m_sigs_oldvalp + code; }

    // Write to previous value buffer value and emit trace entry.
    void fullBit(uint32_t* oldp, CData newval);
    void fullCData(uint32_t* oldp, CData newval, int bits);
    void fullSData(uint32_t* oldp, SData newval, int bits);
    void fullIData(uint32_t* oldp, IData newval, int bits);
    void fullQData(uint32_t* oldp, QData newval, int bits);
    void fullWData(uint32_t* oldp, const WData* newvalp, int bits);
    void fullDouble(uint32_t* oldp, double newval);

    // In non-offload mode, these are called directly by the trace callbacks,
    // and are called chg*. In offload mode, they are called by the worker
    // thread and are called chg*Impl

    // Check previous dumped value of signal. If changed, then emit trace entry
    VL_ATTR_ALWINLINE inline void chgBit(uint32_t* oldp, CData newval) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(oldp, newval);
    }
    VL_ATTR_ALWINLINE inline void chgCData(uint32_t* oldp, CData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullCData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE inline void chgSData(uint32_t* oldp, SData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullSData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE inline void chgIData(uint32_t* oldp, IData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullIData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE inline void chgQData(uint32_t* oldp, QData newval, int bits) {
        const uint64_t diff = *reinterpret_cast<QData*>(oldp) ^ newval;
        if (VL_UNLIKELY(diff)) fullQData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE inline void chgWData(uint32_t* oldp, const WData* newvalp, int bits) {
        for (int i = 0; i < (bits + 31) / 32; ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newvalp[i])) {
                fullWData(oldp, newvalp, bits);
                return;
            }
        }
    }
    VL_ATTR_ALWINLINE inline void chgDouble(uint32_t* oldp, double newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<double*>(oldp) != newval)) fullDouble(oldp, newval);
    }
};

#ifdef VL_THREADED
//=============================================================================
// VerilatedTraceOffloadBuffer

// T_Buffer is the format specific base class of VerilatedTraceBuffer.
// The format-specific hot-path methods use duck-typing via T_Buffer for performance.
template <class T_Buffer>
class VerilatedTraceOffloadBuffer final : public VerilatedTraceBuffer<T_Buffer> {
    using typename VerilatedTraceBuffer<T_Buffer>::Trace;

    friend Trace;  // Give the trace file access to the private bits

    uint32_t* m_offloadBufferWritep;  // Write pointer into current buffer
    uint32_t* const m_offloadBufferEndp;  // End of offload buffer

    explicit VerilatedTraceOffloadBuffer(Trace& owner);
    ~VerilatedTraceOffloadBuffer() override = default;

public:
    //=========================================================================
    // Hot path internal interface to Verilator generated code

    // Offloaded tracing. Just dump everything in the offload buffer
    inline void chgBit(uint32_t code, CData newval) {
        m_offloadBufferWritep[0] = VerilatedTraceOffloadCommand::CHG_BIT_0 | newval;
        m_offloadBufferWritep[1] = code;
        m_offloadBufferWritep += 2;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgCData(uint32_t code, CData newval, int bits) {
        m_offloadBufferWritep[0] = (bits << 4) | VerilatedTraceOffloadCommand::CHG_CDATA;
        m_offloadBufferWritep[1] = code;
        m_offloadBufferWritep[2] = newval;
        m_offloadBufferWritep += 3;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgSData(uint32_t code, SData newval, int bits) {
        m_offloadBufferWritep[0] = (bits << 4) | VerilatedTraceOffloadCommand::CHG_SDATA;
        m_offloadBufferWritep[1] = code;
        m_offloadBufferWritep[2] = newval;
        m_offloadBufferWritep += 3;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgIData(uint32_t code, IData newval, int bits) {
        m_offloadBufferWritep[0] = (bits << 4) | VerilatedTraceOffloadCommand::CHG_IDATA;
        m_offloadBufferWritep[1] = code;
        m_offloadBufferWritep[2] = newval;
        m_offloadBufferWritep += 3;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgQData(uint32_t code, QData newval, int bits) {
        m_offloadBufferWritep[0] = (bits << 4) | VerilatedTraceOffloadCommand::CHG_QDATA;
        m_offloadBufferWritep[1] = code;
        *reinterpret_cast<QData*>(m_offloadBufferWritep + 2) = newval;
        m_offloadBufferWritep += 4;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgWData(uint32_t code, const WData* newvalp, int bits) {
        m_offloadBufferWritep[0] = (bits << 4) | VerilatedTraceOffloadCommand::CHG_WDATA;
        m_offloadBufferWritep[1] = code;
        m_offloadBufferWritep += 2;
        for (int i = 0; i < (bits + 31) / 32; ++i) { *m_offloadBufferWritep++ = newvalp[i]; }
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
    inline void chgDouble(uint32_t code, double newval) {
        m_offloadBufferWritep[0] = VerilatedTraceOffloadCommand::CHG_DOUBLE;
        m_offloadBufferWritep[1] = code;
        // cppcheck-suppress invalidPointerCast
        *reinterpret_cast<double*>(m_offloadBufferWritep + 2) = newval;
        m_offloadBufferWritep += 4;
        VL_DEBUG_IF(assert(m_offloadBufferWritep <= m_offloadBufferEndp););
    }
};
#endif

#endif  // guard
