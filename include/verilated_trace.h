// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2021 by Wilson Snyder. This program is free software; you
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

#include <string>
#include <vector>

#ifdef VL_TRACE_THREADED
# include <condition_variable>
# include <deque>
# include <thread>
#endif

// clang-format on

#ifdef VL_TRACE_THREADED
//=============================================================================
// Threaded tracing

// A simple synchronized first in first out queue
template <class T> class VerilatedThreadQueue final {  // LCOV_EXCL_LINE  // lcov bug
private:
    VerilatedMutex m_mutex;  // Protects m_queue
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
class VerilatedTraceCommand final {
public:
    // These must all fit in 4 bit at the moment, as the tracing routines
    // pack parameters in the top bits.
    enum : vluint8_t {
        CHG_BIT_0 = 0x0,
        CHG_BIT_1 = 0x1,
        CHG_CDATA = 0x2,
        CHG_SDATA = 0x3,
        CHG_IDATA = 0x4,
        CHG_QDATA = 0x5,
        CHG_WDATA = 0x6,
        CHG_DOUBLE = 0x8,
        // TODO: full..
        TIME_CHANGE = 0xd,
        END = 0xe,  // End of buffer
        SHUTDOWN = 0xf  // Shutdown worker thread, also marks end of buffer
    };
};
#endif

//=============================================================================
// VerilatedTrace

// VerilatedTrace uses F-bounded polymorphism to access duck-typed
// implementations in the format specific derived class, which must be passed
// as the type parameter T_Derived
template <class T_Derived> class VerilatedTrace VL_NOT_FINAL {
public:
    //=========================================================================
    // Generic tracing internals

    using initCb_t = void (*)(void*, T_Derived*, vluint32_t);  // Type of init callbacks
    using dumpCb_t = void (*)(void*, T_Derived*);  // Type of all but init callbacks

private:
    struct CallbackRecord {
        // Note: would make these fields const, but some old STL implementations
        // (the one in Ubuntu 14.04 with GCC 4.8.4 in particular) use the
        // assignment operator on inserting into collections, so they don't work
        // with const fields...
        union {
            initCb_t m_initCb;  // The callback function
            dumpCb_t m_dumpCb;  // The callback function
        };
        void* m_userp;  // The user pointer to pass to the callback (the symbol table)
        CallbackRecord(initCb_t cb, void* userp)
            : m_initCb{cb}
            , m_userp{userp} {}
        CallbackRecord(dumpCb_t cb, void* userp)
            : m_dumpCb{cb}
            , m_userp{userp} {}
    };

    vluint32_t* m_sigs_oldvalp;  // Old value store
    vluint64_t m_timeLastDump;  // Last time we did a dump
    std::vector<CallbackRecord> m_initCbs;  // Routines to initialize traciong
    std::vector<CallbackRecord> m_fullCbs;  // Routines to perform full dump
    std::vector<CallbackRecord> m_chgCbs;  // Routines to perform incremental dump
    std::vector<CallbackRecord> m_cleanupCbs;  // Routines to call at the end of dump
    bool m_fullDump;  // Whether a full dump is required on the next call to 'dump'
    vluint32_t m_nextCode;  // Next code number to assign
    vluint32_t m_numSignals;  // Number of distinct signals
    vluint32_t m_maxBits;  // Number of bits in the widest signal
    std::string m_moduleName;  // Name of module being trace initialized now
    char m_scopeEscape;
    double m_timeRes;  // Time resolution (ns/ms etc)
    double m_timeUnit;  // Time units (ns/ms etc)

    void addCallbackRecord(std::vector<CallbackRecord>& cbVec, CallbackRecord& cbRec)
        VL_MT_SAFE_EXCLUDES(m_mutex);

    // Equivalent to 'this' but is of the sub-type 'T_Derived*'. Use 'self()->'
    // to access duck-typed functions to avoid a virtual function call.
    T_Derived* self() { return static_cast<T_Derived*>(this); }

    // Flush any remaining data for this file
    static void onFlush(void* selfp) VL_MT_UNSAFE_ONE;
    // Close the file on termination
    static void onExit(void* selfp) VL_MT_UNSAFE_ONE;

#ifdef VL_TRACE_THREADED
    // Number of total trace buffers that have been allocated
    vluint32_t m_numTraceBuffers;

    // Size of trace buffers
    size_t m_traceBufferSize;

    // Buffers handed to worker for processing
    VerilatedThreadQueue<vluint32_t*> m_buffersToWorker;
    // Buffers returned from worker after processing
    VerilatedThreadQueue<vluint32_t*> m_buffersFromWorker;

    // Get a new trace buffer that can be populated. May block if none available
    vluint32_t* getTraceBuffer();

    // Write pointer into current buffer
    vluint32_t* m_traceBufferWritep;

    // End of trace buffer
    vluint32_t* m_traceBufferEndp;

    // The worker thread itself
    std::unique_ptr<std::thread> m_workerThread;

    // The function executed by the worker thread
    void workerThreadMain();

    // Wait until given buffer is placed in m_buffersFromWorker
    void waitForBuffer(const vluint32_t* bufferp);

    // Shut down and join worker, if it's running, otherwise do nothing
    void shutdownWorker();
#endif

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedTrace);

protected:
    //=========================================================================
    // Internals available to format specific implementations

    VerilatedMutex m_mutex;  // Ensure dump() etc only called from single thread

    vluint32_t nextCode() const { return m_nextCode; }
    vluint32_t numSignals() const { return m_numSignals; }
    vluint32_t maxBits() const { return m_maxBits; }
    const std::string& moduleName() const { return m_moduleName; }
    void fullDump(bool value) { m_fullDump = value; }
    vluint64_t timeLastDump() { return m_timeLastDump; }

    double timeRes() const { return m_timeRes; }
    double timeUnit() const { return m_timeUnit; }
    std::string timeResStr() const;

    void traceInit() VL_MT_UNSAFE;

    void declCode(vluint32_t code, vluint32_t bits, bool tri);

    // Is this an escape?
    bool isScopeEscape(char c) { return std::isspace(c) || c == m_scopeEscape; }
    // Character that splits scopes.  Note whitespace are ALWAYS escapes.
    char scopeEscape() { return m_scopeEscape; }

    void closeBase();
    void flushBase();

    //=========================================================================
    // Virtual functions to be provided by the format specific implementation

    // Called when the trace moves forward to a new time point
    virtual void emitTimeChange(vluint64_t timeui) = 0;

    // These hooks are called before a full or change based dump is produced.
    // The return value indicates whether to proceed with the dump.
    virtual bool preFullDump() = 0;
    virtual bool preChangeDump() = 0;

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

    // Call
    void dump(vluint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex);

    //=========================================================================
    // Non-hot path internal interface to Verilator generated code

    void addInitCb(initCb_t cb, void* userp) VL_MT_SAFE;
    void addFullCb(dumpCb_t cb, void* userp) VL_MT_SAFE;
    void addChgCb(dumpCb_t cb, void* userp) VL_MT_SAFE;
    void addCleanupCb(dumpCb_t cb, void* userp) VL_MT_SAFE;

    void module(const std::string& name) VL_MT_UNSAFE;
    void scopeEscape(char flag) { m_scopeEscape = flag; }

    //=========================================================================
    // Hot path internal interface to Verilator generated code

    // Implementation note: We rely on the following duck-typed implementations
    // in the derived class T_Derived. These emit* functions record a format
    // specific trace entry. Normally one would use pure virtual functions for
    // these here, but we cannot afford dynamic dispatch for calling these as
    // this is very hot code during tracing.

    // duck-typed void emitBit(vluint32_t code, CData newval) = 0;
    // duck-typed void emitCData(vluint32_t code, CData newval, int bits) = 0;
    // duck-typed void emitSData(vluint32_t code, SData newval, int bits) = 0;
    // duck-typed void emitIData(vluint32_t code, IData newval, int bits) = 0;
    // duck-typed void emitQData(vluint32_t code, QData newval, int bits) = 0;
    // duck-typed void emitWData(vluint32_t code, const WData* newvalp, int bits) = 0;
    // duck-typed void emitDouble(vluint32_t code, double newval) = 0;

    vluint32_t* oldp(vluint32_t code) { return m_sigs_oldvalp + code; }

    // Write to previous value buffer value and emit trace entry.
    void fullBit(vluint32_t* oldp, CData newval);
    void fullCData(vluint32_t* oldp, CData newval, int bits);
    void fullSData(vluint32_t* oldp, SData newval, int bits);
    void fullIData(vluint32_t* oldp, IData newval, int bits);
    void fullQData(vluint32_t* oldp, QData newval, int bits);
    void fullWData(vluint32_t* oldp, const WData* newvalp, int bits);
    void fullDouble(vluint32_t* oldp, double newval);

#ifdef VL_TRACE_THREADED
    // Threaded tracing. Just dump everything in the trace buffer
    inline void chgBit(vluint32_t code, CData newval) {
        m_traceBufferWritep[0] = VerilatedTraceCommand::CHG_BIT_0 | newval;
        m_traceBufferWritep[1] = code;
        m_traceBufferWritep += 2;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgCData(vluint32_t code, CData newval, int bits) {
        m_traceBufferWritep[0] = (bits << 4) | VerilatedTraceCommand::CHG_CDATA;
        m_traceBufferWritep[1] = code;
        m_traceBufferWritep[2] = newval;
        m_traceBufferWritep += 3;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgSData(vluint32_t code, SData newval, int bits) {
        m_traceBufferWritep[0] = (bits << 4) | VerilatedTraceCommand::CHG_SDATA;
        m_traceBufferWritep[1] = code;
        m_traceBufferWritep[2] = newval;
        m_traceBufferWritep += 3;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgIData(vluint32_t code, IData newval, int bits) {
        m_traceBufferWritep[0] = (bits << 4) | VerilatedTraceCommand::CHG_IDATA;
        m_traceBufferWritep[1] = code;
        m_traceBufferWritep[2] = newval;
        m_traceBufferWritep += 3;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgQData(vluint32_t code, QData newval, int bits) {
        m_traceBufferWritep[0] = (bits << 4) | VerilatedTraceCommand::CHG_QDATA;
        m_traceBufferWritep[1] = code;
        *reinterpret_cast<QData*>(m_traceBufferWritep + 2) = newval;
        m_traceBufferWritep += 4;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgWData(vluint32_t code, const WData* newvalp, int bits) {
        m_traceBufferWritep[0] = (bits << 4) | VerilatedTraceCommand::CHG_WDATA;
        m_traceBufferWritep[1] = code;
        m_traceBufferWritep += 2;
        for (int i = 0; i < (bits + 31) / 32; ++i) { *m_traceBufferWritep++ = newvalp[i]; }
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }
    inline void chgDouble(vluint32_t code, double newval) {
        m_traceBufferWritep[0] = VerilatedTraceCommand::CHG_DOUBLE;
        m_traceBufferWritep[1] = code;
        // cppcheck-suppress invalidPointerCast
        *reinterpret_cast<double*>(m_traceBufferWritep + 2) = newval;
        m_traceBufferWritep += 4;
        VL_DEBUG_IF(assert(m_traceBufferWritep <= m_traceBufferEndp););
    }

#define CHG(name) chg##name##Impl
#else
#define CHG(name) chg##name
#endif

    // In non-threaded mode, these are called directly by the trace callbacks,
    // and are called chg*. In threaded mode, they are called by the worker
    // thread and are called chg*Impl

    // Check previous dumped value of signal. If changed, then emit trace entry
    inline void CHG(Bit)(vluint32_t* oldp, CData newval) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(oldp, newval);
    }
    inline void CHG(CData)(vluint32_t* oldp, CData newval, int bits) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullCData(oldp, newval, bits);
    }
    inline void CHG(SData)(vluint32_t* oldp, SData newval, int bits) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullSData(oldp, newval, bits);
    }
    inline void CHG(IData)(vluint32_t* oldp, IData newval, int bits) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullIData(oldp, newval, bits);
    }
    inline void CHG(QData)(vluint32_t* oldp, QData newval, int bits) {
        const vluint64_t diff = *reinterpret_cast<QData*>(oldp) ^ newval;
        if (VL_UNLIKELY(diff)) fullQData(oldp, newval, bits);
    }
    inline void CHG(WData)(vluint32_t* oldp, const WData* newvalp, int bits) {
        for (int i = 0; i < (bits + 31) / 32; ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newvalp[i])) {
                fullWData(oldp, newvalp, bits);
                return;
            }
        }
    }
    inline void CHG(Double)(vluint32_t* oldp, double newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<double*>(oldp) != newval)) fullDouble(oldp, newval);
    }

#undef CHG
};
#endif  // guard
