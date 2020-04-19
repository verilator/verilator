// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Tracing functionality common to all formats
///
//=============================================================================
// SPDIFF_OFF

#ifndef _VERILATED_TRACE_H_
#define _VERILATED_TRACE_H_ 1

// clang-format off

#include "verilated.h"

#ifdef VL_TRACE_THREADED
# include "verilated_trace_threaded.h"
# include <memory>
# include <thread>
#endif

#include <string>
#include <vector>

// clang-format on

class VerilatedTraceCallInfo;

//=============================================================================
// VerilatedTrace

// VerilatedTrace uses F-bounded polymorphism to access duck-typed
// implementations in the format specific derived class, which must be passed
// as the type parameter T_Derived
template <class T_Derived> class VerilatedTrace {
private:
    //=========================================================================
    // Generic tracing internals

    vluint32_t* m_sigs_oldvalp;  ///< Old value store
    vluint64_t m_timeLastDump;  ///< Last time we did a dump
    std::vector<VerilatedTraceCallInfo*> m_callbacks;  ///< Routines to perform dumping
    bool m_fullDump;  ///< Whether a full dump is required on the next call to 'dump'
    vluint32_t m_nextCode;  ///< Next code number to assign
    vluint32_t m_numSignals;  ///< Number of distinct signals
    std::string m_moduleName;  ///< Name of module being trace initialized now
    char m_scopeEscape;
    double m_timeRes;  ///< Time resolution (ns/ms etc)
    double m_timeUnit;  ///< Time units (ns/ms etc)

    // Equivalent to 'this' but is of the sub-type 'T_Derived*'. Use 'self()->'
    // to access duck-typed functions to avoid a virtual function call.
    T_Derived* self() { return static_cast<T_Derived*>(this); }

#ifdef VL_TRACE_THREADED
    // Number of total trace buffers that have been allocated
    vluint32_t m_numTraceBuffers;

    // Buffers handed to worker for processing
    VerilatedThreadQueue<VerilatedTraceEntry*> m_buffersToWorker;
    // Buffers returned from worker after processing
    VerilatedThreadQueue<VerilatedTraceEntry*> m_buffersFromWorker;

    // Get a new trace buffer that can be populated. May block if none available
    VerilatedTraceEntry* getTraceBuffer();

    // Write pointer into current buffer
    VerilatedTraceEntry* m_traceBufferWritep;

    // The worker thread itself
    std::unique_ptr<std::thread> m_workerThread;

    // The function executed by the worker thread
    void workerThreadMain();

    // Wait until given buffer is placed in m_buffersFromWorker
    void waitForBuffer(const VerilatedTraceEntry* bufferp);

    // Shut down and join worker, if it's running, otherwise do nothing
    void shutdownWorker();
#endif

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedTrace);

protected:
    //=========================================================================
    // Internals available to format specific implementations

    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread

    vluint32_t nextCode() const { return m_nextCode; }
    vluint32_t numSignals() const { return m_numSignals; }
    const std::string& moduleName() const { return m_moduleName; }
    void fullDump(bool value) { m_fullDump = value; }
    vluint64_t timeLastDump() { return m_timeLastDump; }

    double timeRes() const { return m_timeRes; }
    double timeUnit() const { return m_timeUnit; }
    std::string timeResStr() const;
    std::string timeUnitStr() const;

    void traceInit() VL_MT_UNSAFE;

    void declCode(vluint32_t code, vluint32_t bits, bool tri);

    /// Is this an escape?
    bool isScopeEscape(char c) { return isspace(c) || c == m_scopeEscape; }
    /// Character that splits scopes.  Note whitespace are ALWAYS escapes.
    char scopeEscape() { return m_scopeEscape; }

    void close();
    void flush();

    //=========================================================================
    // Virtual functions to be provided by the format specific implementation

    // Called when the trace moves forward to a new time point
    virtual void emitTimeChange(vluint64_t timeui) = 0;

    // These hooks are called before a full or change based dump is produced.
    // The return value indicates whether to proceed with the dump.
    virtual bool preFullDump() { return true; }
    virtual bool preChangeDump() { return true; }

public:
    //=========================================================================
    // External interface to client code

    explicit VerilatedTrace();
    ~VerilatedTrace();

    // Set time units (s/ms, defaults to ns)
    void set_time_unit(const char* unitp);
    void set_time_unit(const std::string& unit);
    // Set time resolution (s/ms, defaults to ns)
    void set_time_resolution(const char* unitp);
    void set_time_resolution(const std::string& unit);

    // Call
    void dump(vluint64_t timeui);

    //=========================================================================
    // Non-hot path internal interface to Verilator generated code

    typedef void (*callback_t)(T_Derived* tracep, void* userthis, vluint32_t code);

    void changeThread() { m_assertOne.changeThread(); }

    void addCallback(callback_t initcb, callback_t fullcb, callback_t changecb,
                     void* userthis) VL_MT_UNSAFE_ONE;

    void module(const std::string& name) VL_MT_UNSAFE_ONE {
        m_assertOne.check();
        m_moduleName = name;
    }

    void scopeEscape(char flag) { m_scopeEscape = flag; }

    //=========================================================================
    // Hot path internal interface to Verilator generated code

    // Implementation note: We rely on the following duck-typed implementations
    // in the derived class T_Derived. These emit* functions record a format
    // specific trace entry. Normally one would use pure virtual functions for
    // these here, but we cannot afford dynamic dispatch for calling these as
    // this is very hot code during tracing.

    // duck-typed void emitBit(vluint32_t code, vluint32_t newval) = 0;
    // duck-typed template <int T_Bits> void emitBus(vluint32_t code, vluint32_t newval) = 0;
    // duck-typed void emitQuad(vluint32_t code, vluint64_t newval, int bits) = 0;
    // duck-typed void emitArray(vluint32_t code, const vluint32_t* newvalp, int bits) = 0;
    // duck-typed void emitFloat(vluint32_t code, float newval) = 0;
    // duck-typed void emitDouble(vluint32_t code, double newval) = 0;

    vluint32_t* oldp(vluint32_t code) { return m_sigs_oldvalp + code; }

    // Write to previous value buffer value and emit trace entry.
    void fullBit(vluint32_t* oldp, vluint32_t newval);
    template <int T_Bits> void fullBus(vluint32_t* oldp, vluint32_t newval);
    void fullQuad(vluint32_t* oldp, vluint64_t newval, int bits);
    void fullArray(vluint32_t* oldp, const vluint32_t* newvalp, int bits);
    void fullFloat(vluint32_t* oldp, float newval);
    void fullDouble(vluint32_t* oldp, double newval);

#ifdef VL_TRACE_THREADED
    // Threaded tracing. Just dump everything in the trace buffer
    inline void chgBit(vluint32_t* oldp, vluint32_t newval) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_BIT | newval;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep += 2;
    }
    template <int T_Bits> inline void chgBus(vluint32_t* oldp, vluint32_t newval) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_BUS | T_Bits;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep[2].newBits = newval;
        m_traceBufferWritep += 3;
    }
    inline void chgQuad(vluint32_t* oldp, vluint64_t newval, int bits) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_QUAD | bits;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep[2].newBits = newval;
        m_traceBufferWritep += 3;
    }
    inline void chgArray(vluint32_t* oldp, const vluint32_t* newvalp, int bits) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_ARRAY;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep[2].params = bits;
        m_traceBufferWritep += 3;
        vluint32_t* const wp = reinterpret_cast<vluint32_t*>(m_traceBufferWritep);
        for (int i = 0; i < (bits + 31) / 32; ++i) { wp[i] = newvalp[i]; }
        m_traceBufferWritep += (bits + 63) / 64;
    }
    inline void chgFloat(vluint32_t* oldp, float newval) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_FLOAT;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep[2].newFloat = newval;
        m_traceBufferWritep += 3;
    }
    inline void chgDouble(vluint32_t* oldp, double newval) {
        m_traceBufferWritep[0].cmd = VerilatedTraceCommand::CHG_DOUBLE;
        m_traceBufferWritep[1].oldp = oldp;
        m_traceBufferWritep[2].newDouble = newval;
        m_traceBufferWritep += 3;
    }

#define CHG(name) chg##name##Impl
#else
#define CHG(name) chg##name
#endif

    // In non-threaded mode, these are called directly by the trace callbacks,
    // and are called chg*. In threaded mode, they are called by the worker
    // thread and are called chg*Impl

    // Check previous dumped value of signal. If changed, then emit trace entry
    inline void CHG(Bit)(vluint32_t* oldp, vluint32_t newval) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(oldp, newval);
    }
    template <int T_Bits> inline void CHG(Bus)(vluint32_t* oldp, vluint32_t newval) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBus<T_Bits>(oldp, newval);
    }
    inline void CHG(Quad)(vluint32_t* oldp, vluint64_t newval, int bits) {
        const vluint64_t diff = *reinterpret_cast<vluint64_t*>(oldp) ^ newval;
        if (VL_UNLIKELY(diff)) fullQuad(oldp, newval, bits);
    }
    inline void CHG(Array)(vluint32_t* oldp, const vluint32_t* newvalp, int bits) {
        for (int i = 0; i < (bits + 31) / 32; ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newvalp[i])) {
                fullArray(oldp, newvalp, bits);
                return;
            }
        }
    }
    inline void CHG(Float)(vluint32_t* oldp, float newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<float*>(oldp) != newval)) fullFloat(oldp, newval);
    }
    inline void CHG(Double)(vluint32_t* oldp, double newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<double*>(oldp) != newval)) fullDouble(oldp, newval);
    }

#undef CHG
};
#endif  // guard
