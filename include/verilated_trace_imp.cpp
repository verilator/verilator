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
/// \brief Implementation of tracing functionality common to all trace formats
///
//=============================================================================
// SPDIFF_OFF

// clang-format off

#ifndef VL_DERIVED_T
# error "This file should be included in trace format implementations"
#endif

#include "verilated_trace.h"

#if 0
# include <iostream>
# define VL_TRACE_THREAD_DEBUG(msg) std::cout << "TRACE THREAD: " << msg << std::endl
#else
# define VL_TRACE_THREAD_DEBUG(msg)
#endif

// clang-format on

//=============================================================================
// Static utility functions

static double timescaleToDouble(const char* unitp) {
    char* endp;
    double value = strtod(unitp, &endp);
    // On error so we allow just "ns" to return 1e-9.
    if (value == 0.0 && endp == unitp) value = 1;
    unitp = endp;
    for (; *unitp && isspace(*unitp); unitp++) {}
    switch (*unitp) {
    case 's': value *= 1e1; break;
    case 'm': value *= 1e-3; break;
    case 'u': value *= 1e-6; break;
    case 'n': value *= 1e-9; break;
    case 'p': value *= 1e-12; break;
    case 'f': value *= 1e-15; break;
    case 'a': value *= 1e-18; break;
    }
    return value;
}

static std::string doubleToTimescale(double value) {
    const char* suffixp = "s";
    // clang-format off
    if      (value >= 1e0)   { suffixp = "s"; value *= 1e0; }
    else if (value >= 1e-3 ) { suffixp = "ms"; value *= 1e3; }
    else if (value >= 1e-6 ) { suffixp = "us"; value *= 1e6; }
    else if (value >= 1e-9 ) { suffixp = "ns"; value *= 1e9; }
    else if (value >= 1e-12) { suffixp = "ps"; value *= 1e12; }
    else if (value >= 1e-15) { suffixp = "fs"; value *= 1e15; }
    else if (value >= 1e-18) { suffixp = "as"; value *= 1e18; }
    // clang-format on
    char valuestr[100];
    sprintf(valuestr, "%3.0f%s", value, suffixp);
    return valuestr;  // Gets converted to string, so no ref to stack
}

//=============================================================================
// Internal callback routines for each module being traced.

// Each module that wishes to be traced registers a set of callbacks stored in
// this class.  When the trace file is being constructed, this class provides
// the callback routines to be executed.
class VerilatedTraceCallInfo {
public:  // This is in .cpp file so is not widely visible
    typedef VerilatedTrace<VL_DERIVED_T>::callback_t callback_t;

    callback_t m_initcb;  ///< Initialization Callback function
    callback_t m_fullcb;  ///< Full Dumping Callback function
    callback_t m_changecb;  ///< Incremental Dumping Callback function
    void* m_userthis;  ///< User data pointer for callback
    vluint32_t m_code;  ///< Starting code number (set later by traceInit)
    // CONSTRUCTORS
    VerilatedTraceCallInfo(callback_t icb, callback_t fcb, callback_t changecb, void* ut)
        : m_initcb(icb)
        , m_fullcb(fcb)
        , m_changecb(changecb)
        , m_userthis(ut)
        , m_code(1) {}
    ~VerilatedTraceCallInfo() {}
};

#ifdef VL_TRACE_THREADED
//=========================================================================
// Buffer management

template <> VerilatedTraceEntry* VerilatedTrace<VL_DERIVED_T>::getTraceBuffer() {
    VerilatedTraceEntry* bufferp;
    // Some jitter is expected, so some number of alternative trace buffers are
    // required, but don't allocate more than 8 buffers.
    if (m_numTraceBuffers < 8) {
        // Allocate a new buffer if none is available
        if (!m_buffersFromWorker.tryGet(bufferp)) {
            ++m_numTraceBuffers;
            // Note: over allocate a bit so pointer comparison is well defined
            // if we overflow only by a small amount
            bufferp = new VerilatedTraceEntry[m_traceBufferSize + 16];
        }
    } else {
        // Block until a buffer becomes available
        bufferp = m_buffersFromWorker.get();
    }
    return bufferp;
}

template <> void VerilatedTrace<VL_DERIVED_T>::waitForBuffer(const VerilatedTraceEntry* buffp) {
    // Slow path code only called on flush/shutdown, so use a simple algorithm.
    // Collect buffers from worker and stash them until we get the one we want.
    std::deque<VerilatedTraceEntry*> stash;
    do { stash.push_back(m_buffersFromWorker.get()); } while (stash.back() != buffp);
    // Now put them back in the queue, in the original order.
    while (!stash.empty()) {
        m_buffersFromWorker.put_front(stash.back());
        stash.pop_back();
    }
}

//=========================================================================
// Worker thread

template <> void VerilatedTrace<VL_DERIVED_T>::workerThreadMain() {
    while (true) {
        VerilatedTraceEntry* const bufferp = m_buffersToWorker.get();

        VL_TRACE_THREAD_DEBUG("");
        VL_TRACE_THREAD_DEBUG("Got buffer");

        const VerilatedTraceEntry* readp = bufferp;

        vluint32_t cmd;
        unsigned bits;
        vluint32_t* oldp;
        vluint64_t newBits;

        while (true) {
            cmd = (readp++)->cmd;

            switch (cmd & ~0xFFU) {
                //===
                // CHG_* commands
            case VerilatedTraceCommand::CHG_BIT:
                VL_TRACE_THREAD_DEBUG("Command CHG_BIT");
                chgBitImpl((readp++)->oldp, cmd & 1);
                continue;
            case VerilatedTraceCommand::CHG_BUS:
                VL_TRACE_THREAD_DEBUG("Command CHG_BUS");

                oldp = (readp++)->oldp;
                newBits = (readp++)->newBits;

                // Bits stored in bottom byte of command
                switch (cmd & 0xFFU) {
                case 2: chgBusImpl<2>(oldp, newBits); continue;
                case 3: chgBusImpl<3>(oldp, newBits); continue;
                case 4: chgBusImpl<4>(oldp, newBits); continue;
                case 5: chgBusImpl<5>(oldp, newBits); continue;
                case 6: chgBusImpl<6>(oldp, newBits); continue;
                case 7: chgBusImpl<7>(oldp, newBits); continue;
                case 8: chgBusImpl<8>(oldp, newBits); continue;
                case 9: chgBusImpl<9>(oldp, newBits); continue;
                case 10: chgBusImpl<10>(oldp, newBits); continue;
                case 11: chgBusImpl<11>(oldp, newBits); continue;
                case 12: chgBusImpl<12>(oldp, newBits); continue;
                case 13: chgBusImpl<13>(oldp, newBits); continue;
                case 14: chgBusImpl<14>(oldp, newBits); continue;
                case 15: chgBusImpl<15>(oldp, newBits); continue;
                case 16: chgBusImpl<16>(oldp, newBits); continue;
                case 17: chgBusImpl<17>(oldp, newBits); continue;
                case 18: chgBusImpl<18>(oldp, newBits); continue;
                case 19: chgBusImpl<19>(oldp, newBits); continue;
                case 20: chgBusImpl<20>(oldp, newBits); continue;
                case 21: chgBusImpl<21>(oldp, newBits); continue;
                case 22: chgBusImpl<22>(oldp, newBits); continue;
                case 23: chgBusImpl<23>(oldp, newBits); continue;
                case 24: chgBusImpl<24>(oldp, newBits); continue;
                case 25: chgBusImpl<25>(oldp, newBits); continue;
                case 26: chgBusImpl<26>(oldp, newBits); continue;
                case 27: chgBusImpl<27>(oldp, newBits); continue;
                case 28: chgBusImpl<28>(oldp, newBits); continue;
                case 29: chgBusImpl<29>(oldp, newBits); continue;
                case 30: chgBusImpl<30>(oldp, newBits); continue;
                case 31: chgBusImpl<31>(oldp, newBits); continue;
                case 32: chgBusImpl<32>(oldp, newBits); continue;
                }
                VL_FATAL_MT(__FILE__, __LINE__, "", "Bad number of bits in CHG_BUS command");
                break;
            case VerilatedTraceCommand::CHG_QUAD:
                VL_TRACE_THREAD_DEBUG("Command CHG_QUAD");
                // Bits stored in bottom byte of command
                chgQuadImpl(readp[0].oldp, readp[1].newBits, cmd & 0xFF);
                readp += 2;
                continue;
            case VerilatedTraceCommand::CHG_ARRAY:
                VL_TRACE_THREAD_DEBUG("Command CHG_CHG_ARRAY");
                oldp = (readp++)->oldp;
                bits = (readp++)->params;
                chgArrayImpl(oldp, reinterpret_cast<const vluint32_t*>(readp), bits);
                readp += (bits + 63) / 64;
                continue;
            case VerilatedTraceCommand::CHG_FLOAT:
                VL_TRACE_THREAD_DEBUG("Command CHG_FLOAT");
                chgFloatImpl(readp[0].oldp, readp[1].newFloat);
                readp += 2;
                continue;
            case VerilatedTraceCommand::CHG_DOUBLE:
                VL_TRACE_THREAD_DEBUG("Command CHG_DOUBLE");
                chgDoubleImpl(readp[0].oldp, readp[1].newDouble);
                readp += 2;
                continue;

                //===
                // Rare commands
            case VerilatedTraceCommand::TIME_CHANGE:
                VL_TRACE_THREAD_DEBUG("Command TIME_CHANGE");
                emitTimeChange((readp++)->timeui);
                continue;

                //===
                // Commands ending this buffer
            case VerilatedTraceCommand::END: VL_TRACE_THREAD_DEBUG("Command END"); break;
            case VerilatedTraceCommand::SHUTDOWN:
                VL_TRACE_THREAD_DEBUG("Command SHUTDOWN");
                break;

                //===
                // Unknown command
            default:
                VL_PRINTF_MT("Trace command: 0x%08x\n", cmd);
                VL_FATAL_MT(__FILE__, __LINE__, "", "Unknown trace command");
                break;
            }

            // The above switch will execute 'continue' when necessary,
            // so if we ever reach here, we are done with the buffer.
            break;
        }

        VL_TRACE_THREAD_DEBUG("Returning buffer");

        // Return buffer
        m_buffersFromWorker.put(bufferp);

        // Shut down if required
        if (VL_UNLIKELY(cmd == VerilatedTraceCommand::SHUTDOWN)) return;
    }
}

template <> void VerilatedTrace<VL_DERIVED_T>::shutdownWorker() {
    // If the worker thread is not running, done..
    if (!m_workerThread) return;

    // Hand an buffer with a shutdown command to the worker thread
    VerilatedTraceEntry* const bufferp = getTraceBuffer();
    bufferp[0].cmd = VerilatedTraceCommand::SHUTDOWN;
    m_buffersToWorker.put(bufferp);
    // Wait for it to return
    waitForBuffer(bufferp);
    // Join the thread and delete it
    m_workerThread->join();
    m_workerThread.reset(nullptr);
}

#endif

//=============================================================================
// Life cycle

template <> void VerilatedTrace<VL_DERIVED_T>::close() {
#ifdef VL_TRACE_THREADED
    shutdownWorker();
    while (m_numTraceBuffers) {
        delete[] m_buffersFromWorker.get();
        m_numTraceBuffers--;
    }
#endif
}

template <> void VerilatedTrace<VL_DERIVED_T>::flush() {
#ifdef VL_TRACE_THREADED
    // Hand an empty buffer to the worker thread
    VerilatedTraceEntry* const bufferp = getTraceBuffer();
    bufferp[0].cmd = VerilatedTraceCommand::END;
    m_buffersToWorker.put(bufferp);
    // Wait for it to be returned. As the processing is in-order,
    // this ensures all previous buffers have been processed.
    waitForBuffer(bufferp);
#endif
}

//=============================================================================
// VerilatedTrace

template <>
VerilatedTrace<VL_DERIVED_T>::VerilatedTrace()
    : m_sigs_oldvalp(NULL)
    , m_timeLastDump(0)
    , m_fullDump(true)
    , m_nextCode(0)
    , m_numSignals(0)
    , m_scopeEscape('.')
    , m_timeRes(1e-9)
    , m_timeUnit(1e-9)
#ifdef VL_TRACE_THREADED
    , m_numTraceBuffers(0)
#endif
{
    set_time_unit(Verilated::timeunitString());
    set_time_resolution(Verilated::timeprecisionString());
}

template <> VerilatedTrace<VL_DERIVED_T>::~VerilatedTrace() {
    if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = NULL);
    while (!m_callbacks.empty()) {
        delete m_callbacks.back();
        m_callbacks.pop_back();
    }
#ifdef VL_TRACE_THREADED
    close();
#endif
}

//=========================================================================
// Internals available to format specific implementations

template <> void VerilatedTrace<VL_DERIVED_T>::traceInit() VL_MT_UNSAFE {
    m_assertOne.check();

    // Note: It is possible to re-open a trace file (VCD in particular),
    // so we must reset the next code here, but it must have the same number
    // of codes on re-open
    const vluint32_t expectedCodes = nextCode();
    m_nextCode = 1;
    m_numSignals = 0;

    // Call all initialize callbacks, which will call decl* for each signal.
    for (vluint32_t ent = 0; ent < m_callbacks.size(); ++ent) {
        VerilatedTraceCallInfo* cip = m_callbacks[ent];
        cip->m_code = nextCode();
        (cip->m_initcb)(self(), cip->m_userthis, cip->m_code);
    }

    if (expectedCodes && nextCode() != expectedCodes) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Reopening trace file with different number of signals");
    }

    // Now that we know the number of codes, allocate space for the buffer
    // holding previous signal values.
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new vluint32_t[nextCode()];

#ifdef VL_TRACE_THREADED
    // Compute trace buffer size. we need to be able to store a new value for
    // each signal, which is 'nextCode()' entries after the init callbacks
    // above have been run, plus up to 3 more words of metadata per signal,
    // plus fixed overhead of 1 for a termination flag and 2 for a time stamp
    // update.
    m_traceBufferSize = nextCode() + numSignals() * 3 + 3;

    // Start the worker thread
    m_workerThread.reset(new std::thread(&VerilatedTrace<VL_DERIVED_T>::workerThreadMain, this));
#endif
}

template <>
void VerilatedTrace<VL_DERIVED_T>::declCode(vluint32_t code, vluint32_t bits, bool tri) {
    if (!code) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: internal trace problem, code 0 is illegal");
    }
    // Note: The tri-state flag is not used by Verilator, but is here for
    // compatibility with some foreign code.
    int codesNeeded = (bits + 31) / 32;
    if (tri) codesNeeded *= 2;
    m_nextCode = std::max(m_nextCode, code + codesNeeded);
    ++m_numSignals;
}

//=========================================================================
// Internals available to format specific implementations

template <> std::string VerilatedTrace<VL_DERIVED_T>::timeResStr() const {
    return doubleToTimescale(m_timeRes);
}

template <> std::string VerilatedTrace<VL_DERIVED_T>::timeUnitStr() const {
    return doubleToTimescale(m_timeUnit);
}

//=========================================================================
// External interface to client code

template <> void VerilatedTrace<VL_DERIVED_T>::set_time_unit(const char* unitp) {
    m_timeUnit = timescaleToDouble(unitp);
}

template <> void VerilatedTrace<VL_DERIVED_T>::set_time_unit(const std::string& unit) {
    set_time_unit(unit.c_str());
}

template <> void VerilatedTrace<VL_DERIVED_T>::set_time_resolution(const char* unitp) {
    m_timeRes = timescaleToDouble(unitp);
}

template <> void VerilatedTrace<VL_DERIVED_T>::set_time_resolution(const std::string& unit) {
    set_time_resolution(unit.c_str());
}

template <> void VerilatedTrace<VL_DERIVED_T>::dump(vluint64_t timeui) {
    m_assertOne.check();
    if (VL_UNLIKELY(m_timeLastDump && timeui <= m_timeLastDump)) {
        VL_PRINTF_MT("%%Warning: previous dump at t=%" VL_PRI64 "u, requesting t=%" VL_PRI64
                     "u, dump call ignored\n",
                     m_timeLastDump, timeui);
        return;
    }
    m_timeLastDump = timeui;

    Verilated::quiesce();

    // Call hook for format specific behaviour
    if (VL_UNLIKELY(m_fullDump)) {
        if (!preFullDump()) return;
    } else {
        if (!preChangeDump()) return;
    }

#ifdef VL_TRACE_THREADED
    // Get the trace buffer we are about to fill
    VerilatedTraceEntry* const bufferp = getTraceBuffer();
    m_traceBufferWritep = bufferp;
    m_traceBufferEndp = bufferp + m_traceBufferSize;

    // Currently only incremental dumps run on the worker thread
    if (VL_LIKELY(!m_fullDump)) {
        // Tell worker to update time point
        (m_traceBufferWritep++)->cmd = VerilatedTraceCommand::TIME_CHANGE;
        (m_traceBufferWritep++)->timeui = timeui;
    } else {
        // Update time point
        emitTimeChange(timeui);
    }
#else
    // Update time point
    emitTimeChange(timeui);
#endif

    // Run the callbacks
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No more need for next dump to be full
        for (vluint32_t ent = 0; ent < m_callbacks.size(); ++ent) {
            VerilatedTraceCallInfo* cip = m_callbacks[ent];
            (cip->m_fullcb)(self(), cip->m_userthis, cip->m_code);
        }
    } else {
        for (vluint32_t ent = 0; ent < m_callbacks.size(); ++ent) {
            VerilatedTraceCallInfo* cip = m_callbacks[ent];
            (cip->m_changecb)(self(), cip->m_userthis, cip->m_code);
        }
    }

#ifdef VL_TRACE_THREADED
    // Mark end of the trace buffer we just filled
    (m_traceBufferWritep++)->cmd = VerilatedTraceCommand::END;

    // Assert no buffer overflow
    assert(m_traceBufferWritep - bufferp <= m_traceBufferSize);

    // Pass it to the worker thread
    m_buffersToWorker.put(bufferp);
#endif
}

//=============================================================================
// Non-hot path internal interface to Verilator generated code

template <>
void VerilatedTrace<VL_DERIVED_T>::addCallback(callback_t initcb, callback_t fullcb,
                                               callback_t changecb,
                                               void* userthis) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(timeLastDump() != 0)) {
        std::string msg = (std::string("Internal: ") + __FILE__ + "::" + __FUNCTION__
                           + " called with already open file");
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
    }
    VerilatedTraceCallInfo* cip = new VerilatedTraceCallInfo(initcb, fullcb, changecb, userthis);
    m_callbacks.push_back(cip);
}

//=========================================================================
// Hot path internal interface to Verilator generated code

// These functions must write the new value back into the old value store,
// and subsequently call the format specific emit* implementations. Note
// that this file must be included in the format specific implementation, so
// the emit* functions can be inlined for performance.

template <> void VerilatedTrace<VL_DERIVED_T>::fullBit(vluint32_t* oldp, vluint32_t newval) {
    *oldp = newval;
    self()->emitBit(oldp - m_sigs_oldvalp, newval);
}

// We want these functions specialized for sizes to avoid hard to predict
// branches, but we don't want them inlined, so we explicitly instantiate the
// template for each size used by Verilator.
template <>
template <int T_Bits>
void VerilatedTrace<VL_DERIVED_T>::fullBus(vluint32_t* oldp, vluint32_t newval) {
    *oldp = newval;
    self()->emitBus<T_Bits>(oldp - m_sigs_oldvalp, newval);
}

// Note: No specialization for width 1, covered by 'fullBit'
template void VerilatedTrace<VL_DERIVED_T>::fullBus<2>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<3>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<4>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<5>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<6>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<7>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<8>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<9>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<10>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<11>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<12>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<13>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<14>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<15>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<16>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<17>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<18>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<19>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<20>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<21>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<22>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<23>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<24>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<25>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<26>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<27>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<28>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<29>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<30>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<31>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedTrace<VL_DERIVED_T>::fullBus<32>(vluint32_t* oldp, vluint32_t newval);

template <>
void VerilatedTrace<VL_DERIVED_T>::fullQuad(vluint32_t* oldp, vluint64_t newval, int bits) {
    *reinterpret_cast<vluint64_t*>(oldp) = newval;
    self()->emitQuad(oldp - m_sigs_oldvalp, newval, bits);
}
template <>
void VerilatedTrace<VL_DERIVED_T>::fullArray(vluint32_t* oldp, const vluint32_t* newvalp,
                                             int bits) {
    for (int i = 0; i < (bits + 31) / 32; ++i) oldp[i] = newvalp[i];
    self()->emitArray(oldp - m_sigs_oldvalp, newvalp, bits);
}
template <> void VerilatedTrace<VL_DERIVED_T>::fullFloat(vluint32_t* oldp, float newval) {
    // cppcheck-suppress invalidPointerCast
    *reinterpret_cast<float*>(oldp) = newval;
    self()->emitFloat(oldp - m_sigs_oldvalp, newval);
}
template <> void VerilatedTrace<VL_DERIVED_T>::fullDouble(vluint32_t* oldp, double newval) {
    // cppcheck-suppress invalidPointerCast
    *reinterpret_cast<double*>(oldp) = newval;
    self()->emitDouble(oldp - m_sigs_oldvalp, newval);
}
