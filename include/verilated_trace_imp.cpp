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
/// \brief Verilated common-format tracing implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use --trace.
///
/// Use "verilator --trace" to add this to the Makefile for the linker.
///
//=============================================================================

// clang-format off

#ifndef VL_CPPCHECK
#ifndef VL_DERIVED_T
# error "This file should be included in trace format implementations"
#endif

#include "verilated_intrinsics.h"
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
    char* endp = nullptr;
    double value = std::strtod(unitp, &endp);
    // On error so we allow just "ns" to return 1e-9.
    if (value == 0.0 && endp == unitp) value = 1;
    unitp = endp;
    for (; *unitp && std::isspace(*unitp); unitp++) {}
    switch (*unitp) {
    case 's': value *= 1e0; break;
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
    VL_SNPRINTF(valuestr, 100, "%0.0f%s", value, suffixp);
    return valuestr;  // Gets converted to string, so no ref to stack
}

#ifdef VL_TRACE_THREADED
//=========================================================================
// Buffer management

template <> vluint32_t* VerilatedTrace<VL_DERIVED_T>::getTraceBuffer() {
    vluint32_t* bufferp;
    // Some jitter is expected, so some number of alternative trace buffers are
    // required, but don't allocate more than 8 buffers.
    if (m_numTraceBuffers < 8) {
        // Allocate a new buffer if none is available
        if (!m_buffersFromWorker.tryGet(bufferp)) {
            ++m_numTraceBuffers;
            // Note: over allocate a bit so pointer comparison is well defined
            // if we overflow only by a small amount
            bufferp = new vluint32_t[m_traceBufferSize + 16];
        }
    } else {
        // Block until a buffer becomes available
        bufferp = m_buffersFromWorker.get();
    }
    return bufferp;
}

template <> void VerilatedTrace<VL_DERIVED_T>::waitForBuffer(const vluint32_t* buffp) {
    // Slow path code only called on flush/shutdown, so use a simple algorithm.
    // Collect buffers from worker and stash them until we get the one we want.
    std::deque<vluint32_t*> stash;
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
    bool shutdown = false;

    do {
        vluint32_t* const bufferp = m_buffersToWorker.get();

        VL_TRACE_THREAD_DEBUG("");
        VL_TRACE_THREAD_DEBUG("Got buffer: " << bufferp);

        const vluint32_t* readp = bufferp;

        while (true) {
            const vluint32_t cmd = readp[0];
            const vluint32_t top = cmd >> 4;
            // Always set this up, as it is almost always needed
            vluint32_t* const oldp = m_sigs_oldvalp + readp[1];
            // Note this increment needs to be undone on commands which do not
            // actually contain a code, but those are the rare cases.
            readp += 2;

            switch (cmd & 0xF) {
                //===
                // CHG_* commands
            case VerilatedTraceCommand::CHG_BIT_0:
                VL_TRACE_THREAD_DEBUG("Command CHG_BIT_0 " << top);
                chgBitImpl(oldp, 0);
                continue;
            case VerilatedTraceCommand::CHG_BIT_1:
                VL_TRACE_THREAD_DEBUG("Command CHG_BIT_1 " << top);
                chgBitImpl(oldp, 1);
                continue;
            case VerilatedTraceCommand::CHG_CDATA:
                VL_TRACE_THREAD_DEBUG("Command CHG_CDATA " << top);
                // Bits stored in bottom byte of command
                chgCDataImpl(oldp, *readp, top);
                readp += 1;
                continue;
            case VerilatedTraceCommand::CHG_SDATA:
                VL_TRACE_THREAD_DEBUG("Command CHG_SDATA " << top);
                // Bits stored in bottom byte of command
                chgSDataImpl(oldp, *readp, top);
                readp += 1;
                continue;
            case VerilatedTraceCommand::CHG_IDATA:
                VL_TRACE_THREAD_DEBUG("Command CHG_IDATA " << top);
                // Bits stored in bottom byte of command
                chgIDataImpl(oldp, *readp, top);
                readp += 1;
                continue;
            case VerilatedTraceCommand::CHG_QDATA:
                VL_TRACE_THREAD_DEBUG("Command CHG_QDATA " << top);
                // Bits stored in bottom byte of command
                chgQDataImpl(oldp, *reinterpret_cast<const QData*>(readp), top);
                readp += 2;
                continue;
            case VerilatedTraceCommand::CHG_WDATA:
                VL_TRACE_THREAD_DEBUG("Command CHG_WDATA " << top);
                chgWDataImpl(oldp, readp, top);
                readp += VL_WORDS_I(top);
                continue;
            case VerilatedTraceCommand::CHG_DOUBLE:
                VL_TRACE_THREAD_DEBUG("Command CHG_DOUBLE " << top);
                chgDoubleImpl(oldp, *reinterpret_cast<const double*>(readp));
                readp += 2;
                continue;

                //===
                // Rare commands
            case VerilatedTraceCommand::TIME_CHANGE:
                VL_TRACE_THREAD_DEBUG("Command TIME_CHANGE " << top);
                readp -= 1;  // No code in this command, undo increment
                emitTimeChange(*reinterpret_cast<const vluint64_t*>(readp));
                readp += 2;
                continue;

                //===
                // Commands ending this buffer
            case VerilatedTraceCommand::END: VL_TRACE_THREAD_DEBUG("Command END"); break;
            case VerilatedTraceCommand::SHUTDOWN:
                VL_TRACE_THREAD_DEBUG("Command SHUTDOWN");
                shutdown = true;
                break;

            //===
            // Unknown command
            default: {  // LCOV_EXCL_START
                VL_TRACE_THREAD_DEBUG("Command UNKNOWN");
                VL_PRINTF_MT("Trace command: 0x%08x\n", cmd);
                VL_FATAL_MT(__FILE__, __LINE__, "", "Unknown trace command");
                break;
            }  // LCOV_EXCL_STOP
            }

            // The above switch will execute 'continue' when necessary,
            // so if we ever reach here, we are done with the buffer.
            break;
        }

        VL_TRACE_THREAD_DEBUG("Returning buffer");

        // Return buffer
        m_buffersFromWorker.put(bufferp);
    } while (VL_LIKELY(!shutdown));
}

template <> void VerilatedTrace<VL_DERIVED_T>::shutdownWorker() {
    // If the worker thread is not running, done..
    if (!m_workerThread) return;

    // Hand an buffer with a shutdown command to the worker thread
    vluint32_t* const bufferp = getTraceBuffer();
    bufferp[0] = VerilatedTraceCommand::SHUTDOWN;
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

template <> void VerilatedTrace<VL_DERIVED_T>::closeBase() {
#ifdef VL_TRACE_THREADED
    shutdownWorker();
    while (m_numTraceBuffers) {
        delete[] m_buffersFromWorker.get();
        --m_numTraceBuffers;
    }
#endif
}

template <> void VerilatedTrace<VL_DERIVED_T>::flushBase() {
#ifdef VL_TRACE_THREADED
    // Hand an empty buffer to the worker thread
    vluint32_t* const bufferp = getTraceBuffer();
    *bufferp = VerilatedTraceCommand::END;
    m_buffersToWorker.put(bufferp);
    // Wait for it to be returned. As the processing is in-order,
    // this ensures all previous buffers have been processed.
    waitForBuffer(bufferp);
#endif
}

//=============================================================================
// Callbacks to run on global events

template <> void VerilatedTrace<VL_DERIVED_T>::onFlush(void* selfp) {
    // This calls 'flush' on the derived classo (which must then get any mutex)
    reinterpret_cast<VL_DERIVED_T*>(selfp)->flush();
}

template <> void VerilatedTrace<VL_DERIVED_T>::onExit(void* selfp) {
    // This calls 'close' on the derived class (which must then get any mutex)
    reinterpret_cast<VL_DERIVED_T*>(selfp)->close();
}

//=============================================================================
// VerilatedTrace

template <>
VerilatedTrace<VL_DERIVED_T>::VerilatedTrace()
    : m_sigs_oldvalp{nullptr}
    , m_timeLastDump{0}
    , m_fullDump{true}
    , m_nextCode{0}
    , m_numSignals{0}
    , m_maxBits{0}
    , m_scopeEscape{'.'}
    , m_timeRes{1e-9}
    , m_timeUnit {
    1e-9
}
#ifdef VL_TRACE_THREADED
, m_numTraceBuffers { 0 }
#endif
{
    set_time_unit(Verilated::threadContextp()->timeunitString());
    set_time_resolution(Verilated::threadContextp()->timeprecisionString());
}

template <> VerilatedTrace<VL_DERIVED_T>::~VerilatedTrace() {
    if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = nullptr);
    Verilated::removeFlushCb(VerilatedTrace<VL_DERIVED_T>::onFlush, this);
    Verilated::removeExitCb(VerilatedTrace<VL_DERIVED_T>::onExit, this);
#ifdef VL_TRACE_THREADED
    closeBase();
#endif
}

//=========================================================================
// Internals available to format specific implementations

template <> void VerilatedTrace<VL_DERIVED_T>::traceInit() VL_MT_UNSAFE {
    // Note: It is possible to re-open a trace file (VCD in particular),
    // so we must reset the next code here, but it must have the same number
    // of codes on re-open
    const vluint32_t expectedCodes = nextCode();
    m_nextCode = 1;
    m_numSignals = 0;
    m_maxBits = 0;

    // Call all initialize callbacks, which will:
    // - Call decl* for each signal
    // - Store the base code
    for (vluint32_t i = 0; i < m_initCbs.size(); ++i) {
        const CallbackRecord& cbr = m_initCbs[i];
        cbr.m_initCb(cbr.m_userp, self(), nextCode());
    }

    if (expectedCodes && nextCode() != expectedCodes) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "Reopening trace file with different number of signals");
    }

    // Now that we know the number of codes, allocate space for the buffer
    // holding previous signal values.
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new vluint32_t[nextCode()];

    // Set callback so flush/abort will flush this file
    Verilated::addFlushCb(VerilatedTrace<VL_DERIVED_T>::onFlush, this);
    Verilated::addExitCb(VerilatedTrace<VL_DERIVED_T>::onExit, this);

#ifdef VL_TRACE_THREADED
    // Compute trace buffer size. we need to be able to store a new value for
    // each signal, which is 'nextCode()' entries after the init callbacks
    // above have been run, plus up to 2 more words of metadata per signal,
    // plus fixed overhead of 1 for a termination flag and 3 for a time stamp
    // update.
    m_traceBufferSize = nextCode() + numSignals() * 2 + 4;

    // Start the worker thread
    m_workerThread.reset(new std::thread{&VerilatedTrace<VL_DERIVED_T>::workerThreadMain, this});
#endif
}

template <>
void VerilatedTrace<VL_DERIVED_T>::declCode(vluint32_t code, vluint32_t bits, bool tri) {
    if (VL_UNCOVERABLE(!code)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: internal trace problem, code 0 is illegal");
    }
    // Note: The tri-state flag is not used by Verilator, but is here for
    // compatibility with some foreign code.
    int codesNeeded = VL_WORDS_I(bits);
    if (tri) codesNeeded *= 2;
    m_nextCode = std::max(m_nextCode, code + codesNeeded);
    ++m_numSignals;
    m_maxBits = std::max(m_maxBits, bits);
}

//=========================================================================
// Internals available to format specific implementations

template <> std::string VerilatedTrace<VL_DERIVED_T>::timeResStr() const {
    return doubleToTimescale(m_timeRes);
}

//=========================================================================
// External interface to client code

template <> void VerilatedTrace<VL_DERIVED_T>::set_time_unit(const char* unitp) VL_MT_SAFE {
    m_timeUnit = timescaleToDouble(unitp);
}
template <> void VerilatedTrace<VL_DERIVED_T>::set_time_unit(const std::string& unit) VL_MT_SAFE {
    set_time_unit(unit.c_str());
}
template <> void VerilatedTrace<VL_DERIVED_T>::set_time_resolution(const char* unitp) VL_MT_SAFE {
    m_timeRes = timescaleToDouble(unitp);
}
template <>
void VerilatedTrace<VL_DERIVED_T>::set_time_resolution(const std::string& unit) VL_MT_SAFE {
    set_time_resolution(unit.c_str());
}

template <>
void VerilatedTrace<VL_DERIVED_T>::dump(vluint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex) {
    // Not really VL_MT_SAFE but more VL_MT_UNSAFE_ONE.
    // This does get the mutex, but if multiple threads are trying to dump
    // chances are the data being dumped will have other problems
    const VerilatedLockGuard lock{m_mutex};
    if (VL_UNCOVERABLE(m_timeLastDump && timeui <= m_timeLastDump)) {  // LCOV_EXCL_START
        VL_PRINTF_MT("%%Warning: previous dump at t=%" VL_PRI64 "u, requesting t=%" VL_PRI64
                     "u, dump call ignored\n",
                     m_timeLastDump, timeui);
        return;
    }  // LCOV_EXCL_STOP
    m_timeLastDump = timeui;

    Verilated::quiesce();

    // Call hook for format specific behaviour
    if (VL_UNLIKELY(m_fullDump)) {
        if (!preFullDump()) return;
    } else {
        if (!preChangeDump()) return;
    }

#ifdef VL_TRACE_THREADED
    // Currently only incremental dumps run on the worker thread
    vluint32_t* bufferp = nullptr;
    if (VL_LIKELY(!m_fullDump)) {
        // Get the trace buffer we are about to fill
        bufferp = getTraceBuffer();
        m_traceBufferWritep = bufferp;
        m_traceBufferEndp = bufferp + m_traceBufferSize;

        // Tell worker to update time point
        m_traceBufferWritep[0] = VerilatedTraceCommand::TIME_CHANGE;
        *reinterpret_cast<vluint64_t*>(m_traceBufferWritep + 1) = timeui;
        m_traceBufferWritep += 3;
    } else {
        // Update time point
        flushBase();
        emitTimeChange(timeui);
    }
#else
    // Update time point
    emitTimeChange(timeui);
#endif

    // Run the callbacks
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No more need for next dump to be full
        for (vluint32_t i = 0; i < m_fullCbs.size(); ++i) {
            const CallbackRecord& cbr = m_fullCbs[i];
            cbr.m_dumpCb(cbr.m_userp, self());
        }
    } else {
        for (vluint32_t i = 0; i < m_chgCbs.size(); ++i) {
            const CallbackRecord& cbr = m_chgCbs[i];
            cbr.m_dumpCb(cbr.m_userp, self());
        }
    }

    for (vluint32_t i = 0; i < m_cleanupCbs.size(); ++i) {
        const CallbackRecord& cbr = m_cleanupCbs[i];
        cbr.m_dumpCb(cbr.m_userp, self());
    }

#ifdef VL_TRACE_THREADED
    if (VL_LIKELY(bufferp)) {
        // Mark end of the trace buffer we just filled
        *m_traceBufferWritep++ = VerilatedTraceCommand::END;

        // Assert no buffer overflow
        assert(m_traceBufferWritep - bufferp <= m_traceBufferSize);

        // Pass it to the worker thread
        m_buffersToWorker.put(bufferp);
    }
#endif
}

//=============================================================================
// Non-hot path internal interface to Verilator generated code

template <>
void VerilatedTrace<VL_DERIVED_T>::addCallbackRecord(std::vector<CallbackRecord>& cbVec,
                                                     CallbackRecord& cbRec)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    if (VL_UNCOVERABLE(timeLastDump() != 0)) {  // LCOV_EXCL_START
        const std::string msg = (std::string{"Internal: "} + __FILE__ + "::" + __FUNCTION__
                                 + " called with already open file");
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
    }  // LCOV_EXCL_STOP
    cbVec.push_back(cbRec);
}

template <> void VerilatedTrace<VL_DERIVED_T>::addInitCb(initCb_t cb, void* userp) VL_MT_SAFE {
    CallbackRecord cbr{cb, userp};
    addCallbackRecord(m_initCbs, cbr);
}
template <> void VerilatedTrace<VL_DERIVED_T>::addFullCb(dumpCb_t cb, void* userp) VL_MT_SAFE {
    CallbackRecord cbr{cb, userp};
    addCallbackRecord(m_fullCbs, cbr);
}
template <> void VerilatedTrace<VL_DERIVED_T>::addChgCb(dumpCb_t cb, void* userp) VL_MT_SAFE {
    CallbackRecord cbr{cb, userp};
    addCallbackRecord(m_chgCbs, cbr);
}
template <> void VerilatedTrace<VL_DERIVED_T>::addCleanupCb(dumpCb_t cb, void* userp) VL_MT_SAFE {
    CallbackRecord cbr{cb, userp};
    addCallbackRecord(m_cleanupCbs, cbr);
}
template <> void VerilatedTrace<VL_DERIVED_T>::module(const std::string& name) VL_MT_UNSAFE {
    // Called via callbacks way above in call stack, which already hold m_mutex
    m_moduleName = name;
}

//=========================================================================
// Hot path internal interface to Verilator generated code

// These functions must write the new value back into the old value store,
// and subsequently call the format specific emit* implementations. Note
// that this file must be included in the format specific implementation, so
// the emit* functions can be inlined for performance.

template <> void VerilatedTrace<VL_DERIVED_T>::fullBit(vluint32_t* oldp, CData newval) {
    *oldp = newval;
    self()->emitBit(oldp - m_sigs_oldvalp, newval);
}

template <>
void VerilatedTrace<VL_DERIVED_T>::fullCData(vluint32_t* oldp, CData newval, int bits) {
    *oldp = newval;
    self()->emitCData(oldp - m_sigs_oldvalp, newval, bits);
}

template <>
void VerilatedTrace<VL_DERIVED_T>::fullSData(vluint32_t* oldp, SData newval, int bits) {
    *oldp = newval;
    self()->emitSData(oldp - m_sigs_oldvalp, newval, bits);
}

template <>
void VerilatedTrace<VL_DERIVED_T>::fullIData(vluint32_t* oldp, IData newval, int bits) {
    *oldp = newval;
    self()->emitIData(oldp - m_sigs_oldvalp, newval, bits);
}

template <>
void VerilatedTrace<VL_DERIVED_T>::fullQData(vluint32_t* oldp, QData newval, int bits) {
    *reinterpret_cast<QData*>(oldp) = newval;
    self()->emitQData(oldp - m_sigs_oldvalp, newval, bits);
}

template <>
void VerilatedTrace<VL_DERIVED_T>::fullWData(vluint32_t* oldp, const WData* newvalp, int bits) {
    for (int i = 0; i < VL_WORDS_I(bits); ++i) oldp[i] = newvalp[i];
    self()->emitWData(oldp - m_sigs_oldvalp, newvalp, bits);
}

template <> void VerilatedTrace<VL_DERIVED_T>::fullDouble(vluint32_t* oldp, double newval) {
    // cppcheck-suppress invalidPointerCast
    *reinterpret_cast<double*>(oldp) = newval;
    self()->emitDouble(oldp - m_sigs_oldvalp, newval);
}

//=========================================================================
// Primitives converting binary values to strings...

// All of these take a destination pointer where the string will be emitted,
// and a value to convert. There are a couple of variants for efficiency.

static inline void cvtCDataToStr(char* dstp, CData value) {
#ifdef VL_HAVE_SSE2
    // Similar to cvtSDataToStr but only the bottom 8 byte lanes are used
    const __m128i a = _mm_cvtsi32_si128(value);
    const __m128i b = _mm_unpacklo_epi8(a, a);
    const __m128i c = _mm_shufflelo_epi16(b, 0);
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i d = _mm_cmpeq_epi8(_mm_and_si128(c, m), m);
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), d);
    _mm_storel_epi64(reinterpret_cast<__m128i*>(dstp), result);
#else
    dstp[0] = '0' | static_cast<char>((value >> 7) & 1);
    dstp[1] = '0' | static_cast<char>((value >> 6) & 1);
    dstp[2] = '0' | static_cast<char>((value >> 5) & 1);
    dstp[3] = '0' | static_cast<char>((value >> 4) & 1);
    dstp[4] = '0' | static_cast<char>((value >> 3) & 1);
    dstp[5] = '0' | static_cast<char>((value >> 2) & 1);
    dstp[6] = '0' | static_cast<char>((value >> 1) & 1);
    dstp[7] = '0' | static_cast<char>(value & 1);
#endif
}

static inline void cvtSDataToStr(char* dstp, SData value) {
#ifdef VL_HAVE_SSE2
    // We want each bit in the 16-bit input value to end up in a byte lane
    // within the 128-bit XMM register. Note that x86 is little-endian and we
    // want the MSB of the input at the low address, so we will bit-reverse
    // at the same time.

    // Put value in bottom of 128-bit register a[15:0] = value
    const __m128i a = _mm_cvtsi32_si128(value);
    // Interleave bytes with themselves
    // b[15: 0] = {2{a[ 7:0]}} == {2{value[ 7:0]}}
    // b[31:16] = {2{a[15:8]}} == {2{value[15:8]}}
    const __m128i b = _mm_unpacklo_epi8(a, a);
    // Shuffle bottom 64 bits, note swapping high bytes with low bytes
    // c[31: 0] = {2{b[31:16]}} == {4{value[15:8}}
    // c[63:32] = {2{b[15: 0]}} == {4{value[ 7:0}}
    const __m128i c = _mm_shufflelo_epi16(b, 0x05);
    // Shuffle whole register
    // d[ 63: 0] = {2{c[31: 0]}} == {8{value[15:8}}
    // d[126:54] = {2{c[63:32]}} == {8{value[ 7:0}}
    const __m128i d = _mm_shuffle_epi32(c, 0x50);
    // Test each bit within the bytes, this sets each byte lane to 0
    // if the bit for that lane is 0 and to 0xff if the bit is 1.
    const __m128i m = _mm_set1_epi64x(0x0102040810204080);
    const __m128i e = _mm_cmpeq_epi8(_mm_and_si128(d, m), m);
    // Convert to ASCII by subtracting the masks from ASCII '0':
    // '0' - 0 is '0', '0' - -1 is '1'
    const __m128i result = _mm_sub_epi8(_mm_set1_epi8('0'), e);
    // Store the 16 characters to the un-aligned buffer
    _mm_storeu_si128(reinterpret_cast<__m128i*>(dstp), result);
#else
    cvtCDataToStr(dstp, value >> 8);
    cvtCDataToStr(dstp + 8, value);
#endif
}

static inline void cvtIDataToStr(char* dstp, IData value) {
#ifdef VL_HAVE_AVX2
    // Similar to cvtSDataToStr but the bottom 16-bits are processed in the
    // top half of the YMM registerss
    const __m256i a = _mm256_insert_epi32(_mm256_undefined_si256(), value, 0);
    const __m256i b = _mm256_permute4x64_epi64(a, 0);
    const __m256i s = _mm256_set_epi8(0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2,
                                      2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3);
    const __m256i c = _mm256_shuffle_epi8(b, s);
    const __m256i m = _mm256_set1_epi64x(0x0102040810204080);
    const __m256i d = _mm256_cmpeq_epi8(_mm256_and_si256(c, m), m);
    const __m256i result = _mm256_sub_epi8(_mm256_set1_epi8('0'), d);
    _mm256_storeu_si256(reinterpret_cast<__m256i*>(dstp), result);
#else
    cvtSDataToStr(dstp, value >> 16);
    cvtSDataToStr(dstp + 16, value);
#endif
}

static inline void cvtQDataToStr(char* dstp, QData value) {
    cvtIDataToStr(dstp, value >> 32);
    cvtIDataToStr(dstp + 32, value);
}

#define cvtEDataToStr cvtIDataToStr

//=============================================================================

#ifdef VERILATED_VCD_TEST

void verilated_trace_imp_selftest() {
#define SELF_CHECK(got, exp) \
    do { \
        if ((got) != (exp)) VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: selftest\n"); \
    } while (0)

#define SELF_CHECK_TS(scale) \
    SELF_CHECK(doubleToTimescale(timescaleToDouble(scale)), std::string{scale});
    SELF_CHECK_TS("100s");
    SELF_CHECK_TS("10s");
    SELF_CHECK_TS("1s");
    SELF_CHECK_TS("100ms");
    SELF_CHECK_TS("10ms");
    SELF_CHECK_TS("1ms");
    SELF_CHECK_TS("100us");
    SELF_CHECK_TS("10us");
    SELF_CHECK_TS("1us");
    SELF_CHECK_TS("100ns");
    SELF_CHECK_TS("10ns");
    SELF_CHECK_TS("1ns");
    SELF_CHECK_TS("100ps");
    SELF_CHECK_TS("10ps");
    SELF_CHECK_TS("1ps");
    SELF_CHECK_TS("100fs");
    SELF_CHECK_TS("10fs");
    SELF_CHECK_TS("1fs");
    SELF_CHECK_TS("100as");
    SELF_CHECK_TS("10as");
    SELF_CHECK_TS("1as");
}

#endif

#endif  // VL_CPPCHECK
