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
    typedef typename VerilatedTrace<VL_DERIVED_T>::callback_t callback_t;

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

//=============================================================================
// VerilatedTrace

template <>
VerilatedTrace<VL_DERIVED_T>::VerilatedTrace()
    : m_sigs_oldvalp(NULL)
    , m_timeLastDump(0)
    , m_fullDump(true)
    , m_nextCode(0)
    , m_scopeEscape('.')
    , m_timeRes(1e-9)
    , m_timeUnit(1e-9) {
    set_time_unit(Verilated::timeunitString());
    set_time_resolution(Verilated::timeprecisionString());
}

template <> VerilatedTrace<VL_DERIVED_T>::~VerilatedTrace() {
    if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = NULL);
    while (!m_callbacks.empty()) {
        delete m_callbacks.back();
        m_callbacks.pop_back();
    }
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
    if (VL_UNLIKELY(m_fullDump)) {
        if (!preFullDump()) return;
        emitTimeChange(timeui);
        m_fullDump = false;  // No more need for next dump to be full
        for (vluint32_t ent = 0; ent < m_callbacks.size(); ent++) {
            VerilatedTraceCallInfo* cip = m_callbacks[ent];
            (cip->m_fullcb)(self(), cip->m_userthis, cip->m_code);
        }
    } else {
        if (!preChangeDump()) return;
        emitTimeChange(timeui);
        for (vluint32_t ent = 0; ent < m_callbacks.size(); ++ent) {
            VerilatedTraceCallInfo* cip = m_callbacks[ent];
            (cip->m_changecb)(self(), cip->m_userthis, cip->m_code);
        }
    }
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
