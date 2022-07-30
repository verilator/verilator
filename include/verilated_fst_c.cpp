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
/// \brief Verilated C++ tracing in FST format implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use --trace-fst.
///
/// Use "verilator --trace-fst" to add this to the Makefile for the linker.
///
//=============================================================================

// clang-format off

#define __STDC_LIMIT_MACROS  // UINT64_MAX
#include "verilated.h"
#include "verilated_fst_c.h"

// GTKWave configuration
#ifdef VL_THREADED
# define HAVE_LIBPTHREAD
# define FST_WRITER_PARALLEL
#endif

// Include the GTKWave implementation directly
#define FST_CONFIG_INCLUDE "fst_config.h"
#include "gtkwave/fastlz.c"
#include "gtkwave/fstapi.c"
#include "gtkwave/lz4.c"

#include <algorithm>
#include <iterator>
#include <sstream>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

// clang-format on

//=============================================================================
// Check that vltscope_t matches fstScopeType

static_assert(static_cast<int>(FST_ST_VCD_MODULE) == static_cast<int>(VLT_TRACE_SCOPE_MODULE),
              "VLT_TRACE_SCOPE_MODULE mismatches");
static_assert(static_cast<int>(FST_ST_VCD_TASK) == static_cast<int>(VLT_TRACE_SCOPE_TASK),
              "VLT_TRACE_SCOPE_TASK mismatches");
static_assert(static_cast<int>(FST_ST_VCD_FUNCTION) == static_cast<int>(VLT_TRACE_SCOPE_FUNCTION),
              "VLT_TRACE_SCOPE_FUNCTION mismatches");
static_assert(static_cast<int>(FST_ST_VCD_BEGIN) == static_cast<int>(VLT_TRACE_SCOPE_BEGIN),
              "VLT_TRACE_SCOPE_BEGIN mismatches");
static_assert(static_cast<int>(FST_ST_VCD_FORK) == static_cast<int>(VLT_TRACE_SCOPE_FORK),
              "VLT_TRACE_SCOPE_FORK mismatches");
static_assert(static_cast<int>(FST_ST_VCD_GENERATE) == static_cast<int>(VLT_TRACE_SCOPE_GENERATE),
              "VLT_TRACE_SCOPE_GENERATE mismatches");
static_assert(static_cast<int>(FST_ST_VCD_STRUCT) == static_cast<int>(VLT_TRACE_SCOPE_STRUCT),
              "VLT_TRACE_SCOPE_STRUCT mismatches");
static_assert(static_cast<int>(FST_ST_VCD_UNION) == static_cast<int>(VLT_TRACE_SCOPE_UNION),
              "VLT_TRACE_SCOPE_UNION mismatches");
static_assert(static_cast<int>(FST_ST_VCD_CLASS) == static_cast<int>(VLT_TRACE_SCOPE_CLASS),
              "VLT_TRACE_SCOPE_CLASS mismatches");
static_assert(static_cast<int>(FST_ST_VCD_INTERFACE)
                  == static_cast<int>(VLT_TRACE_SCOPE_INTERFACE),
              "VLT_TRACE_SCOPE_INTERFACE mismatches");
static_assert(static_cast<int>(FST_ST_VCD_PACKAGE) == static_cast<int>(VLT_TRACE_SCOPE_PACKAGE),
              "VLT_TRACE_SCOPE_PACKAGE mismatches");
static_assert(static_cast<int>(FST_ST_VCD_PROGRAM) == static_cast<int>(VLT_TRACE_SCOPE_PROGRAM),
              "VLT_TRACE_SCOPE_PROGRAM mismatches");

//=============================================================================
// Specialization of the generics for this trace format

#define VL_SUB_T VerilatedFst
#define VL_BUF_T VerilatedFstBuffer
#include "verilated_trace_imp.h"
#undef VL_SUB_T
#undef VL_BUF_T

//=============================================================================
// VerilatedFst

VerilatedFst::VerilatedFst(void* /*fst*/) {}

VerilatedFst::~VerilatedFst() {
    if (m_fst) fstWriterClose(m_fst);
    if (m_symbolp) VL_DO_CLEAR(delete[] m_symbolp, m_symbolp = nullptr);
    if (m_strbuf) VL_DO_CLEAR(delete[] m_strbuf, m_strbuf = nullptr);
}

void VerilatedFst::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    m_fst = fstWriterCreate(filename, 1);
    fstWriterSetPackType(m_fst, FST_WR_PT_LZ4);
    fstWriterSetTimescaleFromString(m_fst, timeResStr().c_str());  // lintok-begin-on-ref
    if (m_useFstWriterThread) fstWriterSetParallelMode(m_fst, 1);
    fullDump(true);  // First dump must be full for fst

    m_curScope.clear();

    Super::traceInit();

    // Clear the scope stack
    auto it = m_curScope.begin();
    while (it != m_curScope.end()) {
        fstWriterSetUpscope(m_fst);
        it = m_curScope.erase(it);
    }

    // convert m_code2symbol into an array for fast lookup
    if (!m_symbolp) {
        m_symbolp = new fstHandle[nextCode()]{0};
        for (const auto& i : m_code2symbol) m_symbolp[i.first] = i.second;
    }
    m_code2symbol.clear();

    // Allocate string buffer for arrays
    if (!m_strbuf) m_strbuf = new char[maxBits() + 32];
}

void VerilatedFst::close() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::closeBase();
    fstWriterClose(m_fst);
    m_fst = nullptr;
}

void VerilatedFst::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
    fstWriterFlushContext(m_fst);
}

void VerilatedFst::emitTimeChange(uint64_t timeui) { fstWriterEmitTimeChange(m_fst, timeui); }

//=============================================================================
// Decl

void VerilatedFst::declDTypeEnum(int dtypenum, const char* name, uint32_t elements,
                                 unsigned int minValbits, const char** itemNamesp,
                                 const char** itemValuesp) {
    const fstEnumHandle enumNum
        = fstWriterCreateEnumTable(m_fst, name, elements, minValbits, itemNamesp, itemValuesp);
    m_local2fstdtype[dtypenum] = enumNum;
}

void VerilatedFst::declare(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                           fstVarType vartype, bool array, int arraynum, bool bussed, int msb,
                           int lsb) {
    const int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;

    const bool enabled = Super::declCode(code, name, bits, false);
    if (!enabled) return;

    std::string nameasstr = namePrefix() + name;
    std::istringstream nameiss{nameasstr};
    std::istream_iterator<std::string> beg(nameiss);
    std::istream_iterator<std::string> end;
    std::list<std::string> tokens(beg, end);  // Split name
    std::string symbol_name{tokens.back()};
    tokens.pop_back();  // Remove symbol name from hierarchy
    std::string tmpModName;

    // Find point where current and new scope diverge
    auto cur_it = m_curScope.begin();
    auto new_it = tokens.begin();
    while (cur_it != m_curScope.end() && new_it != tokens.end()) {
        if (*cur_it != *new_it) break;
        ++cur_it;
        ++new_it;
    }

    // Go back to the common point
    while (cur_it != m_curScope.end()) {
        fstWriterSetUpscope(m_fst);
        cur_it = m_curScope.erase(cur_it);
    }

    // Follow the hierarchy of the new variable from the common scope point
    while (new_it != tokens.end()) {
        if ((new_it->back() & 0x80)) {
            tmpModName = *new_it;
            tmpModName.pop_back();
            // If the scope ends with a non-ascii character, it will be 0x80 + fstScopeType
            fstWriterSetScope(m_fst, static_cast<fstScopeType>(new_it->back() & 0x7f),
                              tmpModName.c_str(), nullptr);
        } else {
            fstWriterSetScope(m_fst, FST_ST_VCD_SCOPE, new_it->c_str(), nullptr);
        }
        m_curScope.push_back(*new_it);
        new_it = tokens.erase(new_it);
    }

    std::stringstream name_ss;
    name_ss << symbol_name;
    if (array) name_ss << "[" << arraynum << "]";
    if (bussed) name_ss << " [" << msb << ":" << lsb << "]";
    std::string name_str = name_ss.str();

    if (dtypenum > 0) {
        const fstEnumHandle enumNum = m_local2fstdtype[dtypenum];
        fstWriterEmitEnumTableRef(m_fst, enumNum);
    }

    const auto it = vlstd::as_const(m_code2symbol).find(code);
    if (it == m_code2symbol.end()) {  // New
        m_code2symbol[code]
            = fstWriterCreateVar(m_fst, vartype, vardir, bits, name_str.c_str(), 0);
    } else {  // Alias
        fstWriterCreateVar(m_fst, vartype, vardir, bits, name_str.c_str(), it->second);
    }
}

void VerilatedFst::declBit(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                           fstVarType vartype, bool array, int arraynum) {
    declare(code, name, dtypenum, vardir, vartype, array, arraynum, false, 0, 0);
}
void VerilatedFst::declBus(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                           fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, dtypenum, vardir, vartype, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declQuad(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                            fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, dtypenum, vardir, vartype, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declArray(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                             fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, dtypenum, vardir, vartype, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declDouble(uint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                              fstVarType vartype, bool array, int arraynum) {
    declare(code, name, dtypenum, vardir, vartype, array, arraynum, false, 63, 0);
}

//=============================================================================
// Get/commit trace buffer

VerilatedFst::Buffer* VerilatedFst::getTraceBuffer() {
#ifdef VL_THREADED
    if (offload()) return new OffloadBuffer{*this};
#endif
    return new Buffer{*this};
}

void VerilatedFst::commitTraceBuffer(VerilatedFst::Buffer* bufp) {
#ifdef VL_THREADED
    if (offload()) {
        OffloadBuffer* const offloadBufferp = static_cast<OffloadBuffer*>(bufp);
        if (offloadBufferp->m_offloadBufferWritep) {
            m_offloadBufferWritep = offloadBufferp->m_offloadBufferWritep;
            return;  // Buffer will be deleted by the offload thread
        }
    }
#endif
    delete bufp;
}

//=============================================================================
// Configure

void VerilatedFst::configure(const VerilatedTraceConfig& config) {
    // If at least one model requests the FST writer thread, then use it
    m_useFstWriterThread |= config.m_useFstWriterThread;
}

//=============================================================================
// VerilatedFstBuffer implementation

//=============================================================================
// Trace rendering primitives

// Note: emit* are only ever called from one place (full* in
// verilated_trace_imp.h, which is included in this file at the top),
// so always inline them.

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitBit(uint32_t code, CData newval) {
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    fstWriterEmitValueChange(m_fst, m_symbolp[code], newval ? "1" : "0");
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitCData(uint32_t code, CData newval, int bits) {
    char buf[VL_BYTESIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtCDataToStr(buf, newval << (VL_BYTESIZE - bits));
    fstWriterEmitValueChange(m_fst, m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitSData(uint32_t code, SData newval, int bits) {
    char buf[VL_SHORTSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtSDataToStr(buf, newval << (VL_SHORTSIZE - bits));
    fstWriterEmitValueChange(m_fst, m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitIData(uint32_t code, IData newval, int bits) {
    char buf[VL_IDATASIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtIDataToStr(buf, newval << (VL_IDATASIZE - bits));
    fstWriterEmitValueChange(m_fst, m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitQData(uint32_t code, QData newval, int bits) {
    char buf[VL_QUADSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtQDataToStr(buf, newval << (VL_QUADSIZE - bits));
    fstWriterEmitValueChange(m_fst, m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitWData(uint32_t code, const WData* newvalp, int bits) {
    int words = VL_WORDS_I(bits);
    char* wp = m_strbuf;
    // Convert the most significant word
    const int bitsInMSW = VL_BITBIT_E(bits) ? VL_BITBIT_E(bits) : VL_EDATASIZE;
    cvtEDataToStr(wp, newvalp[--words] << (VL_EDATASIZE - bitsInMSW));
    wp += bitsInMSW;
    // Convert the remaining words
    while (words > 0) {
        cvtEDataToStr(wp, newvalp[--words]);
        wp += VL_EDATASIZE;
    }
    fstWriterEmitValueChange(m_fst, m_symbolp[code], m_strbuf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitDouble(uint32_t code, double newval) {
    fstWriterEmitValueChange(m_fst, m_symbolp[code], &newval);
}
