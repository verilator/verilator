// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2025 by Wilson Snyder. This program is free software; you
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

#include "verilated.h"
#include "verilated_fst_c.h"

// GTKWave configuration
#define HAVE_LIBPTHREAD
#define FST_WRITER_PARALLEL
#define LZ4_DISABLE_DEPRECATE_WARNINGS

// Include the GTKWave implementation directly
#define FST_CONFIG_INCLUDE "fst_config.h"
#include "gtkwave/fastlz.c"
#include "gtkwave/fstapi.c"
#include "gtkwave/lz4.c"

#include <algorithm>
#include <iterator>
#include <sstream>
#include <type_traits>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

#if defined(_WIN32) || defined(__MINGW32__)
# include <direct.h>  // _mkdir
#else
# include <sys/stat.h> // mkdir
#endif

#include <iostream>

// clang-format on

//=============================================================================
// Check that forward declared types matches the FST API types

static_assert(std::is_same<vlFstHandle, fstHandle>::value, "vlFstHandle mismatch");
static_assert(std::is_same<vlFstEnumHandle, fstEnumHandle>::value, "vlFstHandle mismatch");

//=============================================================================
// Specialization of the generics for this trace format

#define VL_SUB_T VerilatedFst
#define VL_BUF_T VerilatedFstBuffer
#include "verilated_trace_imp.h"
#undef VL_SUB_T
#undef VL_BUF_T

//=============================================================================
// VerilatedFstWriter

class VerilatedFstWriter final {
    void* m_fst = nullptr;

public:
    uint64_t m_timeui = 0;

    VerilatedFstWriter(const std::string& filename, const std::string& timeRes,
                       bool useWriterThread) {
        m_fst = fstWriterCreate(filename.c_str(), 1);
        fstWriterSetPackType(m_fst, FST_WR_PT_LZ4);
        fstWriterSetTimescaleFromString(m_fst, timeRes.c_str());  // lintok-begin-on-ref
        if (useWriterThread) fstWriterSetParallelMode(m_fst, 1);
    }

    ~VerilatedFstWriter() { fstWriterClose(m_fst); }

    void flush() { fstWriterFlushContext(m_fst); }

    void pushScope(enum fstScopeType scopeType, const char* scopeName) {
        fstWriterSetScope(m_fst, scopeType, scopeName, nullptr);
    }

    void popScope() { fstWriterSetUpscope(m_fst); }

    fstEnumHandle createEnumTable(const char* name, uint32_t elements, unsigned int minValbits,
                                  const char** itemNamesp, const char** itemValuesp) {
        return fstWriterCreateEnumTable(m_fst, name, elements, minValbits, itemNamesp,
                                        itemValuesp);
    }

    fstHandle createVar(enum fstVarType varType, enum fstVarDir varDir, uint32_t bits,
                        const std::string& name, fstHandle aliasHandle) {
        return fstWriterCreateVar(m_fst, varType, varDir, bits, name.c_str(), aliasHandle);
    }

    void emitEnumTableRef(fstEnumHandle enumHandle) {
        fstWriterEmitEnumTableRef(m_fst, enumHandle);
    }

    void emitValueChange(fstHandle handle, const void* val) {
        fstWriterEmitValueChange(m_fst, handle, val);
    }

    bool flushPending() { return fstWriterGetFlushContextPending(m_fst); }

    // Static as might be called from worker thread
    static void emitTimeChange(void* p, bool flush) {
        VerilatedFstWriter* const selfp = static_cast<VerilatedFstWriter*>(p);
        if (flush) selfp->flush();
        fstWriterEmitTimeChange(selfp->m_fst, selfp->m_timeui);
    }
};

//=============================================================================
// VerilatedFst

VerilatedFst::VerilatedFst(void* /*fst*/) {}

VerilatedFst::~VerilatedFst() {
    for (VerilatedFstWriter* const writerp : m_writerps) delete writerp;
    m_writerps.clear();
    if (m_symbolp) VL_DO_CLEAR(delete[] m_symbolp, m_symbolp = nullptr);
    m_strbufps.clear();
}

void VerilatedFst::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};

    const std::string timeRes = timeResStr();
    if (split()) {
#if defined(_WIN32) || defined(__MINGW32__)
        _mkdir(filename);
#else
        mkdir(filename, 0777);
#endif
        for (uint32_t n = 0; n < nSplits(); ++n) {
            const std::string splitName = std::string{filename} + "/" + std::to_string(n);
            m_writerps.push_back(new VerilatedFstWriter{splitName, timeRes, m_useFstWriterThread});
        }
    } else {
        m_writerps.push_back(new VerilatedFstWriter{filename, timeRes, m_useFstWriterThread});
    }
    constDump(true);  // First dump must contain the const signals
    fullDump(true);  // First dump must be full for fst
    Super::traceInit();

    // convert m_code2symbol into an array for fast lookup
    if (!m_symbolp) {
        m_symbolp = new fstHandle[nextCode()]{0};
        for (const auto& i : m_code2symbol) m_symbolp[i.first] = i.second;
    }
    m_code2symbol.clear();

    // Allocate buffer for data
    m_strbufps.resize(m_writerps.size());
    for (std::unique_ptr<char[]>& uptr : m_strbufps) uptr.reset(new char[maxBits() + 32]);
}

void VerilatedFst::close() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::closeBase();
    for (VerilatedFstWriter* const writerp : m_writerps) delete writerp;
    m_writerps.clear();
}

void VerilatedFst::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
    for (VerilatedFstWriter* const writerp : m_writerps) writerp->flush();
}

void VerilatedFst::emitTimeChange(uint64_t timeui) {
    // Pick up the thread pool
    if (VlThreadPool* const threadPoolp = static_cast<VlThreadPool*>(contextp()->threadPoolp())) {
        // Thread pool is available, use it to call VerilatedFstWriter::emitTimeChange,
        // as it might cause a long running compression phase to apply

        bool flush = false;
        for (VerilatedFstWriter* const writerp : m_writerps) {
            // If one has a flush pending (due to reaching buffer size limits),
            // then flush all of them, so all flush at the same time in parallel
            flush |= writerp->flushPending();
            // Set the time point to emit
            writerp->m_timeui = timeui;
        }

        // We use the whole pool + the main thread
        const size_t nThreads = std::min<size_t>(threadPoolp->numThreads() + 1, m_writerps.size());

        // Enque emitTimeChange on workers
        for (size_t i = 0; i < m_writerps.size(); ++i) {
            if (const size_t idx = i % nThreads) {
                threadPoolp->workerp(idx - 1)->addTask(VerilatedFstWriter::emitTimeChange,
                                                       m_writerps[i], flush);
            }
        }

        // emitTimeChange on main (this) thread
        for (size_t i = 0; i < m_writerps.size(); ++i) {
            if (i % nThreads == 0) VerilatedFstWriter::emitTimeChange(m_writerps[i], flush);
        }
    } else {
        // No thread pool, everything on main thread
        for (VerilatedFstWriter* const writerp : m_writerps) {
            // Set the time point to emit
            writerp->m_timeui = timeui;
            // Emit time change in this writer
            VerilatedFstWriter::emitTimeChange(writerp, false);
        }
    }
}

//=============================================================================
// Decl

void VerilatedFst::declDTypeEnum(int dtypenum, const char* name, uint32_t elements,
                                 unsigned int minValbits, const char** itemNamesp,
                                 const char** itemValuesp) {
    for (VerilatedFstWriter* const writerp : m_writerps) {
        const fstEnumHandle enumHandle
            = writerp->createEnumTable(name, elements, minValbits, itemNamesp, itemValuesp);
        const auto pair = m_local2fstdtype.emplace(dtypenum, enumHandle);
        // All enum handles should be the same in all files
        assert(pair.second || pair.first->second == enumHandle);
    }
}

// TODO: should return std::optional<fstScopeType>, but I can't have C++17
static std::pair<bool, fstScopeType> toFstScopeType(VerilatedTracePrefixType type) {
    switch (type) {
    case VerilatedTracePrefixType::ROOTIO_MODULE: return {true, FST_ST_VCD_MODULE};
    case VerilatedTracePrefixType::SCOPE_MODULE: return {true, FST_ST_VCD_MODULE};
    case VerilatedTracePrefixType::SCOPE_INTERFACE: return {true, FST_ST_VCD_INTERFACE};
    case VerilatedTracePrefixType::STRUCT_PACKED:
    case VerilatedTracePrefixType::STRUCT_UNPACKED: return {true, FST_ST_VCD_STRUCT};
    case VerilatedTracePrefixType::UNION_PACKED: return {true, FST_ST_VCD_UNION};
    default: return {false, /* unused so whatever, just need a value */ FST_ST_VCD_SCOPE};
    }
}

void VerilatedFst::pushPrefix(const std::string& name, VerilatedTracePrefixType type) {
    assert(!m_prefixStack.empty());  // Constructor makes an empty entry
    std::string pname = name;
    // An empty name means this is the root of a model created with name()=="".  The
    // tools get upset if we try to pass this as empty, so we put the signals under a
    // new scope, but the signals further down will be peers, not children (as usual
    // for name()!="")
    // Terminate earlier $root?
    if (m_prefixStack.back().second == VerilatedTracePrefixType::ROOTIO_MODULE) popPrefix();
    if (pname.empty()) {  // Start new temporary root
        pname = "$rootio";  // VCD names are not backslash escaped
        m_prefixStack.emplace_back("", VerilatedTracePrefixType::ROOTIO_WRAPPER);
        type = VerilatedTracePrefixType::ROOTIO_MODULE;
    }
    const std::string newPrefix = m_prefixStack.back().first + pname;
    const auto pair = toFstScopeType(type);
    const bool properScope = pair.first;
    const fstScopeType scopeType = pair.second;
    m_prefixStack.emplace_back(newPrefix + (properScope ? " " : ""), type);
    if (properScope) {
        const std::string scopeName = lastWord(newPrefix);
        for (VerilatedFstWriter* const writerp : m_writerps) {
            writerp->pushScope(scopeType, scopeName.c_str());
        }
    }
}

void VerilatedFst::popPrefix() {
    assert(!m_prefixStack.empty());
    const bool properScope = toFstScopeType(m_prefixStack.back().second).first;
    if (properScope) {
        for (VerilatedFstWriter* const writerp : m_writerps) writerp->popScope();
    }
    m_prefixStack.pop_back();
    assert(!m_prefixStack.empty());  // Always one left, the constructor's initial one
}

void VerilatedFst::declare(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                           VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                           VerilatedTraceSigType type, bool array, int arraynum, bool bussed,
                           int msb, int lsb) {
    const int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;

    const std::string hierarchicalName = m_prefixStack.back().first + name;

    const bool enabled = Super::declCode(code, hierarchicalName, bits);
    if (!enabled) return;

    assert(hierarchicalName.rfind(' ') != std::string::npos);
    std::stringstream name_ss;
    name_ss << lastWord(hierarchicalName);
    if (array) name_ss << "[" << arraynum << "]";
    if (bussed) name_ss << " [" << msb << ":" << lsb << "]";
    const std::string name_str = name_ss.str();

    const uint32_t widx = fidx % m_writerps.size();

    if (dtypenum > 0) m_writerps[widx]->emitEnumTableRef(m_local2fstdtype.at(dtypenum));

    fstVarDir varDir = FST_VD_IMPLICIT;
    switch (direction) {
    case VerilatedTraceSigDirection::INOUT: varDir = FST_VD_INOUT; break;
    case VerilatedTraceSigDirection::OUTPUT: varDir = FST_VD_OUTPUT; break;
    case VerilatedTraceSigDirection::INPUT: varDir = FST_VD_INPUT; break;
    case VerilatedTraceSigDirection::NONE: varDir = FST_VD_IMPLICIT; break;
    }

    fstVarType varType;
    // Doubles have special decoding properties, so must indicate if a double
    if (type == VerilatedTraceSigType::DOUBLE) {
        if (kind == VerilatedTraceSigKind::PARAMETER) {
            varType = FST_VT_VCD_REAL_PARAMETER;
        } else {
            varType = FST_VT_VCD_REAL;
        }
    }
    // clang-format off
    else if (kind == VerilatedTraceSigKind::PARAMETER) varType = FST_VT_VCD_PARAMETER;
    else if (kind == VerilatedTraceSigKind::SUPPLY0) varType = FST_VT_VCD_SUPPLY0;
    else if (kind == VerilatedTraceSigKind::SUPPLY1) varType = FST_VT_VCD_SUPPLY1;
    else if (kind == VerilatedTraceSigKind::TRI) varType = FST_VT_VCD_TRI;
    else if (kind == VerilatedTraceSigKind::TRI0) varType = FST_VT_VCD_TRI0;
    else if (kind == VerilatedTraceSigKind::TRI1) varType = FST_VT_VCD_TRI1;
    else if (kind == VerilatedTraceSigKind::WIRE) varType = FST_VT_VCD_WIRE;
    //
    else if (type == VerilatedTraceSigType::INTEGER) varType = FST_VT_VCD_INTEGER;
    else if (type == VerilatedTraceSigType::BIT) varType = FST_VT_SV_BIT;
    else if (type == VerilatedTraceSigType::LOGIC) varType = FST_VT_SV_LOGIC;
    else if (type == VerilatedTraceSigType::INT) varType = FST_VT_SV_INT;
    else if (type == VerilatedTraceSigType::SHORTINT) varType = FST_VT_SV_SHORTINT;
    else if (type == VerilatedTraceSigType::LONGINT) varType = FST_VT_SV_LONGINT;
    else if (type == VerilatedTraceSigType::BYTE) varType = FST_VT_SV_BYTE;
    else if (type == VerilatedTraceSigType::EVENT) varType = FST_VT_VCD_EVENT;
    else if (type == VerilatedTraceSigType::TIME) varType = FST_VT_VCD_TIME;
    else { assert(0); /* Unreachable */ }
    // clang-format on

    const auto pair = m_code2symbol.emplace(code, 0);
    if (pair.second) {  // New
        pair.first->second = m_writerps[widx]->createVar(varType, varDir, bits, name_str, 0);
    } else {  // Alias - Verilator arranged for aliases to have the same fidx, so this is safe
        m_writerps[widx]->createVar(varType, varDir, bits, name_str, pair.first->second);
    }
}

void VerilatedFst::declEvent(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                             VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                             VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, false, 0, 0);
}
void VerilatedFst::declBit(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                           VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                           VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, false, 0, 0);
}
void VerilatedFst::declBus(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                           VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                           VerilatedTraceSigType type, bool array, int arraynum, int msb,
                           int lsb) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declQuad(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                            VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                            VerilatedTraceSigType type, bool array, int arraynum, int msb,
                            int lsb) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declArray(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                             VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                             VerilatedTraceSigType type, bool array, int arraynum, int msb,
                             int lsb) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declDouble(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                              VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                              VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, fidx, name, dtypenum, direction, kind, type, array, arraynum, false, 63, 0);
}

//=============================================================================
// Get/commit trace buffer

VerilatedFst::Buffer* VerilatedFst::getTraceBuffer(uint32_t fidx) {
    if (offload()) return new OffloadBuffer{*this};
    return new Buffer{*this, fidx};
}

void VerilatedFst::commitTraceBuffer(VerilatedFst::Buffer* bufp) {
    if (offload()) {
        OffloadBuffer* const offloadBufferp = static_cast<OffloadBuffer*>(bufp);
        if (offloadBufferp->m_offloadBufferWritep) {
            m_offloadBufferWritep = offloadBufferp->m_offloadBufferWritep;
            return;  // Buffer will be deleted by the offload thread
        }
    }
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
void VerilatedFstBuffer::emitEvent(uint32_t code) {
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    m_writer.emitValueChange(m_symbolp[code], "1");
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitBit(uint32_t code, CData newval) {
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    m_writer.emitValueChange(m_symbolp[code], newval ? "1" : "0");
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitCData(uint32_t code, CData newval, int bits) {
    char buf[VL_BYTESIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtCDataToStr(buf, newval << (VL_BYTESIZE - bits));
    m_writer.emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitSData(uint32_t code, SData newval, int bits) {
    char buf[VL_SHORTSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtSDataToStr(buf, newval << (VL_SHORTSIZE - bits));
    m_writer.emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitIData(uint32_t code, IData newval, int bits) {
    char buf[VL_IDATASIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtIDataToStr(buf, newval << (VL_IDATASIZE - bits));
    m_writer.emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitQData(uint32_t code, QData newval, int bits) {
    char buf[VL_QUADSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtQDataToStr(buf, newval << (VL_QUADSIZE - bits));
    m_writer.emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitWData(uint32_t code, const WData* newvalp, int bits) {
    int words = VL_WORDS_I(bits);
    char* wp = m_strbufp;
    // Convert the most significant word
    const int bitsInMSW = VL_BITBIT_E(bits) ? VL_BITBIT_E(bits) : VL_EDATASIZE;
    cvtEDataToStr(wp, newvalp[--words] << (VL_EDATASIZE - bitsInMSW));
    wp += bitsInMSW;
    // Convert the remaining words
    while (words > 0) {
        cvtEDataToStr(wp, newvalp[--words]);
        wp += VL_EDATASIZE;
    }
    m_writer.emitValueChange(m_symbolp[code], m_strbufp);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitDouble(uint32_t code, double newval) {
    m_writer.emitValueChange(m_symbolp[code], &newval);
}
