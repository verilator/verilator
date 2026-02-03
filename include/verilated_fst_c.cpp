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

// Include fstcpp library
#include "fstcpp/fstcpp_writer.h"

#include <algorithm>
#include <iterator>
#include <sstream>
#include <type_traits>
#include <vector>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

// clang-format on

//=============================================================================
// Check that forward declared types matches the FST API types

static_assert(std::is_same<vlFstHandle, fst::Handle>::value, "vlFstHandle mismatch");
static_assert(std::is_same<vlFstEnumHandle, fst::EnumHandle>::value, "vlFstHandle mismatch");

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
    if (m_fst) VL_DO_CLEAR(delete m_fst, m_fst = nullptr);
    if (m_symbolp) VL_DO_CLEAR(delete[] m_symbolp, m_symbolp = nullptr);
    if (m_strbufp) VL_DO_CLEAR(delete[] m_strbufp, m_strbufp = nullptr);
}

void VerilatedFst::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    m_fst = new fst::Writer{filename};
    m_fst->setWriterPackType(fst::WriterPackType::LZ4);
    m_fst->setTimecale(int8_t(round(log10(timeRes()))));
    // if (m_useFstWriterThread) fstWriterSetParallelMode(m_fst, 1);
    constDump(true);  // First dump must contain the const signals
    fullDump(true);  // First dump must be full for fst

    Super::traceInit();

    // convert m_code2symbol into an array for fast lookup
    if (!m_symbolp) {
        m_symbolp = new fst::Handle[nextCode()]{0};
        for (const auto& i : m_code2symbol) m_symbolp[i.first] = i.second;
    }
    m_code2symbol.clear();

    // Allocate string buffer for arrays
    if (!m_strbufp) m_strbufp = new char[maxBits() + 32];
}

void VerilatedFst::close() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::closeBase();
    emitTimeChangeMaybe();
    if (m_fst) m_fst->close();
    m_fst = nullptr;
}

void VerilatedFst::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
    emitTimeChangeMaybe();
    if (m_fst) m_fst->flushValueChangeData();
}

void VerilatedFst::emitTimeChange(uint64_t timeui) {
    if (!timeui) m_fst->emitTimeChange(timeui);
    m_timeui = timeui;
}

VL_ATTR_ALWINLINE
void VerilatedFst::emitTimeChangeMaybe() {
    if (VL_UNLIKELY(m_timeui)) {
        m_fst->emitTimeChange(m_timeui);
        m_timeui = 0;
    }
}

//=============================================================================
// Decl

void VerilatedFst::declDTypeEnum(int dtypenum, const char* name, uint32_t elements,
                                 unsigned int minValbits, const char** itemNamesp,
                                 const char** itemValuesp) {
    std::vector<std::pair<const char*, const char*>> itemNameValuesp{elements};
    for (uint32_t i = 0; i < elements; ++i) {
        itemNameValuesp[i].first = itemNamesp[i];
        itemNameValuesp[i].second = itemValuesp[i];
    }
    const fst::EnumHandle enumNum = m_fst->createEnumTable(name, minValbits, itemNameValuesp);
    m_local2fstdtype[dtypenum] = enumNum;
}

// TODO: should return std::optional<fstScopeType>, but I can't have C++17
static std::pair<bool, fst::Hierarchy::ScopeType> toFstScopeType(VerilatedTracePrefixType type) {
    switch (type) {
    case VerilatedTracePrefixType::SCOPE_MODULE:
        return {true, fst::Hierarchy::ScopeType::VCD_MODULE};
    case VerilatedTracePrefixType::SCOPE_INTERFACE:
        return {true, fst::Hierarchy::ScopeType::VCD_INTERFACE};
    case VerilatedTracePrefixType::STRUCT_PACKED:
    case VerilatedTracePrefixType::STRUCT_UNPACKED:
        return {true, fst::Hierarchy::ScopeType::VCD_STRUCT};
    case VerilatedTracePrefixType::UNION_PACKED:
        return {true, fst::Hierarchy::ScopeType::VCD_UNION};
    default:
        return {false,
                /* unused so whatever, just need a value */ fst::Hierarchy::ScopeType::VCD_MODULE};
    }
}

void VerilatedFst::pushPrefix(const std::string& name, VerilatedTracePrefixType type) {
    assert(!m_prefixStack.empty());  // Constructor makes an empty entry
    // An empty name means this is the root of a model created with
    // name()=="".  The tools get upset if we try to pass this as empty, so
    // we put the signals under a new $rootio scope, but the signals
    // further down will be peers, not children (as usual for name()!="").
    const std::string prevPrefix = m_prefixStack.back().first;
    if (name == "$rootio" && !prevPrefix.empty()) {
        // Upper has name, we can suppress inserting $rootio, but still push so popPrefix works
        m_prefixStack.emplace_back(prevPrefix, VerilatedTracePrefixType::ROOTIO_WRAPPER);
        return;
    } else if (name.empty()) {
        m_prefixStack.emplace_back(prevPrefix, VerilatedTracePrefixType::ROOTIO_WRAPPER);
        return;
    }

    // This code assumes a signal at a given prefix level is declared before
    // any pushPrefix are done at that same level.
    const std::string newPrefix = prevPrefix + name;
    const auto pair = toFstScopeType(type);
    const bool properScope = pair.first;
    const fst::Hierarchy::ScopeType scopeType = pair.second;
    m_prefixStack.emplace_back(newPrefix + (properScope ? " " : ""), type);
    if (properScope) {
        const std::string scopeName = lastWord(newPrefix);
        m_fst->setScope(scopeType, scopeName, std::string{});
    }
}

void VerilatedFst::popPrefix() {
    assert(!m_prefixStack.empty());
    const bool properScope = toFstScopeType(m_prefixStack.back().second).first;
    if (properScope) m_fst->upscope();
    m_prefixStack.pop_back();
    assert(!m_prefixStack.empty());  // Always one left, the constructor's initial one
}

void VerilatedFst::declare(uint32_t code, const char* name, int dtypenum,
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

    if (dtypenum > 0) m_fst->emitEnumTableRef(m_local2fstdtype[dtypenum]);

    fst::Hierarchy::VarDirection varDir = fst::Hierarchy::VarDirection::IMPLICIT;
    switch (direction) {
    case VerilatedTraceSigDirection::INOUT: varDir = fst::Hierarchy::VarDirection::INOUT; break;
    case VerilatedTraceSigDirection::OUTPUT: varDir = fst::Hierarchy::VarDirection::OUTPUT; break;
    case VerilatedTraceSigDirection::INPUT: varDir = fst::Hierarchy::VarDirection::INPUT; break;
    case VerilatedTraceSigDirection::NONE: varDir = fst::Hierarchy::VarDirection::IMPLICIT; break;
    }

    fst::Hierarchy::VarType varType;
    // Doubles have special decoding properties, so must indicate if a double
    if (type == VerilatedTraceSigType::DOUBLE) {
        if (kind == VerilatedTraceSigKind::PARAMETER) {
            varType = fst::Hierarchy::VarType::VCD_REAL_PARAMETER;
        } else {
            varType = fst::Hierarchy::VarType::VCD_REAL;
        }
    }
    // clang-format off
    else if (kind == VerilatedTraceSigKind::PARAMETER) varType = fst::Hierarchy::VarType::VCD_PARAMETER;
    else if (kind == VerilatedTraceSigKind::SUPPLY0) varType = fst::Hierarchy::VarType::VCD_SUPPLY0;
    else if (kind == VerilatedTraceSigKind::SUPPLY1) varType = fst::Hierarchy::VarType::VCD_SUPPLY1;
    else if (kind == VerilatedTraceSigKind::TRI) varType = fst::Hierarchy::VarType::VCD_TRI;
    else if (kind == VerilatedTraceSigKind::TRI0) varType = fst::Hierarchy::VarType::VCD_TRI0;
    else if (kind == VerilatedTraceSigKind::TRI1) varType = fst::Hierarchy::VarType::VCD_TRI1;
    else if (kind == VerilatedTraceSigKind::WIRE) varType = fst::Hierarchy::VarType::VCD_WIRE;
    //
    else if (type == VerilatedTraceSigType::INTEGER) varType = fst::Hierarchy::VarType::VCD_INTEGER;
    else if (type == VerilatedTraceSigType::BIT) varType = fst::Hierarchy::VarType::SV_BIT;
    else if (type == VerilatedTraceSigType::LOGIC) varType = fst::Hierarchy::VarType::SV_LOGIC;
    else if (type == VerilatedTraceSigType::INT) varType = fst::Hierarchy::VarType::SV_INT;
    else if (type == VerilatedTraceSigType::SHORTINT) varType = fst::Hierarchy::VarType::SV_SHORTINT;
    else if (type == VerilatedTraceSigType::LONGINT) varType = fst::Hierarchy::VarType::SV_LONGINT;
    else if (type == VerilatedTraceSigType::BYTE) varType = fst::Hierarchy::VarType::SV_BYTE;
    else if (type == VerilatedTraceSigType::EVENT) varType = fst::Hierarchy::VarType::VCD_EVENT;
    else if (type == VerilatedTraceSigType::TIME) varType = fst::Hierarchy::VarType::VCD_TIME;
    else { assert(0); /* Unreachable */ }
    // clang-format on

    const auto it = vlstd::as_const(m_code2symbol).find(code);
    if (it == m_code2symbol.end()) {  // New
        m_code2symbol[code] = m_fst->createVar(varType, varDir, bits, name_str.c_str(), 0);
    } else {  // Alias
        m_fst->createVar(varType, varDir, bits, name_str.c_str(), it->second);
    }
}

void VerilatedFst::declEvent(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                             VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                             VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, false, 0, 0);
}
void VerilatedFst::declBit(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                           VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                           VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, false, 0, 0);
}
void VerilatedFst::declBus(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                           VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                           VerilatedTraceSigType type, bool array, int arraynum, int msb,
                           int lsb) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declQuad(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                            VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                            VerilatedTraceSigType type, bool array, int arraynum, int msb,
                            int lsb) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declArray(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                             VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                             VerilatedTraceSigType type, bool array, int arraynum, int msb,
                             int lsb) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, true, msb, lsb);
}
void VerilatedFst::declDouble(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                              VerilatedTraceSigDirection direction, VerilatedTraceSigKind kind,
                              VerilatedTraceSigType type, bool array, int arraynum) {
    declare(code, name, dtypenum, direction, kind, type, array, arraynum, false, 63, 0);
}

//=============================================================================
// Get/commit trace buffer

VerilatedFst::Buffer* VerilatedFst::getTraceBuffer(uint32_t fidx) {
    if (offload()) return new OffloadBuffer{*this};
    return new Buffer{*this};
}

void VerilatedFst::commitTraceBuffer(VerilatedFst::Buffer* bufp) {
    if (offload()) {
        const OffloadBuffer* const offloadBufferp = static_cast<const OffloadBuffer*>(bufp);
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
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], "1");
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitBit(uint32_t code, CData newval) {
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], newval ? "1" : "0");
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitCData(uint32_t code, CData newval, int bits) {
    char buf[VL_BYTESIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtCDataToStr(buf, newval << (VL_BYTESIZE - bits));
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitSData(uint32_t code, SData newval, int bits) {
    char buf[VL_SHORTSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtSDataToStr(buf, newval << (VL_SHORTSIZE - bits));
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitIData(uint32_t code, IData newval, int bits) {
    char buf[VL_IDATASIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtIDataToStr(buf, newval << (VL_IDATASIZE - bits));
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], buf);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitQData(uint32_t code, QData newval, int bits) {
    char buf[VL_QUADSIZE];
    VL_DEBUG_IFDEF(assert(m_symbolp[code]););
    cvtQDataToStr(buf, newval << (VL_QUADSIZE - bits));
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], buf);
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
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], m_strbufp);
}

VL_ATTR_ALWINLINE
void VerilatedFstBuffer::emitDouble(uint32_t code, double newval) {
    m_owner.emitTimeChangeMaybe();
    m_fst->emitValueChange(m_symbolp[code], reinterpret_cast<const uint64_t*>(&newval));
}
