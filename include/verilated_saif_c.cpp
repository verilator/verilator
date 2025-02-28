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
/// \brief Verilated C++ tracing in SAIF format implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use --trace.
///
/// Use "verilator --trace" to add this to the Makefile for the linker.
///
//=============================================================================

// clang-format off

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_saif_c.h"

#include <algorithm>
#include <cerrno>
#include <fcntl.h>
#include <string>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

#ifndef O_LARGEFILE  // WIN32 headers omit this
# define O_LARGEFILE 0
#endif
#ifndef O_NONBLOCK  // WIN32 headers omit this
# define O_NONBLOCK 0
#endif
#ifndef O_CLOEXEC  // WIN32 headers omit this
# define O_CLOEXEC 0
#endif

// clang-format on

//=============================================================================
// Specialization of the generics for this trace format

#define VL_SUB_T VerilatedSaif
#define VL_BUF_T VerilatedSaifBuffer
#include "verilated_trace_imp.h"
#undef VL_SUB_T
#undef VL_BUF_T

//=============================================================================
//=============================================================================
//=============================================================================
// ActivityVar

VL_ATTR_ALWINLINE
void ActivityVar::emitBit(uint64_t time, CData newval) {
    assert(m_lastTime <= time);
    m_bits[0].aggregateVal(time - m_lastTime, newval);
    updateLastTime(time);
}

VL_ATTR_ALWINLINE
void ActivityVar::emitWData(uint64_t time, const WData* newvalp, uint32_t bits) {
    assert(m_lastTime <= time);
    uint64_t dt = time - m_lastTime;
    for (std::size_t i = 0; i < std::min(m_width, bits); ++i) {
        size_t wordIndex = i / VL_EDATASIZE;
        m_bits[i].aggregateVal(dt, (newvalp[wordIndex] >> VL_BITBIT_E(i)) & 1);
    }

    updateLastTime(time);
}

ActivityBit& ActivityVar::getBit(std::size_t index) {
    assert(index < m_width);
    return m_bits[index];
}

//=============================================================================
//=============================================================================
//=============================================================================
// VerilatedSaifFile

bool VerilatedSaifFile::open(const std::string& name) VL_MT_UNSAFE {
    m_fd = ::open(name.c_str(),
                  O_CREAT | O_WRONLY | O_TRUNC | O_LARGEFILE | O_NONBLOCK | O_CLOEXEC, 0666);
    return m_fd >= 0;
}

void VerilatedSaifFile::close() VL_MT_UNSAFE { ::close(m_fd); }

ssize_t VerilatedSaifFile::write(const char* bufp, ssize_t len) VL_MT_UNSAFE {
    return ::write(m_fd, bufp, len);
}

//=============================================================================
//=============================================================================
//=============================================================================
// Opening/Closing

VerilatedSaif::VerilatedSaif(VerilatedSaifFile* filep) {
    // Not in header to avoid link issue if header is included without this .cpp file
    m_fileNewed = (filep == nullptr);
    m_filep = m_fileNewed ? new VerilatedSaifFile : filep;
}

void VerilatedSaif::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    if (isOpen()) return;

    // Set member variables
    m_filename = filename;  // "" is ok, as someone may overload open

    openNextImp(m_rolloverSize != 0);
    if (!isOpen()) return;

    initializeSaifFileContents();

    Super::traceInit();

    // When using rollover, the first chunk contains the header only.
    if (m_rolloverSize) openNextImp(true);
}

void VerilatedSaif::openNext(bool incFilename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    // Open next filename in concat sequence, mangle filename if
    // incFilename is true.
    const VerilatedLockGuard lock{m_mutex};
    openNextImp(incFilename);
}

void VerilatedSaif::openNextImp(bool incFilename) {
    closePrev();  // Close existing
    if (incFilename) {
        // Find _0000.{ext} in filename
        std::string name = m_filename;
        const size_t pos = name.rfind('.');
        if (pos > 8 && 0 == std::strncmp("_cat", name.c_str() + pos - 8, 4)
            && std::isdigit(name.c_str()[pos - 4]) && std::isdigit(name.c_str()[pos - 3])
            && std::isdigit(name.c_str()[pos - 2]) && std::isdigit(name.c_str()[pos - 1])) {
            // Increment code.
            if ((++(name[pos - 1])) > '9') {
                name[pos - 1] = '0';
                if ((++(name[pos - 2])) > '9') {
                    name[pos - 2] = '0';
                    if ((++(name[pos - 3])) > '9') {
                        name[pos - 3] = '0';
                        if ((++(name[pos - 4])) > '9') {  //
                            name[pos - 4] = '0';
                        }
                    }
                }
            }
        } else {
            // Append _cat0000
            name.insert(pos, "_cat0000");
        }
        m_filename = name;
    }
    if (VL_UNCOVERABLE(m_filename[0] == '|')) {
        assert(0);  // LCOV_EXCL_LINE // Not supported yet.
    } else {
        // cppcheck-suppress duplicateExpression
        if (!m_filep->open(m_filename)) {
            // User code can check isOpen()
            m_isOpen = false;
            return;
        }
    }
    m_isOpen = true;
    constDump(true);  // First dump must containt the const signals
    fullDump(true);  // First dump must be full
}

void VerilatedSaif::initializeSaifFileContents() {
    printStr("(SAIFILE\n");
    printStr("(SAIFVERSION \"2.0\")\n");
    printStr("(DIRECTION \"backward\")\n");
    printStr("(DESIGN \"foo\")\n");
    printStr("(PROGRAM_NAME \"Verilator\")\n");
    printStr("(VERSION \"5.032\")\n");
    printStr("(DIVIDER / )\n");
    printStr("(TIMESCALE ");
    printStr(timeResStr().c_str());
    printStr(")\n");
}

bool VerilatedSaif::preChangeDump() {
    if (VL_UNLIKELY(m_rolloverSize)) openNextImp(true);
    return isOpen();
}

void VerilatedSaif::emitTimeChange(uint64_t timeui) { m_time = timeui; }

VerilatedSaif::~VerilatedSaif() {
    close();
    if (m_filep && m_fileNewed) VL_DO_CLEAR(delete m_filep, m_filep = nullptr);
}

void VerilatedSaif::closePrev() {
    // This function is on the flush() call path
    if (!isOpen()) return;

    Super::flushBase();
    m_isOpen = false;
    m_filep->close();
}

void VerilatedSaif::closeErr() {
    // This function is on the flush() call path
    // Close due to an error.  We might abort before even getting here,
    // depending on the definition of vl_fatal.
    if (!isOpen()) return;

    // No buffer flush, just fclose
    m_isOpen = false;
    m_filep->close();  // May get error, just ignore it
}

void VerilatedSaif::close() VL_MT_SAFE_EXCLUDES(m_mutex) {
    // This function is on the flush() call path
    const VerilatedLockGuard lock{m_mutex};
    if (!isOpen()) return;

    finalizeSaifFileContents();
    clearCurrentlyCollectedData();

    closePrev();
    // closePrev() called Super::flush(), so we just
    // need to shut down the tracing thread here.
    Super::closeBase();
}

void VerilatedSaif::finalizeSaifFileContents() {
    printStr("(DURATION ");
    printStr(std::to_string(m_time).c_str());
    printStr(")\n");

    incrementIndent();
    for (int32_t topScopeIndex : m_topScopes) { recursivelyPrintScopes(topScopeIndex); }
    decrementIndent();

    printStr(")\n");  // SAIFILE
}

void VerilatedSaif::recursivelyPrintScopes(uint32_t scopeIndex) {
    const ActivityScope& scope = m_scopes.at(scopeIndex);

    openInstanceScope(scope.getName().c_str());

    printScopeActivities(scope);

    for (uint32_t childScopeIndex : scope.getChildScopesIndices()) {
        recursivelyPrintScopes(childScopeIndex);
    }

    closeInstanceScope();
}

void VerilatedSaif::openInstanceScope(const char* instanceName) {
    printIndent();
    printStr("(INSTANCE ");
    printStr(instanceName);
    printStr("\n");
    incrementIndent();
}

void VerilatedSaif::closeInstanceScope() {
    decrementIndent();
    printIndent();
    printStr(")\n");
}

void VerilatedSaif::printScopeActivities(const ActivityScope& scope) {
    bool anyNetValid{false};
    for (auto& childSignal : scope.getChildActivities()) {
        uint32_t code = childSignal.first;
        const char* name = childSignal.second.c_str();
        anyNetValid = printActivityStats(code, name, anyNetValid);
    }

    if (anyNetValid) { closeNetScope(); }
}

void VerilatedSaif::openNetScope() {
    printIndent();
    printStr("(NET\n");
    incrementIndent();
}

void VerilatedSaif::closeNetScope() {
    decrementIndent();
    printIndent();
    printStr(")\n");
}

bool VerilatedSaif::printActivityStats(uint32_t activityCode, const char* activityName,
                                       bool anyNetValid) {
    ActivityVar& activity = m_activity.at(activityCode);
    for (size_t i = 0; i < activity.getWidth(); i++) {
        ActivityBit& bit = activity.getBit(i);

        if (bit.getToggleCount() <= 0) {
            // Skip bits with no toggles
            continue;
        }

        bit.aggregateVal(m_time - activity.getLastUpdateTime(), bit.getBitValue());

        if (!anyNetValid) {
            openNetScope();
            anyNetValid = true;
        }

        printIndent();
        printStr("(");
        printStr(activityName);
        if (activity.getWidth() > 1) {
            printStr("\\[");
            printStr(std::to_string(i).c_str());
            printStr("\\]");
        }

        // We only have two-value logic so TZ, TX and TB will always be 0
        printStr(" (T0 ");
        printStr(std::to_string(m_time - bit.getHighTime()).c_str());
        printStr(") (T1 ");
        printStr(std::to_string(bit.getHighTime()).c_str());
        printStr(") (TZ 0) (TX 0) (TB 0) (TC ");
        printStr(std::to_string(bit.getToggleCount()).c_str());
        printStr("))\n");
    }

    activity.updateLastTime(m_time);

    return anyNetValid;
}

void VerilatedSaif::clearCurrentlyCollectedData() {
    m_currentScope = -1;
    m_scopes.clear();
    m_topScopes.clear();
    m_activity.clear();
    m_activityArena.clear();
    m_time = 0;
}

void VerilatedSaif::printStr(const char* str) { m_filep->write(str, strlen(str)); }

//=============================================================================
// Definitions

void VerilatedSaif::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
}

void VerilatedSaif::incrementIndent() { m_indent += 1; }

void VerilatedSaif::decrementIndent() { m_indent -= 1; }

void VerilatedSaif::printIndent() {
    for (int i = 0; i < m_indent; ++i) printStr(" ");
}

void VerilatedSaif::pushPrefix(const std::string& name, VerilatedTracePrefixType type) {
    assert(!m_prefixStack.empty());

    std::string pname = name;
    if (pname.empty()) { pname = "$rootio"; }

    if (type != VerilatedTracePrefixType::ARRAY_UNPACKED
        && type != VerilatedTracePrefixType::ARRAY_PACKED) {
        int32_t newScopeIndex = m_scopes.size();
        if (m_currentScope >= 0) {
            m_scopes.at(m_currentScope).addChildScopeIndex(newScopeIndex);
        } else {
            m_topScopes.emplace_back(newScopeIndex);
        }
        m_scopes.emplace_back(lastWord(m_prefixStack.back().first + pname), m_currentScope);
        m_currentScope = newScopeIndex;
    }

    std::string newPrefix = m_prefixStack.back().first + pname;
    if (type != VerilatedTracePrefixType::ARRAY_UNPACKED
        && type != VerilatedTracePrefixType::ARRAY_PACKED) {
        newPrefix += ' ';
    }

    m_prefixStack.emplace_back(newPrefix, type);
}

void VerilatedSaif::popPrefix() {
    assert(m_prefixStack.size() > 1);

    if (m_prefixStack.back().second != VerilatedTracePrefixType::ARRAY_UNPACKED
        && m_prefixStack.back().second != VerilatedTracePrefixType::ARRAY_PACKED) {
        m_currentScope = m_scopes.at(m_currentScope).getParentScopeIndex();
    }

    m_prefixStack.pop_back();
}

void VerilatedSaif::declare(uint32_t code, const char* name, const char* wirep, bool array,
                            int arraynum, bool bussed, int msb, int lsb) {
    const int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;

    std::string hierarchicalName = m_prefixStack.back().first + name;

    if (!Super::declCode(code, hierarchicalName, bits)) { return; }

    const size_t block_size = 1024;
    if (m_activityArena.empty()
        || m_activityArena.back().size() + bits > m_activityArena.back().capacity()) {
        m_activityArena.emplace_back();
        m_activityArena.back().reserve(block_size);
    }
    size_t bitsIdx = m_activityArena.back().size();
    m_activityArena.back().resize(m_activityArena.back().size() + bits);

    std::string finalName = lastWord(hierarchicalName);
    if (array) {
        finalName += '[';
        finalName += std::to_string(arraynum);
        finalName += ']';
    }

    assert(m_currentScope >= 0);
    m_scopes.at(m_currentScope).addActivityVar(code, std::move(finalName));

    m_activity.emplace(
        code, ActivityVar{static_cast<uint32_t>(bits), m_activityArena.back().data() + bitsIdx});
}

void VerilatedSaif::declEvent(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                              VerilatedTraceSigDirection, VerilatedTraceSigKind,
                              VerilatedTraceSigType, bool array, int arraynum) {
    declare(code, name, "event", array, arraynum, false, 0, 0);
}

void VerilatedSaif::declBit(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                            VerilatedTraceSigDirection, VerilatedTraceSigKind,
                            VerilatedTraceSigType, bool array, int arraynum) {
    declare(code, name, "wire", array, arraynum, false, 0, 0);
}
void VerilatedSaif::declBus(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                            VerilatedTraceSigDirection, VerilatedTraceSigKind,
                            VerilatedTraceSigType, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declQuad(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                             VerilatedTraceSigDirection, VerilatedTraceSigKind,
                             VerilatedTraceSigType, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declArray(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                              VerilatedTraceSigDirection, VerilatedTraceSigKind,
                              VerilatedTraceSigType, bool array, int arraynum, int msb, int lsb) {
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declDouble(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                               VerilatedTraceSigDirection, VerilatedTraceSigKind,
                               VerilatedTraceSigType, bool array, int arraynum) {
    declare(code, name, "real", array, arraynum, false, 63, 0);
}

//=============================================================================
// Get/commit trace buffer

VerilatedSaif::Buffer* VerilatedSaif::getTraceBuffer(uint32_t fidx) { return new Buffer{*this}; }

void VerilatedSaif::commitTraceBuffer(VerilatedSaif::Buffer* bufp) { delete bufp; }

//=============================================================================
// VerilatedSaifBuffer implementation

//=============================================================================
// emit* trace routines

// Note: emit* are only ever called from one place (full* in
// verilated_trace_imp.h, which is included in this file at the top),
// so always inline them.

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitEvent(uint32_t code) {
    // Noop
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitBit(uint32_t code, CData newval) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitBit(m_owner.m_time, newval);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitCData(uint32_t code, CData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitData<CData>(m_owner.m_time, newval, bits);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitSData(uint32_t code, SData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitData<SData>(m_owner.m_time, newval, bits);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitIData(uint32_t code, IData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitData<IData>(m_owner.m_time, newval, bits);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitQData(uint32_t code, QData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitData<QData>(m_owner.m_time, newval, bits);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitWData(uint32_t code, const WData* newvalp, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    ActivityVar& activity = m_owner.m_activity.at(code);
    activity.emitWData(m_owner.m_time, newvalp, bits);
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitDouble(uint32_t code, double newval) {
    // Noop
}
