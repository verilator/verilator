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

// This size comes form SAIF allowing use of printable ASCII characters between
// '!' and '~' inclusive, which are a total of 94 different values. Encoding a
// 32 bit code hence needs a maximum of std::ceil(log94(2**32-1)) == 5 bytes.
constexpr unsigned VL_TRACE_MAX_SAIF_CODE_SIZE = 5;  // Maximum length of a SAIF string code

// We use 8 bytes per code in a suffix buffer array.
// 1 byte optional separator + VL_TRACE_MAX_SAIF_CODE_SIZE bytes for code
// + 1 byte '\n' + 1 byte suffix size. This luckily comes out to a power of 2,
// meaning the array can be aligned such that entries never straddle multiple
// cache-lines.
constexpr unsigned VL_TRACE_SUFFIX_ENTRY_SIZE = 8;  // Size of a suffix entry

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
    m_wrChunkSize = 8 * 1024;
    m_wrBufp = new char[m_wrChunkSize * 8];
    m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
    m_writep = m_wrBufp;
}

void VerilatedSaif::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    if (isOpen()) return;

    // Set member variables
    m_filename = filename;  // "" is ok, as someone may overload open

    openNextImp(m_rolloverSize != 0);
    if (!isOpen()) return;

    // NOTE: maybe extract those keywords to some variables to keep them in one place
    printStr("(SAIFILE\n");
    printStr("(SAIFVERSION \"2.0\")\n");
    printStr("(DIRECTION \"backward\")\n");
    printStr("(DESIGN \"foo\")\n");
    //printStr("(DATE \"foo\")\n");
    //printStr("(VENDOR \"foo\")\n");
    printStr("(PROGRAM_NAME \"Verilator\")\n");
    //printStr("(PROGRAM_VERSION \"foo\")\n");
    printStr("(VERSION \"5.032\")\n");
    printStr("(DIVIDER .)\n");
    printStr("(TIMESCALE ");
    printStr(timeResStr().c_str());
    printStr(")\n");

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
    m_wroteBytes = 0;
}

bool VerilatedSaif::preChangeDump() {
    if (VL_UNLIKELY(m_rolloverSize && m_wroteBytes > m_rolloverSize)) openNextImp(true);
    return isOpen();
}

void VerilatedSaif::emitTimeChange(uint64_t timeui) { m_time = timeui; }

VerilatedSaif::~VerilatedSaif() {
    close();
    if (m_wrBufp) VL_DO_CLEAR(delete[] m_wrBufp, m_wrBufp = nullptr);
    if (m_filep && m_fileNewed) VL_DO_CLEAR(delete m_filep, m_filep = nullptr);
    if (parallel()) {
        assert(m_numBuffers == m_freeBuffers.size());
        for (auto& pair : m_freeBuffers) VL_DO_CLEAR(delete[] pair.first, pair.first = nullptr);
    }
}

void VerilatedSaif::closePrev() {
    // This function is on the flush() call path
    if (!isOpen()) return;

    Super::flushBase();
    bufferFlush();
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
    assert(m_time > 0);
    printStr("(DURATION ");
    printStr(std::to_string(m_time).c_str());
    printStr(")\n");

    incrementIndent();
    printInstance(0);
    decrementIndent();
    
    printStr(")\n");  // SAIFILE

    // This function is on the flush() call path
    const VerilatedLockGuard lock{m_mutex};
    if (!isOpen()) return;
    closePrev();
    // closePrev() called Super::flush(), so we just
    // need to shut down the tracing thread here.
    Super::closeBase();
}

void VerilatedSaif::printInstance(uint32_t scopeIndex) {
    const SaifScope& saifScope = m_scopes.at(scopeIndex);

    printIndent();
    printStr("(INSTANCE ");
    printStr(saifScope.scopeName.c_str());
    printStr("\n");

    //NOTE: for now only care about NET, also PORT will be added
    incrementIndent();
    printIndent();
    printStr("(NET\n");

    incrementIndent();
    for (auto& childSignalCode : saifScope.childSignalCodes) {
        ActivityVar& activity = m_activity.at(childSignalCode);
        for (size_t i = 0; i < activity.width; i++) {
            auto& bit = activity.bits[i];
            if (bit.lastVal && activity.lastTime < m_time) {
                bit.highTime += m_time - activity.lastTime;
            }
            if (bit.transitions <= 0) {
                // Skip bits with no transitions
                continue;
            }
            assert(m_time >= bit.highTime);

            printIndent();
            printStr("(");
            printStr(activity.name.c_str());
            if (activity.width > 1) {
                printStr("[");
                printStr(std::to_string(activity.lsb + i).c_str());
                printStr("]");
            }
            printStr(" (T0 ");
            printStr(std::to_string(m_time - bit.highTime).c_str());
            printStr(") (T1 ");
            printStr(std::to_string(bit.highTime).c_str());
            printStr(") (TZ 0) (TX 0) (TB 0) (TC ");
            printStr(std::to_string(bit.transitions).c_str());
            printStr("))\n");

            // NOTE: TZ, TX and TB will be allways 0
            // NOTE: I.3.4 and I.3.5 mentions also about TG, IG and IK
        }
        activity.lastTime = m_time;
    }
    decrementIndent();
    
    printIndent();
    printStr(")\n"); // NET

    for (uint32_t childScopeIndex : saifScope.childScopesIndices) {
        printInstance(childScopeIndex);
    }

    decrementIndent();
    printIndent();
    printStr(")\n"); // INSTANCE
}

void VerilatedSaif::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
    bufferFlush();
}

void VerilatedSaif::printStr(const char* str) { m_filep->write(str, strlen(str)); }

void VerilatedSaif::bufferResize(size_t minsize) {
    // minsize is size of largest write.  We buffer at least 8 times as much data,
    // writing when we are 3/4 full (with thus 2*minsize remaining free)
    if (VL_UNLIKELY(minsize > m_wrChunkSize)) {
        const char* oldbufp = m_wrBufp;
        m_wrChunkSize = roundUpToMultipleOf<1024>(minsize * 2);
        m_wrBufp = new char[m_wrChunkSize * 8];
        std::memcpy(m_wrBufp, oldbufp, m_writep - oldbufp);
        m_writep = m_wrBufp + (m_writep - oldbufp);
        m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
        VL_DO_CLEAR(delete[] oldbufp, oldbufp = nullptr);
    }
}

void VerilatedSaif::bufferFlush() VL_MT_UNSAFE_ONE {
    // This function can be called from the trace offload thread
    // This function is on the flush() call path
    // We add output data to m_writep.
    // When it gets nearly full we dump it using this routine which calls write()
    // This is much faster than using buffered I/O
    if (VL_UNLIKELY(!m_isOpen)) return;
    const char* wp = m_wrBufp;
    while (true) {
        const ssize_t remaining = (m_writep - wp);
        if (remaining == 0) break;
        errno = 0;
        const ssize_t got = m_filep->write(wp, remaining);
        if (got > 0) {
            wp += got;
            m_wroteBytes += got;
        } else if (VL_UNCOVERABLE(got < 0)) {
            if (VL_UNCOVERABLE(errno != EAGAIN && errno != EINTR)) {
                // LCOV_EXCL_START
                // write failed, presume error (perhaps out of disk space)
                const std::string msg = "VerilatedSaif::bufferFlush: "s + std::strerror(errno);
                VL_FATAL_MT("", 0, "", msg.c_str());
                closeErr();
                break;
                // LCOV_EXCL_STOP
            }
        }
    }

    // Reset buffer
    m_writep = m_wrBufp;
}

//=============================================================================
// Definitions

void VerilatedSaif::incrementIndent()
{
    m_indent += 1;
}

void VerilatedSaif::decrementIndent()
{
    m_indent -= 1;
}

void VerilatedSaif::printIndent() {
    for (int i = 0; i < m_indent; ++i) printStr(" ");
}

void VerilatedSaif::pushPrefix(const std::string& name, VerilatedTracePrefixType type) {
    fprintf(stdout, "Pushing prefix: %s\n", name.c_str());
    assert(!m_prefixStack.empty());  // Constructor makes an empty entry
    std::string pname = name;

    int32_t newScopeIndex = m_scopes.size();
    m_scopes.emplace_back();
    SaifScope& newScope = m_scopes.back();
    newScope.scopeName = name;

    if (m_currentScope >= 0) {
        m_scopes.at(m_currentScope).childScopesIndices.emplace_back(newScopeIndex);
        newScope.parentScopeIndex = m_currentScope;
    }
    m_currentScope = newScopeIndex;

    // An empty name means this is the root of a model created with name()=="".  The
    // tools get upset if we try to pass this as empty, so we put the signals under a
    // new scope, but the signals further down will be peers, not children (as usual
    // for name()!="")
    // Terminate earlier $root?
    if (m_prefixStack.back().second == VerilatedTracePrefixType::ROOTIO_MODULE) popPrefix();
    if (pname.empty()) {  // Start new temporary root
        pname = "$rootio";  // SAIF names are not backslash escaped
        m_prefixStack.emplace_back("", VerilatedTracePrefixType::ROOTIO_WRAPPER);
        type = VerilatedTracePrefixType::ROOTIO_MODULE;
    }
    std::string newPrefix = m_prefixStack.back().first + pname;
    switch (type) {
    case VerilatedTracePrefixType::ROOTIO_MODULE:
    case VerilatedTracePrefixType::SCOPE_MODULE:
    case VerilatedTracePrefixType::SCOPE_INTERFACE:
    case VerilatedTracePrefixType::STRUCT_PACKED:
    case VerilatedTracePrefixType::STRUCT_UNPACKED:
    case VerilatedTracePrefixType::UNION_PACKED: {
        newPrefix += ' ';
        break;
    }
    default: break;
    }
    m_prefixStack.emplace_back(newPrefix, type);
}

void VerilatedSaif::popPrefix() {
    assert(!m_prefixStack.empty());
    switch (m_prefixStack.back().second) {
    case VerilatedTracePrefixType::ROOTIO_MODULE:
    case VerilatedTracePrefixType::SCOPE_MODULE:
    case VerilatedTracePrefixType::SCOPE_INTERFACE:
    case VerilatedTracePrefixType::STRUCT_PACKED:
    case VerilatedTracePrefixType::STRUCT_UNPACKED:
    case VerilatedTracePrefixType::UNION_PACKED: break;
    default: break;
    }
    fprintf(stdout, "Popping prefix: %s\n", m_prefixStack.back().first.c_str());
    m_prefixStack.pop_back();
    assert(!m_prefixStack.empty());  // Always one left, the constructor's initial one

    m_currentScope = m_scopes.at(m_currentScope).parentScopeIndex;
}

void VerilatedSaif::declare(uint32_t code, const char* name, const char* wirep, bool array,
                            int arraynum, bool bussed, int msb, int lsb) {
    // check if already declared to avoid duplicates
    if (m_activity.count(code)) {
        return;
    }
    
    const int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;

    std::string hierarchicalName = m_prefixStack.back().first + name;

    const bool enabled = Super::declCode(code, hierarchicalName, bits);
    if (!enabled) return;

    const size_t block_size = 1024;
    if (m_activityArena.empty() || m_activityArena.back().size() + bits > m_activityArena.back().capacity()) {
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
    m_scopes.at(m_currentScope).childSignalCodes.emplace_back(code);

    m_activity.emplace(code, ActivityVar{
        finalName,
        static_cast<uint32_t>(lsb),
        static_cast<uint32_t>(bits),
        m_activityArena.back().data() + bitsIdx
    });
}

void VerilatedSaif::declEvent(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum) {
    fprintf(stdout, "Declaring event - code: %d, fidx: %d, name: %s, \n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
    declare(code, name, "event", array, arraynum, false, 0, 0);
}

void VerilatedSaif::printSignalDirection(VerilatedTraceSigDirection signalDirection)
{
    return;
    switch (signalDirection) {
        case VerilatedTraceSigDirection::INPUT:
        {
            fprintf(stdout, "Signal direction INPUT\n");
            break;
        }
        case VerilatedTraceSigDirection::OUTPUT:
        {
            fprintf(stdout, "Signal direction OUTPUT\n");
            break;
        }
        case VerilatedTraceSigDirection::INOUT:
        {
            fprintf(stdout, "Signal direction INOUT\n");
            break;
        }
        default:
        {
            fprintf(stdout, "Signal direction NONE\n");
            break;
        }
    }
}

void VerilatedSaif::printSignalKind(VerilatedTraceSigKind signalKind)
{
    return;
    switch (signalKind) {
        case VerilatedTraceSigKind::PARAMETER:
        {
            fprintf(stdout, "Signal kind PARAMETER\n");
            break;
        }
        case VerilatedTraceSigKind::SUPPLY0:
        {
            fprintf(stdout, "Signal kind SUPPLY0\n");
            break;
        }
        case VerilatedTraceSigKind::SUPPLY1:
        {
            fprintf(stdout, "Signal kind SUPPLY1\n");
            break;
        }
        case VerilatedTraceSigKind::TRI:
        {
            fprintf(stdout, "Signal kind TRI\n");
            break;
        }
        case VerilatedTraceSigKind::TRI0:
        {
            fprintf(stdout, "Signal kind TRI0\n");
            break;
        }
        case VerilatedTraceSigKind::WIRE:
        {
            fprintf(stdout, "Signal kind WIRE\n");
            break;
        }
        case VerilatedTraceSigKind::VAR:
        {
            fprintf(stdout, "Signal kind VAR\n");
            break;
        }
        default:
        {
            break;
        }
    }
}

void VerilatedSaif::printSignalType(VerilatedTraceSigType signalType)
{
    return;
    switch (signalType) {
        case VerilatedTraceSigType::DOUBLE:
        {
            fprintf(stdout, "Signal type DOUBLE\n");
            break;
        }
        case VerilatedTraceSigType::INTEGER:
        {
            fprintf(stdout, "Signal type INTEGER\n");
            break;
        }
        case VerilatedTraceSigType::BIT:
        {
            fprintf(stdout, "Signal type BIT\n");
            break;
        }
        case VerilatedTraceSigType::LOGIC:
        {
            fprintf(stdout, "Signal type LOGIC\n");
            break;
        }
        case VerilatedTraceSigType::INT:
        {
            fprintf(stdout, "Signal type INT\n");
            break;
        }
        case VerilatedTraceSigType::SHORTINT:
        {
            fprintf(stdout, "Signal type SHORTINT\n");
            break;
        }
        case VerilatedTraceSigType::LONGINT:
        {
            fprintf(stdout, "Signal type LONGINT\n");
            break;
        }
        case VerilatedTraceSigType::BYTE:
        {
            fprintf(stdout, "Signal type BYTE\n");
            break;
        }
        case VerilatedTraceSigType::EVENT:
        {
            fprintf(stdout, "Signal type EVENT\n");
            break;
        }
        case VerilatedTraceSigType::TIME:
        {
            fprintf(stdout, "Signal type TIME\n");
            break;
        }
        default:
        {
            break;
        }
    }
}

void VerilatedSaif::declBit(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum) {
    fprintf(stdout, "Declaring bit - code: %d, fidx: %d, name: %s, dtypenum: %d, array: %d, arraynum: %d\n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
    declare(code, name, "wire", array, arraynum, false, 0, 0);
}
void VerilatedSaif::declBus(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum, int msb, int lsb) {
    fprintf(stdout, "Declaring bus - code: %d, fidx: %d, name: %s, dtypenum: %d, array: %d, arraynum: %d\n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declQuad(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum, int msb, int lsb) {
    fprintf(stdout, "Declaring quad - code: %d, fidx: %d, name: %s, dtypenum: %d, array: %d, arraynum: %d\n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declArray(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum, int msb, int lsb) {
    fprintf(stdout, "Declaring array - code: %d, fidx: %d, name: %s, dtypenum: %d, array: %d, arraynum: %d\n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
    declare(code, name, "wire", array, arraynum, true, msb, lsb);
}
void VerilatedSaif::declDouble(
        uint32_t code, uint32_t fidx, const char* name, int dtypenum, VerilatedTraceSigDirection signalDirection,
        VerilatedTraceSigKind signalKind, VerilatedTraceSigType signalType, bool array, int arraynum) {
    fprintf(stdout, "Declaring double - code: %d, fidx: %d, name: %s, dtypenum: %d, array: %d, arraynum: %d\n", code, fidx, name, dtypenum, array, arraynum);
    printSignalDirection(signalDirection);
    printSignalKind(signalKind);
    printSignalType(signalType);
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
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting bit - name: %s, code: %d, newval: %d, activity.width: %d\n", activity.name.c_str(), code, newval, activity.width);

    auto& bit = activity.bits[0];
    bit.aggregateVal(m_owner.m_time - activity.lastTime, newval);
    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitCData(uint32_t code, CData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting char - name: %s, code: %d, newval: %d, bits: %d, activity.width: %d\n", activity.name.c_str(), code, newval, bits, activity.width);
    
    if (bits > activity.width) {
        fprintf(stdout, "Trying to emit more bits than activity width\n");
    }

    auto dt = m_owner.m_time - activity.lastTime;
    for (size_t i = 0; i < activity.width; i++) {
        activity.bits[i].aggregateVal(dt, (newval >> i) & 1);
    }
    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitSData(uint32_t code, SData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting short - name: %s, code: %d, newval: %d, bits: %d, activity.width: %d\n", activity.name.c_str(), code, newval, bits, activity.width);
    
    if (bits > activity.width) {
        fprintf(stdout, "Trying to emit more bits than activity width\n");
    }

    auto dt = m_owner.m_time - activity.lastTime;
    for (size_t i = 0; i < activity.width; i++) {
        activity.bits[i].aggregateVal(dt, (newval >> i) & 1);
    }
    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitIData(uint32_t code, IData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting integer - name: %s, code: %d, newval: %d, bits: %d, activity.width: %d\n", activity.name.c_str(), code, newval, bits, activity.width);
    
    if (bits > activity.width) {
        fprintf(stdout, "Trying to emit more bits than activity width\n");
    }
    
    auto dt = m_owner.m_time - activity.lastTime;
    for (size_t i = 0; i < activity.width; i++) {
        activity.bits[i].aggregateVal(dt, (newval >> i) & 1);
    }
    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitQData(uint32_t code, QData newval, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting quad - name: %s, code: %d, newval: %d, bits: %d, activity.width: %d\n", activity.name.c_str(), code, newval, bits, activity.width);
    
    if (bits > activity.width) {
        fprintf(stdout, "Trying to emit more bits than activity width\n");
    }

    auto dt = m_owner.m_time - activity.lastTime;
    for (size_t i = 0; i < activity.width; i++) {
        activity.bits[i].aggregateVal(dt, (newval >> i) & 1);
    }
    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitWData(uint32_t code, const WData* newvalp, int bits) {
    assert(m_owner.m_activity.count(code) && "Activity must be declared earlier");
    auto& activity = m_owner.m_activity.at(code);

    fprintf(stdout, "Emitting words - name: %s, code: %d, bits: %d, activity.width: %d\n", activity.name.c_str(), code, bits, activity.width);
    
    if (bits > activity.width) {
        fprintf(stdout, "Trying to emit more bits than activity width\n");
    }

    auto dt = m_owner.m_time - activity.lastTime;

    for (std::size_t i = 0; i < activity.width; ++i) {
        size_t wordIndex = i / VL_EDATASIZE;
        activity.bits[i].aggregateVal(dt, (newvalp[wordIndex] >> VL_BITBIT_E(i)) & 1);
    }

    activity.lastTime = m_owner.m_time;
}

VL_ATTR_ALWINLINE
void VerilatedSaifBuffer::emitDouble(uint32_t code, double newval) {
    // Noop
}
