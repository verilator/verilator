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
/// \brief Verilated C++ tracing in VCD format implementation code
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
#include "verilated_vcd_c.h"

#include <algorithm>
#include <cerrno>
#include <ctime>
#include <fcntl.h>

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

// This size comes form VCD allowing use of printable ASCII characters between
// '!' and '~' inclusive, which are a total of 94 different values. Encoding a
// 32 bit code hence needs a maximum of std::ceil(log94(2**32-1)) == 5 bytes.
constexpr unsigned VL_TRACE_MAX_VCD_CODE_SIZE = 5;  // Maximum length of a VCD string code

// We use 8 bytes per code in a suffix buffer array.
// 1 byte optional separator + VL_TRACE_MAX_VCD_CODE_SIZE bytes for code
// + 1 byte '\n' + 1 byte suffix size. This luckily comes out to a power of 2,
// meaning the array can be aligned such that entries never straddle multiple
// cache-lines.
constexpr unsigned VL_TRACE_SUFFIX_ENTRY_SIZE = 8;  // Size of a suffix entry

//=============================================================================
// Utility functions: TODO: put these in a common place and share them.

template <size_t N>
static size_t roundUpToMultipleOf(size_t value) {
    static_assert((N & (N - 1)) == 0, "'N' must be a power of 2");
    size_t mask = N - 1;
    return (value + mask) & ~mask;
}

//=============================================================================
// Specialization of the generics for this trace format

#define VL_SUB_T VerilatedVcd
#define VL_BUF_T VerilatedVcdBuffer
#include "verilated_trace_imp.h"
#undef VL_SUB_T
#undef VL_BUF_T

//=============================================================================
//=============================================================================
//=============================================================================
// VerilatedVcdFile

bool VerilatedVcdFile::open(const std::string& name) VL_MT_UNSAFE {
    m_fd = ::open(name.c_str(),
                  O_CREAT | O_WRONLY | O_TRUNC | O_LARGEFILE | O_NONBLOCK | O_CLOEXEC, 0666);
    return m_fd >= 0;
}

void VerilatedVcdFile::close() VL_MT_UNSAFE { ::close(m_fd); }

ssize_t VerilatedVcdFile::write(const char* bufp, ssize_t len) VL_MT_UNSAFE {
    return ::write(m_fd, bufp, len);
}

//=============================================================================
//=============================================================================
//=============================================================================
// Opening/Closing

VerilatedVcd::VerilatedVcd(VerilatedVcdFile* filep) {
    // Not in header to avoid link issue if header is included without this .cpp file
    m_fileNewed = (filep == nullptr);
    m_filep = m_fileNewed ? new VerilatedVcdFile : filep;
    m_wrChunkSize = 8 * 1024;
    m_wrBufp = new char[m_wrChunkSize * 8];
    m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
    m_writep = m_wrBufp;
}

void VerilatedVcd::open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    if (isOpen()) return;

    // Set member variables
    m_filename = filename;  // "" is ok, as someone may overload open

    openNextImp(m_rolloverSize != 0);
    if (!isOpen()) return;

    dumpHeader();

    // When using rollover, the first chunk contains the header only.
    if (m_rolloverSize) openNextImp(true);
}

void VerilatedVcd::openNext(bool incFilename) VL_MT_SAFE_EXCLUDES(m_mutex) {
    // Open next filename in concat sequence, mangle filename if
    // incFilename is true.
    const VerilatedLockGuard lock{m_mutex};
    openNextImp(incFilename);
}

void VerilatedVcd::openNextImp(bool incFilename) {
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
    fullDump(true);  // First dump must be full
    m_wroteBytes = 0;
}

bool VerilatedVcd::preChangeDump() {
    if (VL_UNLIKELY(m_rolloverSize && m_wroteBytes > m_rolloverSize)) openNextImp(true);
    return isOpen();
}

void VerilatedVcd::emitTimeChange(uint64_t timeui) {
    printStr("#");
    printQuad(timeui);
    printStr("\n");
}

void VerilatedVcd::makeNameMap() {
    // Take signal information from each module and build m_namemapp
    deleteNameMap();
    m_namemapp = new NameMap;

    Super::traceInit();

    // Though not speced, it's illegal to generate a vcd with signals
    // not under any module - it crashes at least two viewers.
    // If no scope was specified, prefix everything with a "top"
    // This comes from user instantiations with no name - IE Vtop("").
    bool nullScope = false;
    for (const auto& i : *m_namemapp) {
        const std::string& hiername = i.first;
        if (!hiername.empty() && hiername[0] == '\t') nullScope = true;
    }
    if (nullScope) {
        NameMap* const newmapp = new NameMap;
        for (const auto& i : *m_namemapp) {
            const std::string& hiername = i.first;
            const std::string& decl = i.second;
            std::string newname{"top"};
            if (hiername[0] != '\t') newname += ' ';
            newname += hiername;
            newmapp->emplace(newname, decl);
        }
        deleteNameMap();
        m_namemapp = newmapp;
    }
}

void VerilatedVcd::deleteNameMap() {
    if (m_namemapp) VL_DO_CLEAR(delete m_namemapp, m_namemapp = nullptr);
}

VerilatedVcd::~VerilatedVcd() {
    close();
    if (m_wrBufp) VL_DO_CLEAR(delete[] m_wrBufp, m_wrBufp = nullptr);
    deleteNameMap();
    if (m_filep && m_fileNewed) VL_DO_CLEAR(delete m_filep, m_filep = nullptr);
#ifdef VL_THREADED
    if (parallel()) {
        assert(m_numBuffers == m_freeBuffers.size());
        for (auto& pair : m_freeBuffers) VL_DO_CLEAR(delete[] pair.first, pair.first = nullptr);
    }
#endif
}

void VerilatedVcd::closePrev() {
    // This function is on the flush() call path
    if (!isOpen()) return;

    Super::flushBase();
    bufferFlush();
    m_isOpen = false;
    m_filep->close();
}

void VerilatedVcd::closeErr() {
    // This function is on the flush() call path
    // Close due to an error.  We might abort before even getting here,
    // depending on the definition of vl_fatal.
    if (!isOpen()) return;

    // No buffer flush, just fclose
    m_isOpen = false;
    m_filep->close();  // May get error, just ignore it
}

void VerilatedVcd::close() VL_MT_SAFE_EXCLUDES(m_mutex) {
    // This function is on the flush() call path
    const VerilatedLockGuard lock{m_mutex};
    if (!isOpen()) return;
    closePrev();
    // closePrev() called Super::flush(), so we just
    // need to shut down the tracing thread here.
    Super::closeBase();
}

void VerilatedVcd::flush() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    Super::flushBase();
    bufferFlush();
}

void VerilatedVcd::printStr(const char* str) {
    // Not fast...
    while (*str) {
        *m_writep++ = *str++;
        bufferCheck();
    }
}

void VerilatedVcd::printQuad(uint64_t n) {
    constexpr size_t LEN_STR_QUAD = 40;
    char buf[LEN_STR_QUAD];
    VL_SNPRINTF(buf, LEN_STR_QUAD, "%" PRIu64, n);
    printStr(buf);
}

void VerilatedVcd::bufferResize(size_t minsize) {
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

void VerilatedVcd::bufferFlush() VL_MT_UNSAFE_ONE {
    // This function can be called from the trace offload thread
    // This function is on the flush() call path
    // We add output data to m_writep.
    // When it gets nearly full we dump it using this routine which calls write()
    // This is much faster than using buffered I/O
    if (VL_UNLIKELY(!isOpen())) return;
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
                const std::string msg
                    = std::string{"VerilatedVcd::bufferFlush: "} + std::strerror(errno);
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
// VCD string code

char* VerilatedVcd::writeCode(char* writep, uint32_t code) {
    *writep++ = static_cast<char>('!' + code % 94);
    code /= 94;
    while (code) {
        --code;
        *writep++ = static_cast<char>('!' + code % 94);
        code /= 94;
    }
    return writep;
}

//=============================================================================
// Definitions

void VerilatedVcd::printIndent(int level_change) {
    if (level_change < 0) m_modDepth += level_change;
    assert(m_modDepth >= 0);
    for (int i = 0; i < m_modDepth; i++) printStr(" ");
    if (level_change > 0) m_modDepth += level_change;
}

void VerilatedVcd::dumpHeader() {
    printStr("$version Generated by VerilatedVcd $end\n");
    printStr("$date ");
    {
        const time_t tick = time(nullptr);
        tm ticktm;
        VL_LOCALTIME_R(&tick, &ticktm);
        constexpr size_t LEN_BUF = 50;
        char buf[LEN_BUF];
        std::strftime(buf, LEN_BUF, "%c", &ticktm);
        printStr(buf);
    }
    printStr(" $end\n");

    printStr("$timescale ");
    printStr(timeResStr().c_str());  // lintok-begin-on-ref
    printStr(" $end\n");

    makeNameMap();

    // Signal header
    assert(m_modDepth == 0);
    printIndent(1);
    printStr("\n");

    // We detect the spaces in module names to determine hierarchy.  This
    // allows signals to be declared without fixed ordering, which is
    // required as Verilog signals might be separately declared from
    // SC module signals.

    // Print the signal names
    const char* lastName = "";
    for (const auto& i : *m_namemapp) {
        const std::string& hiernamestr = i.first;
        const std::string& decl = i.second;

        // Determine difference between the old and new names
        const char* const hiername = hiernamestr.c_str();
        const char* lp = lastName;
        const char* np = hiername;
        lastName = hiername;

        // Skip common prefix, it must break at a space or tab
        for (; *np && (*np == *lp); np++, lp++) {}
        while (np != hiername && *np && *np != ' ' && *np != '\t') {
            --np;
            --lp;
        }
        // printf("hier %s\n  lp=%s\n  np=%s\n",hiername,lp,np);

        // Any extra spaces in last name are scope ups we need to do
        bool first = true;
        for (; *lp; lp++) {
            if (*lp == ' ' || (first && *lp != '\t')) {
                printIndent(-1);
                printStr("$upscope $end\n");
            }
            first = false;
        }

        // Any new spaces are scope downs we need to do
        while (*np) {
            if (*np == ' ') np++;
            if (*np == '\t') break;  // tab means signal name starts
            printIndent(1);
            // Find character after name end
            const char* sp = np;
            while (*sp && *sp != ' ' && *sp != '\t' && !(*sp & '\x80')) sp++;

            printStr("$scope ");
            if (*sp & '\x80') {
                switch (*sp & 0x7f) {
                case VLT_TRACE_SCOPE_STRUCT: printStr("struct "); break;
                case VLT_TRACE_SCOPE_INTERFACE: printStr("interface "); break;
                case VLT_TRACE_SCOPE_UNION: printStr("union "); break;
                default: printStr("module ");
                }
            } else {
                printStr("module ");
            }

            for (; *np && *np != ' ' && *np != '\t'; np++) {
                if (*np == '[') {
                    printStr("[");
                } else if (*np == ']') {
                    printStr("]");
                } else if (!(*np & '\x80')) {
                    *m_writep++ = *np;
                }
            }
            printStr(" $end\n");
        }

        printIndent(0);
        printStr(decl.c_str());
    }

    while (m_modDepth > 1) {
        printIndent(-1);
        printStr("$upscope $end\n");
    }

    printIndent(-1);
    printStr("$enddefinitions $end\n\n\n");
    assert(m_modDepth == 0);

    // Reclaim storage
    deleteNameMap();
}

void VerilatedVcd::declare(uint32_t code, const char* name, const char* wirep, bool array,
                           int arraynum, bool tri, bool bussed, int msb, int lsb) {
    const int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;

    const bool enabled = Super::declCode(code, name, bits, tri);

    if (m_suffixes.size() <= nextCode() * VL_TRACE_SUFFIX_ENTRY_SIZE) {
        m_suffixes.resize(nextCode() * VL_TRACE_SUFFIX_ENTRY_SIZE * 2, 0);
    }

    // Keep upper bound on bytes a single signal cna emit into the buffer
    m_maxSignalBytes = std::max<size_t>(m_maxSignalBytes, bits + 32);
    // Make sure write buffer is large enough, plus header
    bufferResize(m_maxSignalBytes + 1024);

    if (!enabled) return;

    // Split name into basename
    // Spaces and tabs aren't legal in VCD signal names, so:
    // Space separates each level of scope
    // Tab separates final scope from signal name
    // Tab sorts before spaces, so signals nicely will print before scopes
    // Note the hiername may be nothing, if so we'll add "\t{name}"
    std::string nameasstr = namePrefix() + name;
    std::string hiername;
    std::string basename;
    for (const char* cp = nameasstr.c_str(); *cp; cp++) {
        if (isScopeEscape(*cp)) {
            // Ahh, we've just read a scope, not a basename
            if (!hiername.empty()) hiername += " ";
            hiername += basename;
            basename = "";
        } else {
            basename += *cp;
        }
    }
    hiername += "\t" + basename;

    // Print reference
    std::string decl = "$var ";
    decl += wirep;  // usually "wire"

    constexpr size_t bufsize = 1000;
    char buf[bufsize];
    VL_SNPRINTF(buf, bufsize, " %2d ", bits);
    decl += buf;
    // Add string code to decl
    char* const endp = writeCode(buf, code);
    *endp = '\0';
    decl += buf;
    // Build suffix array entry
    char* const entryp = &m_suffixes[code * VL_TRACE_SUFFIX_ENTRY_SIZE];
    const size_t length = endp - buf;
    assert(length <= VL_TRACE_MAX_VCD_CODE_SIZE);
    // 1 bit values don't have a ' ' separator between value and string code
    const bool isBit = bits == 1;
    entryp[0] = ' ';  // Separator
    // Use memcpy as we checked size above, and strcpy is flagged unsafe
    std::memcpy(entryp + !isBit, buf,
                std::strlen(buf));  // Code (overwrite separator if isBit)
    entryp[length + !isBit] = '\n';  // Replace '\0' with line termination '\n'
    // Set length of suffix (used to increment write pointer)
    entryp[VL_TRACE_SUFFIX_ENTRY_SIZE - 1] = !isBit + length + 1;
    decl += " ";
    decl += basename;
    if (array) {
        VL_SNPRINTF(buf, bufsize, "[%d]", arraynum);
        decl += buf;
        hiername += buf;
    }
    if (bussed) {
        VL_SNPRINTF(buf, bufsize, " [%d:%d]", msb, lsb);
        decl += buf;
    }
    decl += " $end\n";
    m_namemapp->emplace(hiername, decl);
}

void VerilatedVcd::declBit(uint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "wire", array, arraynum, false, false, 0, 0);
}
void VerilatedVcd::declBus(uint32_t code, const char* name, bool array, int arraynum, int msb,
                           int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declQuad(uint32_t code, const char* name, bool array, int arraynum, int msb,
                            int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declArray(uint32_t code, const char* name, bool array, int arraynum, int msb,
                             int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declDouble(uint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "real", array, arraynum, false, false, 63, 0);
}

//=============================================================================
// Get/commit trace buffer

VerilatedVcd::Buffer* VerilatedVcd::getTraceBuffer() {
    VerilatedVcd::Buffer* const bufp = new Buffer{*this};
#ifdef VL_THREADED
    if (parallel()) {
        // Note: This is called from VeriltedVcd::dump, which already holds the lock
        // If no buffer available, allocate a new one
        if (m_freeBuffers.empty()) {
            constexpr size_t pageSize = 4096;
            // 4 * m_maxSignalBytes, so we can reserve 2 * m_maxSignalBytes at the end for safety
            size_t startingSize = roundUpToMultipleOf<pageSize>(4 * m_maxSignalBytes);
            m_freeBuffers.emplace_back(new char[startingSize], startingSize);
            ++m_numBuffers;
        }
        // Grab a buffer
        const auto pair = m_freeBuffers.back();
        m_freeBuffers.pop_back();
        // Initialize
        bufp->m_writep = bufp->m_bufp = pair.first;
        bufp->m_size = pair.second;
        bufp->adjustGrowp();
    }
#endif
    // Return the buffer
    return bufp;
}

void VerilatedVcd::commitTraceBuffer(VerilatedVcd::Buffer* bufp) {
    if (parallel()) {
#if VL_THREADED
        // Note: This is called from VeriltedVcd::dump, which already holds the lock
        // Resize output buffer. Note, we use the full size of the trace buffer, as
        // this is a lot more stable than the actual occupancy of the trace buffer.
        // This helps us to avoid re-allocations due to small size changes.
        bufferResize(bufp->m_size);
        // Compute occupancy of buffer
        const size_t usedSize = bufp->m_writep - bufp->m_bufp;
        // Copy to output buffer
        std::memcpy(m_writep, bufp->m_bufp, usedSize);
        // Adjust write pointer
        m_writep += usedSize;
        // Flush if necessary
        bufferCheck();
        // Put buffer back on free list
        m_freeBuffers.emplace_back(bufp->m_bufp, bufp->m_size);
#else
        VL_FATAL_MT(__FILE__, __LINE__, "", "Unreachable");
#endif
    } else {
        // Needs adjusting for emitTimeChange
        m_writep = bufp->m_writep;
    }
    delete bufp;
}

//=============================================================================
// VerilatedVcdBuffer implementation

//=============================================================================
// Trace rendering primitives

static inline void
VerilatedVcdCCopyAndAppendNewLine(char* writep, const char* suffixp) VL_ATTR_NO_SANITIZE_ALIGN;

static inline void VerilatedVcdCCopyAndAppendNewLine(char* writep, const char* suffixp) {
    // Copy the whole suffix (this avoid having hard to predict branches which
    // helps a lot). Note: The maximum length of the suffix is
    // VL_TRACE_MAX_VCD_CODE_SIZE + 2 == 7, but we unroll this here for speed.
#ifdef VL_X86_64
    // Copy the whole 8 bytes in one go, this works on little-endian machines
    // supporting unaligned stores.
    *reinterpret_cast<uint64_t*>(writep) = *reinterpret_cast<const uint64_t*>(suffixp);
#else
    // Portable variant
    writep[0] = suffixp[0];
    writep[1] = suffixp[1];
    writep[2] = suffixp[2];
    writep[3] = suffixp[3];
    writep[4] = suffixp[4];
    writep[5] = suffixp[5];
    writep[6] = '\n';  // The 6th index is always '\n' if it's relevant, no need to fetch it.
#endif
}

void VerilatedVcdBuffer::finishLine(uint32_t code, char* writep) {
    const char* const suffixp = m_suffixes + code * VL_TRACE_SUFFIX_ENTRY_SIZE;
    VL_DEBUG_IFDEF(assert(suffixp[0]););
    VerilatedVcdCCopyAndAppendNewLine(writep, suffixp);

    // Now write back the write pointer incremented by the actual size of the
    // suffix, which was stored in the last byte of the suffix buffer entry.
    m_writep = writep + suffixp[VL_TRACE_SUFFIX_ENTRY_SIZE - 1];

    if (m_owner.parallel()) {
#ifdef VL_THREADED
        // Double the size of the buffer if necessary
        if (VL_UNLIKELY(m_writep >= m_growp)) {
            // Compute occupied size of current buffer
            const size_t usedSize = m_writep - m_bufp;
            // We are always doubling the size
            m_size *= 2;
            // Allocate the new buffer
            char* const newBufp = new char[m_size];
            // Copy from current buffer to new buffer
            std::memcpy(newBufp, m_bufp, usedSize);
            // Delete current buffer
            delete[] m_bufp;
            // Make new buffer the current buffer
            m_bufp = newBufp;
            // Adjust write pointer
            m_writep = m_bufp + usedSize;
            // Adjust resize limit
            adjustGrowp();
        }
#else
        VL_FATAL_MT(__FILE__, __LINE__, "", "Unreachable");
#endif
    } else {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY(m_writep > m_wrFlushp)) {
            m_owner.m_writep = m_writep;
            m_owner.bufferFlush();
            m_writep = m_owner.m_writep;
        }
    }
}

//=============================================================================
// emit* trace routines

// Note: emit* are only ever called from one place (full* in
// verilated_trace_imp.h, which is included in this file at the top),
// so always inline them.

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitBit(uint32_t code, CData newval) {
    // Don't prefetch suffix as it's a bit too late;
    char* wp = m_writep;
    *wp++ = '0' | static_cast<char>(newval);
    finishLine(code, wp);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitCData(uint32_t code, CData newval, int bits) {
    char* wp = m_writep;
    *wp++ = 'b';
    cvtCDataToStr(wp, newval << (VL_BYTESIZE - bits));
    finishLine(code, wp + bits);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitSData(uint32_t code, SData newval, int bits) {
    char* wp = m_writep;
    *wp++ = 'b';
    cvtSDataToStr(wp, newval << (VL_SHORTSIZE - bits));
    finishLine(code, wp + bits);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitIData(uint32_t code, IData newval, int bits) {
    char* wp = m_writep;
    *wp++ = 'b';
    cvtIDataToStr(wp, newval << (VL_IDATASIZE - bits));
    finishLine(code, wp + bits);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitQData(uint32_t code, QData newval, int bits) {
    char* wp = m_writep;
    *wp++ = 'b';
    cvtQDataToStr(wp, newval << (VL_QUADSIZE - bits));
    finishLine(code, wp + bits);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitWData(uint32_t code, const WData* newvalp, int bits) {
    int words = VL_WORDS_I(bits);
    char* wp = m_writep;
    *wp++ = 'b';
    // Handle the most significant word
    const int bitsInMSW = VL_BITBIT_E(bits) ? VL_BITBIT_E(bits) : VL_EDATASIZE;
    cvtEDataToStr(wp, newvalp[--words] << (VL_EDATASIZE - bitsInMSW));
    wp += bitsInMSW;
    // Handle the remaining words
    while (words > 0) {
        cvtEDataToStr(wp, newvalp[--words]);
        wp += VL_EDATASIZE;
    }
    finishLine(code, wp);
}

VL_ATTR_ALWINLINE
void VerilatedVcdBuffer::emitDouble(uint32_t code, double newval) {
    char* wp = m_writep;
    // Buffer can't overflow before VL_SNPRINTF; we sized during declaration
    VL_SNPRINTF(wp, m_maxSignalBytes, "r%.16g", newval);
    wp += std::strlen(wp);
    finishLine(code, wp);
}
