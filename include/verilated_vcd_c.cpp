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
/// \brief C++ Tracing in VCD Format
///
//=============================================================================
// SPDIFF_OFF

// clang-format off

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <algorithm>
#include <cerrno>
#include <ctime>
#include <fcntl.h>
#include <sys/stat.h>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

// SPDIFF_ON

#ifndef O_LARGEFILE  // For example on WIN32
# define O_LARGEFILE 0
#endif
#ifndef O_NONBLOCK
# define O_NONBLOCK 0
#endif
#ifndef O_CLOEXEC
# define O_CLOEXEC 0
#endif

// This size comes form VCD allowing use of printable ASCII characters between
// '!' and '~' inclusive, which are a total of 94 different values. Encoding a
// 32 bit code hence needs a maximum of ceil(log94(2**32-1)) == 5 bytes.
#define VL_TRACE_MAX_VCD_CODE_SIZE 5  ///< Maximum length of a VCD string code
// We use 8 bytes per code in a suffix buffer array.
// 1 byte optional separator + VL_TRACE_MAX_VCD_CODE_SIZE bytes for code
// + 1 byte '\n' + 1 byte suffix size. This luckily comes out to a power of 2,
// meaning the array can be aligned such that entries never straddle multiple
// cache-lines.
#define VL_TRACE_SUFFIX_ENTRY_SIZE 8  ///< Size of a suffix entry

// clang-format on

//=============================================================================
// VerilatedVcdImp
/// Base class to hold some static state
/// This is an internally used class

class VerilatedVcdSingleton {
private:
    typedef std::vector<VerilatedVcd*> VcdVec;
    struct Singleton {
        VerilatedMutex s_vcdMutex;  ///< Protect the singleton
        VcdVec s_vcdVecp VL_GUARDED_BY(s_vcdMutex);  ///< List of all created traces
    };
    static Singleton& singleton() {
        static Singleton s;
        return s;
    }

public:
    static void pushVcd(VerilatedVcd* vcdp) VL_EXCLUDES(singleton().s_vcdMutex) {
        VerilatedLockGuard lock(singleton().s_vcdMutex);
        singleton().s_vcdVecp.push_back(vcdp);
    }
    static void removeVcd(const VerilatedVcd* vcdp) VL_EXCLUDES(singleton().s_vcdMutex) {
        VerilatedLockGuard lock(singleton().s_vcdMutex);
        VcdVec::iterator pos
            = find(singleton().s_vcdVecp.begin(), singleton().s_vcdVecp.end(), vcdp);
        if (pos != singleton().s_vcdVecp.end()) { singleton().s_vcdVecp.erase(pos); }
    }
    static void flush_all() VL_EXCLUDES(singleton().s_vcdMutex) VL_MT_UNSAFE_ONE {
        // Thread safety: Although this function is protected by a mutex so
        // perhaps in the future we can allow tracing in separate threads,
        // vcdp->flush() assumes call from single thread
        VerilatedLockGuard lock(singleton().s_vcdMutex);
        for (VcdVec::const_iterator it = singleton().s_vcdVecp.begin();
             it != singleton().s_vcdVecp.end(); ++it) {
            VerilatedVcd* vcdp = *it;
            vcdp->flush();
        }
    }
};

//=============================================================================
// VerilatedVcdCallInfo
/// Internal callback routines for each module being traced.
////
/// Each module that wishes to be traced registers a set of
/// callbacks stored in this class.  When the trace file is being
/// constructed, this class provides the callback routines to be executed.

class VerilatedVcdCallInfo {
protected:
    friend class VerilatedVcd;
    VerilatedVcdCallback_t m_initcb;  ///< Initialization Callback function
    VerilatedVcdCallback_t m_fullcb;  ///< Full Dumping Callback function
    VerilatedVcdCallback_t m_changecb;  ///< Incremental Dumping Callback function
    void* m_userthis;  ///< Fake "this" for caller
    vluint32_t m_code;  ///< Starting code number (set later by traceInit)
    // CONSTRUCTORS
    VerilatedVcdCallInfo(VerilatedVcdCallback_t icb, VerilatedVcdCallback_t fcb,
                         VerilatedVcdCallback_t changecb, void* ut)
        : m_initcb(icb)
        , m_fullcb(fcb)
        , m_changecb(changecb)
        , m_userthis(ut)
        , m_code(1) {}
    ~VerilatedVcdCallInfo() {}
};

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

VerilatedVcd::VerilatedVcd(VerilatedVcdFile* filep)
    : m_isOpen(false)
    , m_rolloverMB(0)
    , m_modDepth(0)
    , m_nextCode(1) {
    // Not in header to avoid link issue if header is included without this .cpp file
    m_fileNewed = (filep == NULL);
    m_filep = m_fileNewed ? new VerilatedVcdFile : filep;
    m_namemapp = NULL;
    m_timeRes = m_timeUnit = 1e-9;
    m_timeLastDump = 0;
    m_sigs_oldvalp = NULL;
    m_evcd = false;
    m_scopeEscape = '.';  // Backward compatibility
    m_fullDump = true;
    m_wrChunkSize = 8 * 1024;
    m_wrBufp = new char[m_wrChunkSize * 8];
    m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
    m_writep = m_wrBufp;
    m_wroteBytes = 0;
}

void VerilatedVcd::open(const char* filename) {
    m_assertOne.check();
    if (isOpen()) return;

    // Set member variables
    m_filename = filename;  // "" is ok, as someone may overload open
    VerilatedVcdSingleton::pushVcd(this);

    // SPDIFF_OFF
    // Set callback so an early exit will flush us
    Verilated::flushCb(&flush_all);

    // SPDIFF_ON
    openNext(m_rolloverMB != 0);
    if (!isOpen()) return;

    dumpHeader();

    // Allocate space now we know the number of codes
    if (!m_sigs_oldvalp) m_sigs_oldvalp = new vluint32_t[m_nextCode + 10];

    // Get the direct access pointer to the code strings
    m_suffixesp = &m_suffixes[0];  // Note: C++11 m_suffixes.data();

    if (m_rolloverMB) {
        openNext(true);
        if (!isOpen()) return;
    }
}

void VerilatedVcd::openNext(bool incFilename) {
    // Open next filename in concat sequence, mangle filename if
    // incFilename is true.
    m_assertOne.check();
    closePrev();  // Close existing
    if (incFilename) {
        // Find _0000.{ext} in filename
        std::string name = m_filename;
        size_t pos = name.rfind('.');
        if (pos > 8 && 0 == strncmp("_cat", name.c_str() + pos - 8, 4)
            && isdigit(name.c_str()[pos - 4]) && isdigit(name.c_str()[pos - 3])
            && isdigit(name.c_str()[pos - 2]) && isdigit(name.c_str()[pos - 1])) {
            // Increment code.
            if ((++(name[pos - 1])) > '9') {
                name[pos - 1] = '0';
                if ((++(name[pos - 2])) > '9') {
                    name[pos - 2] = '0';
                    if ((++(name[pos - 3])) > '9') {
                        name[pos - 3] = '0';
                        if ((++(name[pos - 4])) > '9') { name[pos - 4] = '0'; }
                    }
                }
            }
        } else {
            // Append _cat0000
            name.insert(pos, "_cat0000");
        }
        m_filename = name;
    }
    if (m_filename[0] == '|') {
        assert(0);  // Not supported yet.
    } else {
        // cppcheck-suppress duplicateExpression
        if (!m_filep->open(m_filename)) {
            // User code can check isOpen()
            m_isOpen = false;
            return;
        }
    }
    m_isOpen = true;
    m_fullDump = true;  // First dump must be full
    m_wroteBytes = 0;
}

void VerilatedVcd::makeNameMap() {
    // Take signal information from each module and build m_namemapp
    deleteNameMap();
    m_nextCode = 1;
    m_namemapp = new NameMap;
    for (vluint32_t ent = 0; ent < m_callbacks.size(); ent++) {
        VerilatedVcdCallInfo* cip = m_callbacks[ent];
        cip->m_code = m_nextCode;
        // Initialize; callbacks will call decl* which update m_nextCode
        (cip->m_initcb)(this, cip->m_userthis, cip->m_code);
    }

    // Though not speced, it's illegal to generate a vcd with signals
    // not under any module - it crashes at least two viewers.
    // If no scope was specified, prefix everything with a "top"
    // This comes from user instantiations with no name - IE Vtop("").
    bool nullScope = false;
    for (NameMap::const_iterator it = m_namemapp->begin(); it != m_namemapp->end(); ++it) {
        const std::string& hiername = it->first;
        if (!hiername.empty() && hiername[0] == '\t') nullScope = true;
    }
    if (nullScope) {
        NameMap* newmapp = new NameMap;
        for (NameMap::const_iterator it = m_namemapp->begin(); it != m_namemapp->end(); ++it) {
            const std::string& hiername = it->first;
            const std::string& decl = it->second;
            std::string newname = std::string("top");
            if (hiername[0] != '\t') newname += ' ';
            newname += hiername;
            newmapp->insert(std::make_pair(newname, decl));
        }
        deleteNameMap();
        m_namemapp = newmapp;
    }
}

void VerilatedVcd::deleteNameMap() {
    if (m_namemapp) VL_DO_CLEAR(delete m_namemapp, m_namemapp = NULL);
}

VerilatedVcd::~VerilatedVcd() {
    close();
    if (m_wrBufp) VL_DO_CLEAR(delete[] m_wrBufp, m_wrBufp = NULL);
    if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = NULL);
    deleteNameMap();
    if (m_filep && m_fileNewed) VL_DO_CLEAR(delete m_filep, m_filep = NULL);
    for (CallbackVec::const_iterator it = m_callbacks.begin(); it != m_callbacks.end(); ++it) {
        delete *it;
    }
    m_callbacks.clear();
    VerilatedVcdSingleton::removeVcd(this);
}

void VerilatedVcd::closePrev() {
    // This function is on the flush() call path
    if (!isOpen()) return;

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

void VerilatedVcd::close() {
    // This function is on the flush() call path
    m_assertOne.check();
    if (!isOpen()) return;
    if (m_evcd) {
        printStr("$vcdclose ");
        printTime(m_timeLastDump);
        printStr(" $end\n");
    }
    closePrev();
}

void VerilatedVcd::printStr(const char* str) {
    // Not fast...
    while (*str) {
        *m_writep++ = *str++;
        bufferCheck();
    }
}

void VerilatedVcd::printQuad(vluint64_t n) {
    char buf[100];
    sprintf(buf, "%" VL_PRI64 "u", n);
    printStr(buf);
}

void VerilatedVcd::printTime(vluint64_t timeui) {
    // VCD file format specification does not allow non-integers for timestamps
    // Dinotrace doesn't mind, but Cadence Vision seems to choke
    if (VL_UNLIKELY(timeui < m_timeLastDump)) {
        timeui = m_timeLastDump;
        static VL_THREAD_LOCAL bool backTime = false;
        if (!backTime) {
            backTime = true;
            VL_PRINTF_MT("%%Warning: VCD time is moving backwards, wave file may be incorrect.\n");
        }
    }
    m_timeLastDump = timeui;
    printQuad(timeui);
}

void VerilatedVcd::bufferResize(vluint64_t minsize) {
    // minsize is size of largest write.  We buffer at least 8 times as much data,
    // writing when we are 3/4 full (with thus 2*minsize remaining free)
    if (VL_UNLIKELY(minsize > m_wrChunkSize)) {
        char* oldbufp = m_wrBufp;
        m_wrChunkSize = minsize * 2;
        m_wrBufp = new char[m_wrChunkSize * 8];
        memcpy(m_wrBufp, oldbufp, m_writep - oldbufp);
        m_writep = m_wrBufp + (m_writep - oldbufp);
        m_wrFlushp = m_wrBufp + m_wrChunkSize * 6;
        VL_DO_CLEAR(delete[] oldbufp, oldbufp = NULL);
    }
}

void VerilatedVcd::bufferFlush() VL_MT_UNSAFE_ONE {
    // This function is on the flush() call path
    // We add output data to m_writep.
    // When it gets nearly full we dump it using this routine which calls write()
    // This is much faster than using buffered I/O
    m_assertOne.check();
    if (VL_UNLIKELY(!isOpen())) return;
    char* wp = m_wrBufp;
    while (true) {
        ssize_t remaining = (m_writep - wp);
        if (remaining == 0) break;
        errno = 0;
        ssize_t got = m_filep->write(wp, remaining);
        if (got > 0) {
            wp += got;
            m_wroteBytes += got;
        } else if (got < 0) {
            if (errno != EAGAIN && errno != EINTR) {
                // write failed, presume error (perhaps out of disk space)
                std::string msg = std::string("VerilatedVcd::bufferFlush: ") + strerror(errno);
                VL_FATAL_MT("", 0, "", msg.c_str());
                closeErr();
                break;
            }
        }
    }

    // Reset buffer
    m_writep = m_wrBufp;
}

//=============================================================================
// Simple methods

void VerilatedVcd::set_time_unit(const char* unitp) {
    // cout<<" set_time_unit("<<unitp<<") == "<<timescaleToDouble(unitp)
    //    <<" == "<<doubleToTimescale(timescaleToDouble(unitp))<<endl;
    m_timeUnit = timescaleToDouble(unitp);
}

void VerilatedVcd::set_time_resolution(const char* unitp) {
    // cout<<"set_time_resolution("<<unitp<<") == "<<timescaleToDouble(unitp)
    //    <<" == "<<doubleToTimescale(timescaleToDouble(unitp))<<endl;
    m_timeRes = timescaleToDouble(unitp);
}

double VerilatedVcd::timescaleToDouble(const char* unitp) {
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

std::string VerilatedVcd::doubleToTimescale(double value) {
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
// VCD string code

char* VerilatedVcd::writeCode(char* writep, vluint32_t code) {
    *writep++ = static_cast<char>('!' + code % 94);
    code /= 94;
    while (code) {
        code--;
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
    for (int i = 0; i < m_modDepth; i++) {
        printStr(" ");
    }
    if (level_change > 0) m_modDepth += level_change;
}

void VerilatedVcd::dumpHeader() {
    printStr("$version Generated by VerilatedVcd $end\n");
    time_t time_str = time(NULL);
    printStr("$date ");
    printStr(ctime(&time_str));
    printStr(" $end\n");

    printStr("$timescale ");
    const std::string& timeResStr = doubleToTimescale(m_timeRes);
    printStr(timeResStr.c_str());
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
    for (NameMap::const_iterator it = m_namemapp->begin(); it != m_namemapp->end(); ++it) {
        const std::string& hiernamestr = it->first;
        const std::string& decl = it->second;

        // Determine difference between the old and new names
        const char* hiername = hiernamestr.c_str();
        const char* lp = lastName;
        const char* np = hiername;
        lastName = hiername;

        // Skip common prefix, it must break at a space or tab
        for (; *np && (*np == *lp); np++, lp++) {}
        while (np != hiername && *np && *np != ' ' && *np != '\t') {
            np--;
            lp--;
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
            printStr("$scope module ");
            for (; *np && *np != ' ' && *np != '\t'; np++) {
                if (*np == '[') {
                    printStr("(");
                } else if (*np == ']') {
                    printStr(")");
                } else {
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

void VerilatedVcd::module(const std::string& name) {
    m_assertOne.check();
    m_modName = name;
}

void VerilatedVcd::declare(vluint32_t code, const char* name, const char* wirep, bool array,
                           int arraynum, bool tri, bool bussed, int msb, int lsb) {
    if (!code) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Internal: internal trace problem, code 0 is illegal");
    }

    int bits = ((msb > lsb) ? (msb - lsb) : (lsb - msb)) + 1;
    int codesNeeded = 1 + int(bits / 32);
    if (tri) codesNeeded *= 2;  // Space in change array for __en signals

    // Make sure array is large enough
    m_nextCode = std::max(m_nextCode, code + codesNeeded);
    if (m_sigs.capacity() <= m_nextCode) {
        m_sigs.reserve(m_nextCode * 2);  // Power-of-2 allocation speeds things up
    }
    if (m_suffixes.size() <= m_nextCode * VL_TRACE_SUFFIX_ENTRY_SIZE) {
        m_suffixes.resize(m_nextCode * VL_TRACE_SUFFIX_ENTRY_SIZE * 2, 0);
    }

    // Make sure write buffer is large enough (one character per bit), plus header
    bufferResize(bits + 1024);

    // Save declaration info
    VerilatedVcdSig sig = VerilatedVcdSig(code, bits);
    m_sigs.push_back(sig);

    // Split name into basename
    // Spaces and tabs aren't legal in VCD signal names, so:
    // Space separates each level of scope
    // Tab separates final scope from signal name
    // Tab sorts before spaces, so signals nicely will print before scopes
    // Note the hiername may be nothing, if so we'll add "\t{name}"
    std::string nameasstr = name;
    if (!m_modName.empty()) {
        nameasstr = m_modName + m_scopeEscape + nameasstr;  // Optional ->module prefix
    }
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
    if (m_evcd) {
        decl += "port";
    } else {
        decl += wirep;  // usually "wire"
    }

    char buf[1000];
    sprintf(buf, " %2d ", bits);
    decl += buf;
    if (m_evcd) {
        sprintf(buf, "<%u", code);
        decl += buf;
    } else {
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
        std::strcpy(entryp + !isBit, buf);  // Code (overwrite separator if isBit)
        entryp[length + !isBit] = '\n';  // Replace '\0' with line termination '\n'
        // Set length of suffix (used to increment write pointer)
        entryp[VL_TRACE_SUFFIX_ENTRY_SIZE - 1] = !isBit + length + 1;
    }
    decl += " ";
    decl += basename;
    if (array) {
        sprintf(buf, "(%d)", arraynum);
        decl += buf;
        hiername += buf;
    }
    if (bussed) {
        sprintf(buf, " [%d:%d]", msb, lsb);
        decl += buf;
    }
    decl += " $end\n";
    m_namemapp->insert(std::make_pair(hiername, decl));
}

void VerilatedVcd::declBit(vluint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "wire", array, arraynum, false, false, 0, 0);
}
void VerilatedVcd::declBus(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                           int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declQuad(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                            int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declArray(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                             int lsb) {
    declare(code, name, "wire", array, arraynum, false, true, msb, lsb);
}
void VerilatedVcd::declFloat(vluint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "real", array, arraynum, false, false, 31, 0);
}
void VerilatedVcd::declDouble(vluint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "real", array, arraynum, false, false, 63, 0);
}
#ifndef VL_TRACE_VCD_OLD_API
void VerilatedVcd::declTriBit(vluint32_t code, const char* name, bool array, int arraynum) {
    declare(code, name, "wire", array, arraynum, true, false, 0, 0);
}
void VerilatedVcd::declTriBus(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                              int lsb) {
    declare(code, name, "wire", array, arraynum, true, true, msb, lsb);
}
void VerilatedVcd::declTriQuad(vluint32_t code, const char* name, bool array, int arraynum,
                               int msb, int lsb) {
    declare(code, name, "wire", array, arraynum, true, true, msb, lsb);
}
void VerilatedVcd::declTriArray(vluint32_t code, const char* name, bool array, int arraynum,
                                int msb, int lsb) {
    declare(code, name, "wire", array, arraynum, true, true, msb, lsb);
}
#endif  //  VL_TRACE_VCD_OLD_API

//=============================================================================
// Trace recording routines

#ifndef VL_TRACE_VCD_OLD_API

//=============================================================================
// Pointer based variants used by Verilator

// Emit suffix, write back write pointer, check buffer
void VerilatedVcd::finishLine(vluint32_t* oldp, char* writep) {
    const vluint32_t code = oldp - m_sigs_oldvalp;
    const char* const suffixp = m_suffixesp + code * VL_TRACE_SUFFIX_ENTRY_SIZE;
    // Copy the whole suffix (this avoid having hard to predict branches which
    // helps a lot). Note suffixp could be aligned, so could load it in one go,
    // but then we would be endiannes dependent which we don't have a way to
    // test right now and probably would make little difference...
    // Note: The maximum length of the suffix is
    // VL_TRACE_MAX_VCD_CODE_SIZE + 2 == 7, but we unroll this here for speed.
    writep[0] = suffixp[0];
    writep[1] = suffixp[1];
    writep[2] = suffixp[2];
    writep[3] = suffixp[3];
    writep[4] = suffixp[4];
    writep[5] = suffixp[5];
    writep[6] = '\n';  // The 6th index is always '\n' if it's relevant, no need to fetch it.
    // Now write back the write pointer incremented by the actual size of the
    // suffix, which was stored in the last byte of the suffix buffer entry.
    m_writep = writep + suffixp[VL_TRACE_SUFFIX_ENTRY_SIZE - 1];
    bufferCheck();
}

void VerilatedVcd::fullBit(vluint32_t* oldp, vluint32_t newval) {
    *oldp = newval;
    char* wp = m_writep;
    *wp++ = '0' | static_cast<char>(newval);
    finishLine(oldp, wp);
}

// We do want these functions specialized for sizes to avoid hard to predict
// branches, but we don't want them inlined, so we explicitly create one
// specialization for each size used here here.

// T_Bits is the number of used bits in the value
template <int T_Bits> void VerilatedVcd::fullBus(vluint32_t* oldp, vluint32_t newval) {
    *oldp = newval;
    char* wp = m_writep;
    *wp++ = 'b';
    newval <<= 32 - T_Bits;
    int bits = T_Bits;
    do {
        *wp++ = '0' | static_cast<char>(newval >> 31);
        newval <<= 1;
    } while (--bits);
    finishLine(oldp, wp);
}
// Note: No specialization for width 1, covered by 'fullBit'
template void VerilatedVcd::fullBus<2>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<3>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<4>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<5>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<6>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<7>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<8>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<9>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<10>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<11>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<12>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<13>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<14>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<15>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<16>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<17>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<18>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<19>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<20>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<21>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<22>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<23>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<24>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<25>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<26>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<27>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<28>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<29>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<30>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<31>(vluint32_t* oldp, vluint32_t newval);
template void VerilatedVcd::fullBus<32>(vluint32_t* oldp, vluint32_t newval);

// T_Bits is the number of used bits in the value
void VerilatedVcd::fullQuad(vluint32_t* oldp, vluint64_t newval, int bits) {
    *reinterpret_cast<vluint64_t*>(oldp) = newval;
    char* wp = m_writep;
    *wp++ = 'b';
    newval <<= 64 - bits;
    // Handle the top 32 bits within the 64 bit input
    const int bitsInTopHalf = bits - 32;
    wp += bitsInTopHalf;
    // clang-format off
    switch (bitsInTopHalf) {
    case 32: wp[-32] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 31: wp[-31] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 30: wp[-30] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 29: wp[-29] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 28: wp[-28] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 27: wp[-27] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 26: wp[-26] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 25: wp[-25] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 24: wp[-24] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 23: wp[-23] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 22: wp[-22] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 21: wp[-21] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 20: wp[-20] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 19: wp[-19] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 18: wp[-18] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 17: wp[-17] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 16: wp[-16] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 15: wp[-15] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 14: wp[-14] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 13: wp[-13] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 12: wp[-12] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 11: wp[-11] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 10: wp[-10] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 9:  wp[ -9] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 8:  wp[ -8] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 7:  wp[ -7] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 6:  wp[ -6] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 5:  wp[ -5] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 4:  wp[ -4] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 3:  wp[ -3] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 2:  wp[ -2] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    case 1:  wp[ -1] = '0' | static_cast<char>(newval >> 63); newval<<=1; //FALLTHRU
    }
    // clang-format on
    // Handle the bottom 32 bits within the 64 bit input
    int remaining = 32;
    do {
        *wp++ = '0' | static_cast<char>(newval >> 63);
        newval <<= 1;
    } while (--remaining);
    finishLine(oldp, wp);
}

void VerilatedVcd::fullArray(vluint32_t* oldp, const vluint32_t* newvalp, int bits) {
    int words = (bits + 31) / 32;
    for (int i = 0; i < words; ++i) {
        oldp[i] = newvalp[i];
    }
    char* wp = m_writep;
    *wp++ = 'b';
    // Handle the most significant word
    const int bitsInMSW = bits % 32 == 0 ? 32 : bits % 32;
    vluint32_t val = newvalp[--words] << (32 - bitsInMSW);
    wp += bitsInMSW;
    // clang-format off
    switch (bitsInMSW) {
    case 32: wp[-32] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 31: wp[-31] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 30: wp[-30] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 29: wp[-29] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 28: wp[-28] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 27: wp[-27] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 26: wp[-26] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 25: wp[-25] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 24: wp[-24] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 23: wp[-23] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 22: wp[-22] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 21: wp[-21] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 20: wp[-20] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 19: wp[-19] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 18: wp[-18] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 17: wp[-17] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 16: wp[-16] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 15: wp[-15] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 14: wp[-14] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 13: wp[-13] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 12: wp[-12] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 11: wp[-11] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 10: wp[-10] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 9:  wp[ -9] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 8:  wp[ -8] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 7:  wp[ -7] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 6:  wp[ -6] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 5:  wp[ -5] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 4:  wp[ -4] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 3:  wp[ -3] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 2:  wp[ -2] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    case 1:  wp[ -1] = '0' | static_cast<char>(val >> 31); val<<=1; //FALLTHRU
    }
    // clang-format on
    // Handle the remaining words
    while (words > 0) {
        vluint32_t val = newvalp[--words];
        int bits = 32;
        do {
            *wp++ = '0' | static_cast<char>(val >> 31);
            val <<= 1;
        } while (--bits);
    }
    finishLine(oldp, wp);
}

void VerilatedVcd::fullFloat(vluint32_t* oldp, float newval) {
    // cppcheck-suppress invalidPointerCast
    *reinterpret_cast<float*>(oldp) = newval;
    char* wp = m_writep;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(wp, "r%.16g", static_cast<double>(newval));
    wp += strlen(wp);
    finishLine(oldp, wp);
}

void VerilatedVcd::fullDouble(vluint32_t* oldp, double newval) {
    // cppcheck-suppress invalidPointerCast
    *reinterpret_cast<double*>(oldp) = newval;
    char* wp = m_writep;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(wp, "r%.16g", newval);
    wp += strlen(wp);
    finishLine(oldp, wp);
}

#else  // VL_TRACE_VCD_OLD_API

void VerilatedVcd::fullBit(vluint32_t code, const vluint32_t newval) {
    // Note the &1, so we don't require clean input -- makes more common no change case faster
    m_sigs_oldvalp[code] = newval;
    *m_writep++ = ('0' + static_cast<char>(newval & 1));
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullBus(vluint32_t code, const vluint32_t newval, int bits) {
    m_sigs_oldvalp[code] = newval;
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = ((newval & (1L << bit)) ? '1' : '0');
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullQuad(vluint32_t code, const vluint64_t newval, int bits) {
    (*(reinterpret_cast<vluint64_t*>(&m_sigs_oldvalp[code]))) = newval;
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = ((newval & (VL_ULL(1) << bit)) ? '1' : '0');
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullArray(vluint32_t code, const vluint32_t* newval, int bits) {
    for (int word = 0; word < (((bits - 1) / 32) + 1); ++word) {
        m_sigs_oldvalp[code + word] = newval[word];
    }
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = ((newval[(bit / 32)] & (1L << (bit & 0x1f))) ? '1' : '0');
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullArray(vluint32_t code, const vluint64_t* newval, int bits) {
    for (int word = 0; word < (((bits - 1) / 64) + 1); ++word) {
        m_sigs_oldvalp[code + word] = newval[word];
    }
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = ((newval[(bit / 64)] & (VL_ULL(1) << (bit & 0x3f))) ? '1' : '0');
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullTriBit(vluint32_t code, const vluint32_t newval, const vluint32_t newtri) {
    m_sigs_oldvalp[code] = newval;
    m_sigs_oldvalp[code + 1] = newtri;
    *m_writep++ = "01zz"[m_sigs_oldvalp[code] | (m_sigs_oldvalp[code + 1] << 1)];
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullTriBus(vluint32_t code, const vluint32_t newval, const vluint32_t newtri,
                              int bits) {
    m_sigs_oldvalp[code] = newval;
    m_sigs_oldvalp[code + 1] = newtri;
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = "01zz"[((newval >> bit) & 1) | (((newtri >> bit) & 1) << 1)];
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullTriQuad(vluint32_t code, const vluint64_t newval, const vluint32_t newtri,
                               int bits) {
    (*(reinterpret_cast<vluint64_t*>(&m_sigs_oldvalp[code]))) = newval;
    (*(reinterpret_cast<vluint64_t*>(&m_sigs_oldvalp[code + 1]))) = newtri;
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++
            = "01zz"[((newval >> bit) & VL_ULL(1)) | (((newtri >> bit) & VL_ULL(1)) << VL_ULL(1))];
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullTriArray(vluint32_t code, const vluint32_t* newvalp,
                                const vluint32_t* newtrip, int bits) {
    for (int word = 0; word < (((bits - 1) / 32) + 1); ++word) {
        m_sigs_oldvalp[code + word * 2] = newvalp[word];
        m_sigs_oldvalp[code + word * 2 + 1] = newtrip[word];
    }
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        vluint32_t valbit = (newvalp[(bit / 32)] >> (bit & 0x1f)) & 1;
        vluint32_t tribit = (newtrip[(bit / 32)] >> (bit & 0x1f)) & 1;
        *m_writep++ = "01zz"[valbit | (tribit << 1)];
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullDouble(vluint32_t code, const double newval) {
    // cppcheck-suppress invalidPointerCast
    (*(reinterpret_cast<double*>(&m_sigs_oldvalp[code]))) = newval;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(m_writep, "r%.16g", newval);
    m_writep += strlen(m_writep);
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullFloat(vluint32_t code, const float newval) {
    // cppcheck-suppress invalidPointerCast
    (*(reinterpret_cast<float*>(&m_sigs_oldvalp[code]))) = newval;
    // Buffer can't overflow before sprintf; we sized during declaration
    sprintf(m_writep, "r%.16g", static_cast<double>(newval));
    m_writep += strlen(m_writep);
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullBitX(vluint32_t code) {
    *m_writep++ = 'x';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullBusX(vluint32_t code, int bits) {
    *m_writep++ = 'b';
    for (int bit = bits - 1; bit >= 0; --bit) {
        *m_writep++ = 'x';
    }
    *m_writep++ = ' ';
    m_writep = writeCode(m_writep, code);
    *m_writep++ = '\n';
    bufferCheck();
}
void VerilatedVcd::fullQuadX(vluint32_t code, int bits) { fullBusX(code, bits); }
void VerilatedVcd::fullArrayX(vluint32_t code, int bits) { fullBusX(code, bits); }

#endif  // VL_TRACE_VCD_OLD_API

//=============================================================================
// Callbacks

void VerilatedVcd::addCallback(VerilatedVcdCallback_t initcb, VerilatedVcdCallback_t fullcb,
                               VerilatedVcdCallback_t changecb, void* userthis) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(isOpen())) {
        std::string msg = std::string("Internal: ") + __FILE__ + "::" + __FUNCTION__
                          + " called with already open file";
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
    }
    VerilatedVcdCallInfo* cip = new VerilatedVcdCallInfo(initcb, fullcb, changecb, userthis);
    m_callbacks.push_back(cip);
}

//=============================================================================
// Dumping

void VerilatedVcd::dumpFull(vluint64_t timeui) {
    m_assertOne.check();
    dumpPrep(timeui);
    Verilated::quiesce();
    for (vluint32_t ent = 0; ent < m_callbacks.size(); ent++) {
        VerilatedVcdCallInfo* cip = m_callbacks[ent];
        (cip->m_fullcb)(this, cip->m_userthis, cip->m_code);
    }
}

void VerilatedVcd::dump(vluint64_t timeui) {
    m_assertOne.check();
    if (!isOpen()) return;
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No more need for next dump to be full
        dumpFull(timeui);
        return;
    }
    if (VL_UNLIKELY(m_rolloverMB && m_wroteBytes > this->m_rolloverMB)) {
        openNext(true);
        if (!isOpen()) return;
    }
    dumpPrep(timeui);
    Verilated::quiesce();
    for (vluint32_t ent = 0; ent < m_callbacks.size(); ++ent) {
        VerilatedVcdCallInfo* cip = m_callbacks[ent];
        (cip->m_changecb)(this, cip->m_userthis, cip->m_code);
    }
}

void VerilatedVcd::dumpPrep(vluint64_t timeui) {
    printStr("#");
    printTime(timeui);
    printStr("\n");
}

//======================================================================
// Static members

void VerilatedVcd::flush_all() VL_MT_UNSAFE_ONE { VerilatedVcdSingleton::flush_all(); }

//======================================================================
//======================================================================
//======================================================================

// clang-format off

#ifdef VERILATED_VCD_TEST
#include <iostream>

vluint32_t v1, v2, s1, s2[3];
vluint32_t tri96[3];
vluint32_t tri96__tri[3];
vluint64_t quad96[2];
vluint8_t ch;
vluint64_t timestamp = 1;
double doub = 0;

void vcdInit(VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->scopeEscape('.');
    vcdp->module("top");
     vcdp->declBus(0x2, "v1",-1,5,1);
     vcdp->declBus(0x3, "v2",-1,6,0);
     vcdp->module("top.sub1");
      vcdp->declBit(0x4, "s1",-1);
      vcdp->declBit(0x5, "ch",-1);
     vcdp->module("top.sub2");
      vcdp->declArray(0x6, "s2",-1, 40,3);
    // Note need to add 3 for next code.
    vcdp->module("top2");
     vcdp->declBus(0x2, "t2v1",-1,4,1);
     vcdp->declTriBit(0x10, "io1",-1);
     vcdp->declTriBus(0x12, "io5",-1,4,0);
     vcdp->declTriArray(0x16, "io96",-1,95,0);
    // Note need to add 6 for next code.
     vcdp->declDouble(0x1c, "doub",-1);
    // Note need to add 2 for next code.
     vcdp->declArray(0x1e, "q2",-1,95,0);
    // Note need to add 4 for next code.
}

void vcdFull(VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->fullBus(0x2, v1, 5);
    vcdp->fullBus(0x3, v2, 7);
    vcdp->fullBit(0x4, s1);
    vcdp->fullBus(0x5, ch, 2);
    vcdp->fullArray(0x6, &s2[0], 38);
    vcdp->fullTriBit(0x10, tri96[0] & 1, tri96__tri[0] & 1);
    vcdp->fullTriBus(0x12, tri96[0] & 0x1f, tri96__tri[0] & 0x1f, 5);
    vcdp->fullTriArray(0x16, tri96, tri96__tri, 96);
    vcdp->fullDouble(0x1c, doub);
    vcdp->fullArray(0x1e, &quad96[0], 96);
}

void vcdChange(VerilatedVcd* vcdp, void* userthis, vluint32_t code) {
    vcdp->chgBus(0x2, v1, 5);
    vcdp->chgBus(0x3, v2, 7);
    vcdp->chgBit(0x4, s1);
    vcdp->chgBus(0x5, ch, 2);
    vcdp->chgArray(0x6, &s2[0], 38);
    vcdp->chgTriBit(0x10, tri96[0] & 1, tri96__tri[0] & 1);
    vcdp->chgTriBus(0x12, tri96[0] & 0x1f, tri96__tri[0] & 0x1f, 5);
    vcdp->chgTriArray(0x16, tri96, tri96__tri, 96);
    vcdp->chgDouble(0x1c, doub);
    vcdp->chgArray(0x1e, &quad96[0], 96);
}

main() {
    std::cout << "test: O_LARGEFILE=" << O_LARGEFILE << std::endl;

    v1 = v2 = s1 = 0;
    s2[0] = s2[1] = s2[2] = 0;
    tri96[2] = tri96[1] = tri96[0] = 0;
    tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = ~0;
    quad96[1] = quad96[0] = 0;
    ch = 0;
    doub = 0;
    {
        VerilatedVcdC* vcdp = new VerilatedVcdC;
        vcdp->spTrace()->addCallback(&vcdInit, &vcdFull, &vcdChange, 0);
        vcdp->open("test.vcd");
        // Dumping
        vcdp->dump(timestamp++);
        v1 = 0xfff;
        tri96[2] = 4; tri96[1] = 2; tri96[0] = 1;
        tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = ~0;  // Still tri
        quad96[1] = 0xffffffff; quad96[0] = 0;
        doub = 1.5;
        vcdp->dump(timestamp++);
        v2 = 0x1;
        s2[1] = 2;
        tri96__tri[2] = tri96__tri[1] = tri96__tri[0] = 0;  // enable w/o data change
        quad96[1] = 0; quad96[0] = ~0;
        doub = -1.66e13;
        vcdp->dump(timestamp++);
        ch = 2;
        tri96[2] = ~4; tri96[1] = ~2; tri96[0] = ~1;
        doub = -3.33e-13;
        vcdp->dump(timestamp++);
        vcdp->dump(timestamp++);
# ifdef VERILATED_VCD_TEST_64BIT
        vluint64_t bytesPerDump = VL_ULL(15);
        for (vluint64_t i = 0; i < ((VL_ULL(1) << 32) / bytesPerDump); i++) {
            v1 = i;
            vcdp->dump(timestamp++);
        }
# endif
        vcdp->close();
    }
}
#endif

//********************************************************************
// ;compile-command: "mkdir -p ../test_dir && cd ../test_dir && c++ -DVERILATED_VCD_TEST ../include/verilated_vcd_c.cpp -o verilated_vcd_c && ./verilated_vcd_c && cat test.vcd"
//
// Local Variables:
// End:
