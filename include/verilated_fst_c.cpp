// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2019 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
//=============================================================================
///
/// \file
/// \brief C++ Tracing in FST Format
///
//=============================================================================
// SPDIFF_OFF

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_fst_c.h"

// GTKWave configuration
#ifdef VL_TRACE_THREADED
# define HAVE_LIBPTHREAD
# define FST_WRITER_PARALLEL
#endif

// Include the GTKWave implementation directly
#include "gtkwave/fastlz.c"
#include "gtkwave/fstapi.c"
#include "gtkwave/lz4.c"

#include <algorithm>
#include <cerrno>
#include <ctime>
#include <fcntl.h>
#include <iterator>
#include <sstream>
#include <sys/stat.h>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

//=============================================================================

class VerilatedFstCallInfo {
protected:
    friend class VerilatedFst;
    VerilatedFstCallback_t m_initcb;  ///< Initialization Callback function
    VerilatedFstCallback_t m_fullcb;  ///< Full Dumping Callback function
    VerilatedFstCallback_t m_changecb;  ///< Incremental Dumping Callback function
    void* m_userthis;  ///< Fake "this" for caller
    vluint32_t m_code;  ///< Starting code number
    // CONSTRUCTORS
    VerilatedFstCallInfo(VerilatedFstCallback_t icb, VerilatedFstCallback_t fcb,
                         VerilatedFstCallback_t changecb,
                         void* ut, vluint32_t code)
        : m_initcb(icb), m_fullcb(fcb), m_changecb(changecb), m_userthis(ut), m_code(code) {};
    ~VerilatedFstCallInfo() {}
};

//=============================================================================
// VerilatedFst

VerilatedFst::VerilatedFst(void* fst)
    : m_fst(fst),
      m_fullDump(true),
      m_scopeEscape('.') {}

void VerilatedFst::open(const char* filename) VL_MT_UNSAFE {
    m_assertOne.check();
    m_fst = fstWriterCreate(filename, 1);
    fstWriterSetPackType(m_fst, FST_WR_PT_LZ4);
#ifdef VL_TRACE_THREADED
    fstWriterSetParallelMode(m_fst, 1);
#endif
    m_curScope.clear();

    for (vluint32_t ent = 0; ent< m_callbacks.size(); ++ent) {
        VerilatedFstCallInfo* cip = m_callbacks[ent];
        cip->m_code = 1;
        (cip->m_initcb)(this, cip->m_userthis, cip->m_code);
    }

    // Clear the scope stack
    std::list<std::string>::iterator it = m_curScope.begin();
    while (it != m_curScope.end()) {
        fstWriterSetUpscope(m_fst);
        it = m_curScope.erase(it);
    }
}

void VerilatedFst::module(const std::string& name) {
    m_module = name;
}

//=============================================================================
// Decl

void VerilatedFst::declDTypeEnum(int dtypenum, const char* name, vluint32_t elements,
                                 unsigned int minValbits,
                                 const char** itemNamesp, const char** itemValuesp) {
    fstEnumHandle enumNum = fstWriterCreateEnumTable(m_fst, name, elements,
                                                     minValbits, itemNamesp, itemValuesp);
    m_local2fstdtype[dtypenum] = enumNum;
}

void VerilatedFst::declSymbol(vluint32_t code, const char* name,
                              int dtypenum, fstVarDir vardir, fstVarType vartype,
                              int arraynum, vluint32_t len) {
    std::pair<Code2SymbolType::iterator, bool> p
        = m_code2symbol.insert(std::make_pair(code, static_cast<fstHandle>(NULL)));
    std::istringstream nameiss(name);
    std::istream_iterator<std::string> beg(nameiss), end;
    std::list<std::string> tokens(beg, end);  // Split name
    std::string symbol_name(tokens.back());
    tokens.pop_back();  // Remove symbol name from hierarchy
    tokens.insert(tokens.begin(), m_module);  // Add current module to the hierarchy

    // Find point where current and new scope diverge
    std::list<std::string>::iterator cur_it = m_curScope.begin();
    std::list<std::string>::iterator new_it = tokens.begin();
    while (cur_it != m_curScope.end() && new_it != tokens.end()) {
        if (*cur_it != *new_it)
            break;
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
        fstWriterSetScope(m_fst, FST_ST_VCD_SCOPE, new_it->c_str(), NULL);
        m_curScope.push_back(*new_it);
        new_it = tokens.erase(new_it);
    }

    std::stringstream name_ss;
    name_ss << symbol_name;
    if (arraynum >= 0)
        name_ss << "(" << arraynum << ")";
    std::string name_str = name_ss.str();

    if (dtypenum > 0) {
        fstEnumHandle enumNum = m_local2fstdtype[dtypenum];
        fstWriterEmitEnumTableRef(m_fst, enumNum);
    }
    if (p.second) {  // New
        p.first->second = fstWriterCreateVar(m_fst, vartype, vardir, len, name_str.c_str(), 0);
        assert(p.first->second);
    } else {  // Alias
        fstWriterCreateVar(m_fst, vartype, vardir, len, name_str.c_str(), p.first->second);
    }
}

//=============================================================================
// Callbacks

void VerilatedFst::addCallback(
    VerilatedFstCallback_t initcb, VerilatedFstCallback_t fullcb,
    VerilatedFstCallback_t changecb, void* userthis) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(isOpen())) {
        std::string msg = std::string("Internal: ")+__FILE__+"::"+__FUNCTION__+" called with already open file";
        VL_FATAL_MT(__FILE__,__LINE__,"",msg.c_str());
    }
    VerilatedFstCallInfo* vci = new VerilatedFstCallInfo(initcb, fullcb, changecb, userthis, 1);
    m_callbacks.push_back(vci);
}

//=============================================================================
// Dumping

void VerilatedFst::dump(vluint64_t timeui) {
    if (!isOpen()) return;
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No need for more full dumps
        for (vluint32_t ent = 0; ent< m_callbacks.size(); ++ent) {
            VerilatedFstCallInfo* cip = m_callbacks[ent];
            (cip->m_fullcb)(this, cip->m_userthis, cip->m_code);
        }
        return;
    }
    fstWriterEmitTimeChange(m_fst, timeui);
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ++ent) {
        VerilatedFstCallInfo* cip = m_callbacks[ent];
        (cip->m_changecb)(this, cip->m_userthis, cip->m_code);
    }
}

//=============================================================================
// Helpers

char* VerilatedFst::word2Str(vluint32_t newval, int bits) {
    m_valueStrBuffer.resize(bits+1);
    char* s = m_valueStrBuffer.data();
    for (int i = 0; i < bits; ++i) {
        *s = '0' + ((newval>>(bits-i-1))&1);
        ++s;
    }
    *s = '\0';
    return m_valueStrBuffer.data();
}

char* VerilatedFst::quad2Str(vluint64_t newval, int bits) {
    m_valueStrBuffer.resize(bits+1);
    char* s = m_valueStrBuffer.data();
    for (int i = 0; i < bits; ++i) {
        *s = '0' + ((newval>>(bits-i-1))&1);
        ++s;
    }
    *s = '\0';
    return m_valueStrBuffer.data();
}

char* VerilatedFst::array2Str(const vluint32_t* newval, int bits) {
    int bq = bits/32, br = bits%32;
    m_valueStrBuffer.resize(bits+1);
    char* s = m_valueStrBuffer.data();
    for (int i = 0; i < br; ++i) {
        *s = '0' + ((newval[bq]>>(br-i-1))&1);
        ++s;
    }
    for (int w = bq-1; w >= 0; --w) {
        for (int i = 0; i < 32; ++i) {
            *s = '0' + ((newval[w]>>(32-i-1))&1);
            ++s;
        }
    }
    *s = '\0';
    return m_valueStrBuffer.data();
}

//********************************************************************
// Local Variables:
// End:
