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
/// \brief C++ Tracing in FST Format
///
//=============================================================================
// SPDIFF_OFF

#define __STDC_LIMIT_MACROS  // UINT64_MAX
#include "verilatedos.h"
#include "verilated.h"
#include "verilated_fst_c.h"

// GTKWave configuration
#ifdef VL_TRACE_THREADED
# define HAVE_LIBPTHREAD
# define FST_WRITER_PARALLEL
#endif

// Include the GTKWave implementation directly
#define FST_CONFIG_INCLUDE "fst_config.h"
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
# include <stdint.h>
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
                         VerilatedFstCallback_t changecb, void* ut)
        : m_initcb(icb)
        , m_fullcb(fcb)
        , m_changecb(changecb)
        , m_userthis(ut)
        , m_code(1) {}
    ~VerilatedFstCallInfo() {}
};

//=============================================================================
// VerilatedFst

VerilatedFst::VerilatedFst(void* fst)
    : m_fst(fst)
    , m_fullDump(true)
    , m_nextCode(1)
    , m_scopeEscape('.') {
    m_valueStrBuffer.reserve(64 + 1);  // Need enough room for quad
}

void VerilatedFst::open(const char* filename) VL_MT_UNSAFE {
    m_assertOne.check();
    m_fst = fstWriterCreate(filename, 1);
    fstWriterSetPackType(m_fst, FST_WR_PT_LZ4);
#ifdef VL_TRACE_THREADED
    fstWriterSetParallelMode(m_fst, 1);
#endif
    m_curScope.clear();
    m_nextCode = 1;

    for (vluint32_t ent = 0; ent< m_callbacks.size(); ++ent) {
        VerilatedFstCallInfo* cip = m_callbacks[ent];
        cip->m_code = m_nextCode;
        // Initialize; callbacks will call decl* which update m_nextCode
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

void VerilatedFst::declSymbol(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                              fstVarType vartype, bool array, int arraynum, vluint32_t len,
                              vluint32_t bits) {

    // Make sure deduplicate tracking increments for future declarations
    int codesNeeded = 1 + int(bits / 32);
    //Not supported: if (tri) codesNeeded *= 2;  // Space in change array for __en signals
    m_nextCode = std::max(m_nextCode, code + codesNeeded);

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
    if (array) name_ss << "(" << arraynum << ")";
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

void VerilatedFst::addCallback(VerilatedFstCallback_t initcb, VerilatedFstCallback_t fullcb,
                               VerilatedFstCallback_t changecb, void* userthis) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(isOpen())) {
        std::string msg = (std::string("Internal: ") + __FILE__ + "::" + __FUNCTION__
                           + " called with already open file");
        VL_FATAL_MT(__FILE__, __LINE__, "", msg.c_str());
    }
    VerilatedFstCallInfo* cip = new VerilatedFstCallInfo(initcb, fullcb, changecb, userthis);
    m_callbacks.push_back(cip);
}

//=============================================================================
// Dumping

void VerilatedFst::dump(vluint64_t timeui) {
    if (!isOpen()) return;
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No more need for next dump to be full
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

//********************************************************************
// Local Variables:
// End:
