// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2018 by Wilson Snyder.  This program is free software;
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
/// \brief C++ Tracing in LXT2 Format
///
//=============================================================================
// SPDIFF_OFF

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_lxt2_c.h"
// Include the GTKWave implementation directly
#include "lxt2/lxt2_write.cpp"

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <cerrno>
#include <ctime>
#include <algorithm>
#include <sstream>

#if defined(_WIN32) && !defined(__MINGW32__) && !defined(__CYGWIN__)
# include <io.h>
#else
# include <unistd.h>
#endif

//=============================================================================

class VerilatedLxt2CallInfo {
protected:
    friend class VerilatedLxt2;
    VerilatedLxt2Callback_t m_initcb;  ///< Initialization Callback function
    VerilatedLxt2Callback_t m_fullcb;  ///< Full Dumping Callback function
    VerilatedLxt2Callback_t m_changecb;  ///< Incremental Dumping Callback function
    void* m_userthis;  ///< Fake "this" for caller
    vluint32_t m_code;  ///< Starting code number
    // CONSTRUCTORS
    VerilatedLxt2CallInfo (VerilatedLxt2Callback_t icb, VerilatedLxt2Callback_t fcb,
                           VerilatedLxt2Callback_t changecb,
                           void* ut, vluint32_t code)
        : m_initcb(icb), m_fullcb(fcb), m_changecb(changecb), m_userthis(ut), m_code(code) {};
    ~VerilatedLxt2CallInfo() {}
};

//=============================================================================
// VerilatedLxt2

VerilatedLxt2::VerilatedLxt2(lxt2_wr_trace* lxt2)
    : m_lxt2(lxt2),
      m_fullDump(true),
      m_scopeEscape('.') {}

void VerilatedLxt2::open(const char* filename) VL_MT_UNSAFE {
    m_assertOne.check();
    m_lxt2 = lxt2_wr_init(filename);
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ent++) {
        VerilatedLxt2CallInfo* cip = m_callbacks[ent];
        cip->m_code = 1;
        (cip->m_initcb)(this, cip->m_userthis, cip->m_code);
    }
}

void VerilatedLxt2::module(const std::string& name) {
    m_module = name;
}

//=============================================================================
// Decl

void VerilatedLxt2::declSymbol(vluint32_t code, const char* name, int arraynum, int msb, int lsb, int flags) {
    if (msb == 0 && lsb == 0) {
        msb = lsb = -1;
    }
    std::pair<Code2SymbolType::iterator, bool> p
        = m_code2symbol.insert(std::make_pair(code, (lxt2_wr_symbol*)(NULL)));
    std::stringstream name_ss;
    name_ss <<m_module<<"."<<name;
    if (arraynum >= 0) {
        name_ss <<"("<<arraynum<<")";
    }
    std::string name_s = name_ss.str();
    for (std::string::iterator it = name_s.begin(); it != name_s.end(); ++it) {
        if (isScopeEscape(*it)) {
            *it = '.';
        }
    }
    if (p.second) {  // New
        p.first->second = lxt2_wr_symbol_add(m_lxt2, name_s.c_str(), 0, msb, lsb, flags);
        assert(p.first->second);
    } else {  // Alias
        lxt2_wr_symbol_alias(m_lxt2, p.first->second->name, name_s.c_str(), msb, lsb);
    }
}

//=============================================================================
// Callbacks

void VerilatedLxt2::addCallback(
    VerilatedLxt2Callback_t initcb, VerilatedLxt2Callback_t fullcb,
    VerilatedLxt2Callback_t changecb, void* userthis) VL_MT_UNSAFE_ONE {
    m_assertOne.check();
    if (VL_UNLIKELY(isOpen())) {
        std::string msg = std::string("Internal: ")+__FILE__+"::"+__FUNCTION__+" called with already open file";
        VL_FATAL_MT(__FILE__,__LINE__,"",msg.c_str());
    }
    VerilatedLxt2CallInfo* vci = new VerilatedLxt2CallInfo(initcb, fullcb, changecb, userthis, 1);
    m_callbacks.push_back(vci);
}

//=============================================================================
// Dumping

void VerilatedLxt2::dump(vluint64_t timeui) {
    if (!isOpen()) return;
    if (VL_UNLIKELY(m_fullDump)) {
        m_fullDump = false;  // No need for more full dumps
        for (vluint32_t ent = 0; ent< m_callbacks.size(); ent++) {
            VerilatedLxt2CallInfo* cip = m_callbacks[ent];
            (cip->m_fullcb)(this, cip->m_userthis, cip->m_code);
        }
        return;
    }
    lxt2_wr_set_time64(m_lxt2, timeui);
    for (vluint32_t ent = 0; ent< m_callbacks.size(); ++ent) {
        VerilatedLxt2CallInfo* cip = m_callbacks[ent];
        (cip->m_changecb)(this, cip->m_userthis, cip->m_code);
    }
}

//=============================================================================
// Helpers

char* VerilatedLxt2::quad2Str(vluint64_t newval, int bits) {
    m_valueStrBuffer.resize(bits+1);
    char* s = m_valueStrBuffer.data();
    for (int i = 0; i < bits; ++i) {
        *s = '0' + ((newval>>(bits-i-1))&1);
        ++s;
    }
    *s = '\0';
    return m_valueStrBuffer.data();
}

char* VerilatedLxt2::array2Str(const vluint32_t* newval, int bits) {
    int bq = bits/32, br = bits%32;
    m_valueStrBuffer.resize(bits+1);
    char* s = m_valueStrBuffer.data();
    for (int w = bq-1; w >= 0; --w) {
        for (int i = 0; i < 32; ++i) {
            *s = '0' + ((newval[w]>>(32-i-1))&1);
            ++s;
        }
    }
    for (int i = 0; i < br; ++i) {
        *s = '0' + ((newval[bq]>>(br-i-1))&1);
        ++s;
    }
    *s = '\0';
    return m_valueStrBuffer.data();
}

//********************************************************************
// Local Variables:
// End:
