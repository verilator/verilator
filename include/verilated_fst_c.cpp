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

// clang-format off

#define __STDC_LIMIT_MACROS  // UINT64_MAX
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

// clang-format on

//=============================================================================
// Specialization of the generics for this trace format

#define VL_DERIVED_T VerilatedFst
#include "verilated_trace_imp.cpp"
#undef VL_DERIVED_T

//=============================================================================
// VerilatedFst

VerilatedFst::VerilatedFst(void* fst)
    : m_fst(fst)
    , m_symbolp(NULL) {}

VerilatedFst::~VerilatedFst() {
    if (m_fst) fstWriterClose(m_fst);
    if (m_symbolp) VL_DO_CLEAR(delete[] m_symbolp, m_symbolp = NULL);
}

void VerilatedFst::open(const char* filename) VL_MT_UNSAFE {
    m_assertOne.check();
    m_fst = fstWriterCreate(filename, 1);
    fstWriterSetPackType(m_fst, FST_WR_PT_LZ4);
    fstWriterSetTimescaleFromString(m_fst, timeResStr().c_str());  // lintok-begin-on-ref
#ifdef VL_TRACE_THREADED
    fstWriterSetParallelMode(m_fst, 1);
#endif
    m_curScope.clear();

    VerilatedTrace<VerilatedFst>::traceInit();

    // Clear the scope stack
    std::list<std::string>::iterator it = m_curScope.begin();
    while (it != m_curScope.end()) {
        fstWriterSetUpscope(m_fst);
        it = m_curScope.erase(it);
    }

    // convert m_code2symbol into an array for fast lookup
    if (!m_symbolp) {
        m_symbolp = new fstHandle[nextCode()];
        for (Code2SymbolType::iterator it = m_code2symbol.begin(); it != m_code2symbol.end();
             ++it) {
            m_symbolp[it->first] = it->second;
        }
    }
    m_code2symbol.clear();
}

void VerilatedFst::emitTimeChange(vluint64_t timeui) { fstWriterEmitTimeChange(m_fst, timeui); }

//=============================================================================
// Decl

void VerilatedFst::declDTypeEnum(int dtypenum, const char* name, vluint32_t elements,
                                 unsigned int minValbits, const char** itemNamesp,
                                 const char** itemValuesp) {
    fstEnumHandle enumNum
        = fstWriterCreateEnumTable(m_fst, name, elements, minValbits, itemNamesp, itemValuesp);
    m_local2fstdtype[dtypenum] = enumNum;
}

void VerilatedFst::declSymbol(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                              fstVarType vartype, bool array, int arraynum, vluint32_t len,
                              vluint32_t bits) {
    VerilatedTrace<VerilatedFst>::declCode(code, bits, false);

    std::pair<Code2SymbolType::iterator, bool> p
        = m_code2symbol.insert(std::make_pair(code, static_cast<fstHandle>(NULL)));
    std::istringstream nameiss(name);
    std::istream_iterator<std::string> beg(nameiss), end;
    std::list<std::string> tokens(beg, end);  // Split name
    std::string symbol_name(tokens.back());
    tokens.pop_back();  // Remove symbol name from hierarchy
    tokens.insert(tokens.begin(), moduleName());  // Add current module to the hierarchy

    // Find point where current and new scope diverge
    std::list<std::string>::iterator cur_it = m_curScope.begin();
    std::list<std::string>::iterator new_it = tokens.begin();
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

void VerilatedFst::declBit(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                           fstVarType vartype, bool array, int arraynum) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 1, 1);
}
void VerilatedFst::declBus(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                           fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
               msb - lsb + 1);
}
void VerilatedFst::declQuad(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                            fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
               msb - lsb + 1);
}
void VerilatedFst::declArray(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                             fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
               msb - lsb + 1);
}
void VerilatedFst::declFloat(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                             fstVarType vartype, bool array, int arraynum) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 1, 32);
}
void VerilatedFst::declDouble(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                              fstVarType vartype, bool array, int arraynum) {
    declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 2, 64);
}

void VerilatedFst::emitBit(vluint32_t code, vluint32_t newval) {
    fstWriterEmitValueChange(m_fst, m_symbolp[code], newval ? "1" : "0");
}
template <int T_Bits> void VerilatedFst::emitBus(vluint32_t code, vluint32_t newval) {
    fstWriterEmitValueChange32(m_fst, m_symbolp[code], T_Bits, newval);
}
void VerilatedFst::emitQuad(vluint32_t code, vluint64_t newval, int bits) {
    fstWriterEmitValueChange64(m_fst, m_symbolp[code], bits, newval);
}
void VerilatedFst::emitArray(vluint32_t code, const vluint32_t* newvalp, int bits) {
    fstWriterEmitValueChangeVec32(m_fst, m_symbolp[code], bits, newvalp);
}
void VerilatedFst::emitFloat(vluint32_t code, float newval) {
    fstWriterEmitValueChange(m_fst, m_symbolp[code], &newval);
}
void VerilatedFst::emitDouble(vluint32_t code, double newval) {
    fstWriterEmitValueChange(m_fst, m_symbolp[code], &newval);
}
