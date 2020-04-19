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

#ifndef _VERILATED_FST_C_H_
#define _VERILATED_FST_C_H_ 1

#include "verilatedos.h"
#include "verilated.h"

#include "gtkwave/fstapi.h"

#include <list>
#include <map>
#include <string>
#include <vector>

class VerilatedFst;
class VerilatedFstCallInfo;
typedef void (*VerilatedFstCallback_t)(VerilatedFst* vcdp, void* userthis, vluint32_t code);

//=============================================================================
// VerilatedFst
/// Base class to create a Verilator FST dump
/// This is an internally used class - see VerilatedFstC for what to call from applications

class VerilatedFst {
    typedef std::map<vluint32_t, fstHandle> Code2SymbolType;
    typedef std::map<int, fstEnumHandle> Local2FstDtype;
    typedef std::vector<VerilatedFstCallInfo*> CallbackVec;

private:
    void* m_fst;
    VerilatedAssertOneThread m_assertOne;  ///< Assert only called from single thread
    bool m_fullDump;
    vluint64_t m_minNextDumpTime;
    vluint32_t m_nextCode;  ///< Next code number to assign
    char m_scopeEscape;
    std::string m_module;
    CallbackVec m_callbacks;  ///< Routines to perform dumping
    Code2SymbolType m_code2symbol;
    Local2FstDtype m_local2fstdtype;
    std::list<std::string> m_curScope;
    fstHandle* m_symbolp;  ///< same as m_code2symbol, but as an array
    vluint32_t* m_sigs_oldvalp;
    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedFst);
    void declSymbol(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                    fstVarType vartype, bool array, int arraynum, vluint32_t len, vluint32_t bits);
    // helpers
    std::vector<char> m_valueStrBuffer;

    std::string m_timeRes;

public:
    explicit VerilatedFst(void* fst = NULL);
    ~VerilatedFst();
    void changeThread() { m_assertOne.changeThread(); }
    bool isOpen() const { return m_fst != NULL; }
    void open(const char* filename) VL_MT_UNSAFE;
    void flush() VL_MT_UNSAFE { fstWriterFlushContext(m_fst); }
    void close() VL_MT_UNSAFE {
        m_assertOne.check();
        fstWriterClose(m_fst);
        m_fst = NULL;
    }
    void set_time_unit(const char*) {}
    void set_time_unit(const std::string& unit) { set_time_unit(unit.c_str()); }

    void set_time_resolution(const char* unitp) { m_timeRes = unitp; }
    void set_time_resolution(const std::string& unit) { m_timeRes = unit; }

    // double timescaleToDouble(const char* unitp);
    // std::string doubleToTimescale(double value);

    /// Change character that splits scopes.  Note whitespace are ALWAYS escapes.
    void scopeEscape(char flag) { m_scopeEscape = flag; }
    /// Is this an escape?
    bool isScopeEscape(char c) { return isspace(c) || c == m_scopeEscape; }
    /// Inside dumping routines, called each cycle to make the dump
    void dump(vluint64_t timeui);
    /// Inside dumping routines, declare callbacks for tracings
    void addCallback(VerilatedFstCallback_t initcb, VerilatedFstCallback_t fullcb,
                     VerilatedFstCallback_t changecb, void* userthis) VL_MT_UNSAFE_ONE;

    /// Inside dumping routines, declare a module
    void module(const std::string& name);
    /// Inside dumping routines, declare a data type
    void declDTypeEnum(int dtypenum, const char* name, vluint32_t elements,
                       unsigned int minValbits, const char** itemNamesp, const char** itemValuesp);
    /// Inside dumping routines, declare a signal
    void declBit(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 1, 1);
    }
    void declBus(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
                   msb - lsb + 1);
    }
    void declQuad(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                  fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
                   msb - lsb + 1);
    }
    void declArray(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                   fstVarType vartype, bool array, int arraynum, int msb, int lsb) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, msb - lsb + 1,
                   msb - lsb + 1);
    }
    void declFloat(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                   fstVarType vartype, bool array, int arraynum) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 1, 32);
    }
    void declDouble(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                    fstVarType vartype, bool array, int arraynum) {
        declSymbol(code, name, dtypenum, vardir, vartype, array, arraynum, 2, 64);
    }

    //=========================================================================
    // Inside dumping routines used by Verilator

    vluint32_t* oldp(vluint32_t code) { return m_sigs_oldvalp + code; }

    //=========================================================================
    // Write back to previous value buffer value and emit

    void fullBit(vluint32_t* oldp, vluint32_t newval) {
        *oldp = newval;
        fstWriterEmitValueChange(m_fst, m_symbolp[oldp - m_sigs_oldvalp], newval ? "1" : "0");
    }
    template <int T_Bits> void fullBus(vluint32_t* oldp, vluint32_t newval) {
        *oldp = newval;
        fstWriterEmitValueChange32(m_fst, m_symbolp[oldp - m_sigs_oldvalp], T_Bits, newval);
    }
    void fullQuad(vluint32_t* oldp, vluint64_t newval, int bits) {
        *reinterpret_cast<vluint64_t*>(oldp) = newval;
        fstWriterEmitValueChange64(m_fst, m_symbolp[oldp - m_sigs_oldvalp], bits, newval);
    }
    void fullArray(vluint32_t* oldp, const vluint32_t* newvalp, int bits) {
        for (int i = 0; i < (bits + 31) / 32; ++i) oldp[i] = newvalp[i];
        fstWriterEmitValueChangeVec32(m_fst, m_symbolp[oldp - m_sigs_oldvalp], bits, newvalp);
    }
    void fullFloat(vluint32_t* oldp, float newval) {
        // cppcheck-suppress invalidPointerCast
        *reinterpret_cast<float*>(oldp) = newval;
        fstWriterEmitValueChange(m_fst, m_symbolp[oldp - m_sigs_oldvalp], oldp);
    }
    void fullDouble(vluint32_t* oldp, double newval) {
        // cppcheck-suppress invalidPointerCast
        *reinterpret_cast<double*>(oldp) = newval;
        fstWriterEmitValueChange(m_fst, m_symbolp[oldp - m_sigs_oldvalp], oldp);
    }

    //=========================================================================
    // Check previous value and emit if changed

    inline void chgBit(vluint32_t* oldp, vluint32_t newval) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(oldp, newval);
    }
    template <int T_Bits> inline void chgBus(vluint32_t* oldp, vluint32_t newval) {
        const vluint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBus<T_Bits>(oldp, newval);
    }
    inline void chgQuad(vluint32_t* oldp, vluint64_t newval, int bits) {
        const vluint64_t diff = *reinterpret_cast<vluint64_t*>(oldp) ^ newval;
        if (VL_UNLIKELY(diff)) fullQuad(oldp, newval, bits);
    }
    inline void chgArray(vluint32_t* oldp, const vluint32_t* newvalp, int bits) {
        for (int i = 0; i < (bits + 31) / 32; ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newvalp[i])) {
                fullArray(oldp, newvalp, bits);
                return;
            }
        }
    }
    inline void chgFloat(vluint32_t* oldp, float newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<float*>(oldp) != newval)) fullFloat(oldp, newval);
    }
    inline void chgDouble(vluint32_t* oldp, double newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY(*reinterpret_cast<double*>(oldp) != newval)) fullDouble(oldp, newval);
    }
};

//=============================================================================
// VerilatedFstC
/// Create a FST dump file in C standalone (no SystemC) simulations.
/// Also derived for use in SystemC simulations.
/// Thread safety: Unless otherwise indicated, every function is VL_MT_UNSAFE_ONE

class VerilatedFstC {
    VerilatedFst m_sptrace;  ///< Trace file being created

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedFstC);

public:
    explicit VerilatedFstC(void* filep = NULL)
        : m_sptrace(filep) {}
    ~VerilatedFstC() { close(); }
    /// Routines can only be called from one thread; allow next call from different thread
    void changeThread() { spTrace()->changeThread(); }

    // ACCESSORS
    /// Is file open?
    bool isOpen() const { return m_sptrace.isOpen(); }
    // METHODS
    /// Open a new FST file
    void open(const char* filename) VL_MT_UNSAFE_ONE { m_sptrace.open(filename); }
    /// Close dump
    void close() VL_MT_UNSAFE_ONE { m_sptrace.close(); }
    /// Flush dump
    void flush() VL_MT_UNSAFE_ONE { m_sptrace.flush(); }
    /// Write one cycle of dump data
    void dump(vluint64_t timeui) { m_sptrace.dump(timeui); }
    /// Write one cycle of dump data - backward compatible and to reduce
    /// conversion warnings.  It's better to use a vluint64_t time instead.
    void dump(double timestamp) { dump(static_cast<vluint64_t>(timestamp)); }
    void dump(vluint32_t timestamp) { dump(static_cast<vluint64_t>(timestamp)); }
    void dump(int timestamp) { dump(static_cast<vluint64_t>(timestamp)); }
    /// Set time units (s/ms, defaults to ns)
    /// For Verilated models, these propage from the Verilated default --timeunit
    void set_time_unit(const char* unitp) { m_sptrace.set_time_unit(unitp); }
    void set_time_unit(const std::string& unit) { set_time_unit(unit.c_str()); }
    /// Set time resolution (s/ms, defaults to ns)
    /// For Verilated models, these propage from the Verilated default --timeunit
    void set_time_resolution(const char* unitp) { m_sptrace.set_time_resolution(unitp); }
    void set_time_resolution(const std::string& unit) { set_time_resolution(unit.c_str()); }

    /// Internal class access
    inline VerilatedFst* spTrace() { return &m_sptrace; };
};

#endif  // guard
