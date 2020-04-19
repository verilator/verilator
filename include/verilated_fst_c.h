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

#include "verilated.h"
#include "verilated_trace.h"

#include "gtkwave/fstapi.h"

#include <list>
#include <map>
#include <string>
#include <vector>

//=============================================================================
// VerilatedFst
/// Base class to create a Verilator FST dump
/// This is an internally used class - see VerilatedFstC for what to call from applications

class VerilatedFst : public VerilatedTrace<VerilatedFst> {
private:
    // Give the superclass access to private bits (to avoid virtual functions)
    friend class VerilatedTrace<VerilatedFst>;

    //=========================================================================
    // FST specific internals

    typedef std::map<vluint32_t, fstHandle> Code2SymbolType;
    typedef std::map<int, fstEnumHandle> Local2FstDtype;

    void* m_fst;
    Code2SymbolType m_code2symbol;
    Local2FstDtype m_local2fstdtype;
    std::list<std::string> m_curScope;
    fstHandle* m_symbolp;  ///< same as m_code2symbol, but as an array
    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedFst);
    void declSymbol(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                    fstVarType vartype, bool array, int arraynum, vluint32_t len, vluint32_t bits);

protected:
    //=========================================================================
    // Implementation of VerilatedTrace interface

    // Implementations of protected virtual methods for VerilatedTrace
    void emitTimeChange(vluint64_t timeui) VL_OVERRIDE;

    // Hooks called from VerilatedTrace
    bool preFullDump() VL_OVERRIDE { return isOpen(); }
    bool preChangeDump() VL_OVERRIDE { return isOpen(); }

    // Implementations of duck-typed methods for VerilatedTrace
    void emitBit(vluint32_t code, vluint32_t newval);
    template <int T_Bits> void emitBus(vluint32_t code, vluint32_t newval);
    void emitQuad(vluint32_t code, vluint64_t newval, int bits);
    void emitArray(vluint32_t code, const vluint32_t* newvalp, int bits);
    void emitFloat(vluint32_t code, float newval);
    void emitDouble(vluint32_t code, double newval);

public:
    //=========================================================================
    // External interface to client code

    explicit VerilatedFst(void* fst = NULL);
    ~VerilatedFst();

    /// Open the file; call isOpen() to see if errors
    void open(const char* filename) VL_MT_UNSAFE;
    /// Close the file
    void close() VL_MT_UNSAFE {
        m_assertOne.check();
        fstWriterClose(m_fst);
        m_fst = NULL;
    }
    /// Flush any remaining data to this file
    void flush() VL_MT_UNSAFE { fstWriterFlushContext(m_fst); }
    /// Is file open?
    bool isOpen() const { return m_fst != NULL; }

    //=========================================================================
    // Internal interface to Verilator generated code

    /// Inside dumping routines, declare a data type
    void declDTypeEnum(int dtypenum, const char* name, vluint32_t elements,
                       unsigned int minValbits, const char** itemNamesp, const char** itemValuesp);

    /// Inside dumping routines, declare a signal
    void declBit(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum);
    void declBus(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declQuad(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                  fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declArray(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                   fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declFloat(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                   fstVarType vartype, bool array, int arraynum);
    void declDouble(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                    fstVarType vartype, bool array, int arraynum);
};

// Declare specialization here as it's used in VerilatedFstC just below
template <> void VerilatedTrace<VerilatedFst>::dump(vluint64_t timeui);
template <> void VerilatedTrace<VerilatedFst>::set_time_unit(const char* unitp);
template <> void VerilatedTrace<VerilatedFst>::set_time_unit(const std::string& unit);
template <> void VerilatedTrace<VerilatedFst>::set_time_resolution(const char* unitp);
template <> void VerilatedTrace<VerilatedFst>::set_time_resolution(const std::string& unit);

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
    void set_time_unit(const std::string& unit) { m_sptrace.set_time_unit(unit); }
    /// Set time resolution (s/ms, defaults to ns)
    /// For Verilated models, these propage from the Verilated default --timeunit
    void set_time_resolution(const char* unitp) { m_sptrace.set_time_resolution(unitp); }
    void set_time_resolution(const std::string& unit) { m_sptrace.set_time_resolution(unit); }

    /// Internal class access
    inline VerilatedFst* spTrace() { return &m_sptrace; };
};

#endif  // guard
