// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated tracing in FST format header
///
/// User wrapper code should use this header when creating FST traces.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_FST_C_H_
#define VERILATOR_VERILATED_FST_C_H_

#include "verilated.h"
#include "verilated_trace.h"

#include "gtkwave/fstapi.h"

#include <list>
#include <map>
#include <string>
#include <vector>

//=============================================================================
// VerilatedFst
// Base class to create a Verilator FST dump
// This is an internally used class - see VerilatedFstC for what to call from applications

class VerilatedFst final : public VerilatedTrace<VerilatedFst> {
private:
    // Give the superclass access to private bits (to avoid virtual functions)
    friend class VerilatedTrace<VerilatedFst>;

    //=========================================================================
    // FST specific internals

    void* m_fst;
    std::map<vluint32_t, fstHandle> m_code2symbol;
    std::map<int, fstEnumHandle> m_local2fstdtype;
    std::list<std::string> m_curScope;
    fstHandle* m_symbolp = nullptr;  // same as m_code2symbol, but as an array
    char* m_strbuf = nullptr;  // String buffer long enough to hold maxBits() chars

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedFst);
    void declare(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum, int msb, int lsb);

protected:
    //=========================================================================
    // Implementation of VerilatedTrace interface

    // Implementations of protected virtual methods for VerilatedTrace
    virtual void emitTimeChange(vluint64_t timeui) override;

    // Hooks called from VerilatedTrace
    virtual bool preFullDump() override { return isOpen(); }
    virtual bool preChangeDump() override { return isOpen(); }

    // Implementations of duck-typed methods for VerilatedTrace. These are
    // called from only one place (namely full*) so always inline them.
    inline void emitBit(vluint32_t code, CData newval);
    inline void emitCData(vluint32_t code, CData newval, int bits);
    inline void emitSData(vluint32_t code, SData newval, int bits);
    inline void emitIData(vluint32_t code, IData newval, int bits);
    inline void emitQData(vluint32_t code, QData newval, int bits);
    inline void emitWData(vluint32_t code, const WData* newvalp, int bits);
    inline void emitDouble(vluint32_t code, double newval);

public:
    //=========================================================================
    // External interface to client code
    // (All must be threadsafe)

    explicit VerilatedFst(void* fst = nullptr);
    ~VerilatedFst();

    // Open the file; call isOpen() to see if errors
    void open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex);
    // Close the file
    void close() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Flush any remaining data to this file
    void flush() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Return if file is open
    bool isOpen() const VL_MT_SAFE { return m_fst != nullptr; }

    //=========================================================================
    // Internal interface to Verilator generated code

    // Inside dumping routines, declare a data type
    void declDTypeEnum(int dtypenum, const char* name, vluint32_t elements,
                       unsigned int minValbits, const char** itemNamesp, const char** itemValuesp);

    // Inside dumping routines, declare a signal
    void declBit(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum);
    void declBus(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                 fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declQuad(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                  fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declArray(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                   fstVarType vartype, bool array, int arraynum, int msb, int lsb);
    void declDouble(vluint32_t code, const char* name, int dtypenum, fstVarDir vardir,
                    fstVarType vartype, bool array, int arraynum);
};

#ifndef DOXYGEN
// Declare specialization here as it's used in VerilatedFstC just below
template <> void VerilatedTrace<VerilatedFst>::dump(vluint64_t timeui);
template <> void VerilatedTrace<VerilatedFst>::set_time_unit(const char* unitp);
template <> void VerilatedTrace<VerilatedFst>::set_time_unit(const std::string& unit);
template <> void VerilatedTrace<VerilatedFst>::set_time_resolution(const char* unitp);
template <> void VerilatedTrace<VerilatedFst>::set_time_resolution(const std::string& unit);
#endif

//=============================================================================
// VerilatedFstC
/// Create a FST dump file in C standalone (no SystemC) simulations.
/// Also derived for use in SystemC simulations.

class VerilatedFstC VL_NOT_FINAL {
    VerilatedFst m_sptrace;  // Trace file being created

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedFstC);

public:
    /// Construct the dump. Optional argument is ignored.
    explicit VerilatedFstC(void* filep = nullptr)
        : m_sptrace{filep} {}
    /// Destruct, flush, and close the dump
    ~VerilatedFstC() { close(); }

    // METHODS - User called

    /// Return if file is open
    bool isOpen() const VL_MT_SAFE { return m_sptrace.isOpen(); }
    /// Open a new FST file
    void open(const char* filename) VL_MT_SAFE { m_sptrace.open(filename); }
    /// Close dump
    void close() VL_MT_SAFE { m_sptrace.close(); }
    /// Flush dump
    void flush() VL_MT_SAFE { m_sptrace.flush(); }
    /// Write one cycle of dump data
    /// Call with the current context's time just after eval'ed,
    /// e.g. ->dump(contextp->time())
    void dump(vluint64_t timeui) { m_sptrace.dump(timeui); }
    /// Write one cycle of dump data - backward compatible and to reduce
    /// conversion warnings.  It's better to use a vluint64_t time instead.
    void dump(double timestamp) { dump(static_cast<vluint64_t>(timestamp)); }
    void dump(vluint32_t timestamp) { dump(static_cast<vluint64_t>(timestamp)); }
    void dump(int timestamp) { dump(static_cast<vluint64_t>(timestamp)); }

    // METHODS - Internal/backward compatible
    // \protectedsection

    // Set time units (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propage from the Verilated default timeunit
    void set_time_unit(const char* unitp) VL_MT_SAFE { m_sptrace.set_time_unit(unitp); }
    void set_time_unit(const std::string& unit) VL_MT_SAFE { m_sptrace.set_time_unit(unit); }
    // Set time resolution (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propage from the Verilated default timeprecision
    void set_time_resolution(const char* unitp) VL_MT_SAFE {
        m_sptrace.set_time_resolution(unitp);
    }
    void set_time_resolution(const std::string& unit) VL_MT_SAFE {
        m_sptrace.set_time_resolution(unit);
    }

    // Internal class access
    inline VerilatedFst* spTrace() { return &m_sptrace; };
};

#endif  // guard
