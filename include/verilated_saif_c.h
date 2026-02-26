// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2001-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated tracing in SAIF format header
///
/// User wrapper code should use this header when creating SAIF traces.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_SAIF_C_H_
#define VERILATOR_VERILATED_SAIF_C_H_

#include "verilated.h"
#include "verilated_trace.h"

#include <string>
#include <unordered_map>
#include <vector>

class VerilatedSaifBuffer;
class VerilatedSaifActivityAccumulator;
class VerilatedSaifActivityScope;
class VerilatedSaifActivityVar;
class VerilatedSaifActivityBit;

//=============================================================================
// VerilatedSaif
// Base class to create a Verilator SAIF dump
// This is an internally used class - see VerilatedSaifC for what to call from applications

class VerilatedSaif VL_NOT_FINAL : public VerilatedTrace<VerilatedSaif, VerilatedSaifBuffer> {
public:
    using Super = VerilatedTrace<VerilatedSaif, VerilatedSaifBuffer>;

private:
    friend VerilatedSaifBuffer;  // Give the buffer access to the private bits

    //=========================================================================
    // SAIF-specific internals

    int m_filep = 0;  // File we're writing to
    bool m_isOpen = false;  // True indicates open file
    std::string m_filename;  // Filename we're writing to (if open)
    std::string m_buffer;  // Write data buffer

    int m_indent = 0;  // Indentation size in spaces
    static constexpr size_t WRITE_BUFFER_SIZE = 256 * 1024;  // Bytes between write calls

    // Currently active scope
    VerilatedSaifActivityScope* m_currentScope = nullptr;
    // Array of declared scopes
    std::vector<std::unique_ptr<VerilatedSaifActivityScope>> m_scopes{};
    // Activity accumulators used to store variables statistics over simulation time
    std::vector<std::unique_ptr<VerilatedSaifActivityAccumulator>> m_activityAccumulators{};
    // Total time of the currently traced simulation
    uint64_t m_time = 0;

    // Stack of declared scopes combined names
    std::vector<std::pair<std::string, VerilatedTracePrefixType>> m_prefixStack{
        {"", VerilatedTracePrefixType::SCOPE_MODULE}};

    // METHODS
    VL_ATTR_ALWINLINE uint64_t currentTime() const { return m_time; }

    void initializeSaifFileContents();
    void finalizeSaifFileContents();
    void recursivelyPrintScopes(const VerilatedSaifActivityScope& scope);
    void openInstanceScope(const std::string& instanceName);
    void closeInstanceScope();
    void printScopeActivities(const VerilatedSaifActivityScope& scope);
    bool
    printScopeActivitiesFromAccumulatorIfPresent(const std::string& absoluteScopePath,
                                                 VerilatedSaifActivityAccumulator& accumulator,
                                                 bool anyNetWritten);
    void openNetScope();
    void closeNetScope();
    bool printActivityStats(VerilatedSaifActivityVar& activity, const std::string& activityName,
                            bool anyNetWritten);

    void incrementIndent();
    void decrementIndent();
    void printIndent();

    void printStr(const char* str);
    void printStr(const std::string& str);
    void writeBuffered(bool force);

    void clearCurrentlyCollectedData();

    void declare(uint32_t code, uint32_t fidx, const char* name, const char* wirep, bool array,
                 int arraynum, bool bussed, int msb, int lsb);

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSaif);

protected:
    //=========================================================================
    // Implementation of VerilatedTrace interface

    // Called when the trace moves forward to a new time point
    void emitTimeChange(uint64_t timeui) override;

    // Hooks called from VerilatedTrace
    bool preFullDump() override { return isOpen(); }
    bool preChangeDump() override { return isOpen(); }

    // Trace buffer management
    Buffer* getTraceBuffer(uint32_t fidx) override;
    void commitTraceBuffer(Buffer*) override;

    // Configure sub-class
    void configure(const VerilatedTraceConfig&) override {}

public:
    //=========================================================================
    // External interface to client code

    // CONSTRUCTOR
    explicit VerilatedSaif(void* filep = nullptr);
    ~VerilatedSaif();

    // METHODS - All must be thread safe
    // Open the file; call isOpen() to see if errors
    void open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex);
    // Close the file
    void close() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Flush any remaining data to this file
    void flush() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Return if file is open
    bool isOpen() const VL_MT_SAFE { return m_isOpen; }

    //=========================================================================
    // Internal interface to Verilator generated code

    void pushPrefix(const char*, VerilatedTracePrefixType);
    void popPrefix();

    // versions to call when the sig is not array member
    void declEvent(uint32_t code, uint32_t fidx, const char* name);
    void declBit(uint32_t code, uint32_t fidx, const char* name);
    void declBus(uint32_t code, uint32_t fidx, const char* name, int msb, int lsb);
    void declQuad(uint32_t code, uint32_t fidx, const char* name, int msb, int lsb);
    void declWide(uint32_t code, uint32_t fidx, const char* name, int msb, int lsb);
    void declDouble(uint32_t code, uint32_t fidx, const char* name);

    // versions to call when the sig is array member
    void declEventArray(uint32_t code, uint32_t fidx, const char* name, int arraynum);
    void declBitArray(uint32_t code, uint32_t fidx, const char* name, int arraynum);
    void declBusArray(uint32_t code, uint32_t fidx, const char* name, int arraynum, int msb,
                      int lsb);
    void declQuadArray(uint32_t code, uint32_t fidx, const char* name, int arraynum, int msb,
                       int lsb);
    void declWideArray(uint32_t code, uint32_t fidx, const char* name, int arraynum, int msb,
                       int lsb);
    void declDoubleArray(uint32_t code, uint32_t fidx, const char* name, int arraynum);
};

// duck-typed interface to decl* methods
// We use macros in order to strip out unused args at compile time.
#define VL_TRACE_DECL_EVENT(tracep, code, fidx, name, dtypenum, dir, kind, type) \
    tracep->declEvent(code, fidx, name)
#define VL_TRACE_DECL_BIT(tracep, code, fidx, name, dtypenum, dir, kind, type) \
    tracep->declBit(code, fidx, name)
#define VL_TRACE_DECL_BUS(tracep, code, fidx, name, dtypenum, dir, kind, type, msb, lsb) \
    tracep->declBus(code, fidx, name, msb, lsb)
#define VL_TRACE_DECL_QUAD(tracep, code, fidx, name, dtypenum, dir, kind, type, msb, lsb) \
    tracep->declQuad(code, fidx, name, msb, lsb)
#define VL_TRACE_DECL_WIDE(tracep, code, fidx, name, dtypenum, dir, kind, type, msb, lsb) \
    tracep->declWide(code, fidx, name, msb, lsb)
#define VL_TRACE_DECL_DOUBLE(tracep, code, fidx, name, dtypenum, dir, kind, type) \
    tracep->declDouble(code, fidx, name)

#define VL_TRACE_DECL_EVENT_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum) \
    tracep->declEventArray(code, fidx, name, arraynum)
#define VL_TRACE_DECL_BIT_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum) \
    tracep->declBitArray(code, fidx, name, arraynum)
#define VL_TRACE_DECL_BUS_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum, \
                                msb, lsb) \
    tracep->declBusArray(code, fidx, name, arraynum, msb, lsb)
#define VL_TRACE_DECL_QUAD_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum, \
                                 msb, lsb) \
    tracep->declQuadArray(code, fidx, name, arraynum, msb, lsb)
#define VL_TRACE_DECL_WIDE_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum, \
                                 msb, lsb) \
    tracep->declWideArray(code, fidx, name, arraynum, msb, lsb)
#define VL_TRACE_DECL_DOUBLE_ARRAY(tracep, code, fidx, name, dtypenum, dir, kind, type, arraynum) \
    tracep->declDoubleArray(code, fidx, name, arraynum)

#ifndef DOXYGEN
// Declare specialization here as it's used in VerilatedSaifC just below
template <>
void VerilatedSaif::Super::dump(uint64_t time);
template <>
void VerilatedSaif::Super::set_time_unit(const char* unitp);
template <>
void VerilatedSaif::Super::set_time_unit(const std::string& unit);
template <>
void VerilatedSaif::Super::set_time_resolution(const char* unitp);
template <>
void VerilatedSaif::Super::set_time_resolution(const std::string& unit);
template <>
void VerilatedSaif::Super::dumpvars(int level, const std::string& hier);
#endif  // DOXYGEN

//=============================================================================
// VerilatedSaifBuffer

class VerilatedSaifBuffer VL_NOT_FINAL {
    // Give the trace file and sub-classes access to the private bits
    friend VerilatedSaif;
    friend VerilatedSaif::Super;
    friend VerilatedSaif::Buffer;
    friend VerilatedSaif::OffloadBuffer;

    VerilatedSaif& m_owner;  // Trace file owning this buffer. Required by subclasses.
    uint32_t m_fidx;  // Index of target activity accumulator

    // CONSTRUCTORS
    explicit VerilatedSaifBuffer(VerilatedSaif& owner)
        : m_owner{owner}
        , m_fidx{0} {}
    explicit VerilatedSaifBuffer(VerilatedSaif& owner, uint32_t fidx)
        : m_owner{owner}
        , m_fidx{fidx} {}
    virtual ~VerilatedSaifBuffer() = default;

    //=========================================================================
    // Implementation of VerilatedTraceBuffer interface
    // Implementations of duck-typed methods for VerilatedTraceBuffer. These are
    // called from only one place (the full* methods), so always inline them.
    VL_ATTR_ALWINLINE void emitEvent(uint32_t code);
    VL_ATTR_ALWINLINE void emitBit(uint32_t code, CData newval);
    VL_ATTR_ALWINLINE void emitCData(uint32_t code, CData newval, int bits);
    VL_ATTR_ALWINLINE void emitSData(uint32_t code, SData newval, int bits);
    VL_ATTR_ALWINLINE void emitIData(uint32_t code, IData newval, int bits);
    VL_ATTR_ALWINLINE void emitQData(uint32_t code, QData newval, int bits);
    VL_ATTR_ALWINLINE void emitWData(uint32_t code, const WData* newvalp, int bits);
    VL_ATTR_ALWINLINE void emitDouble(uint32_t code, double newval);
};

//=============================================================================
// VerilatedSaifC
// Class representing a SAIF dump file in C standalone (no SystemC)
// simulations. Also derived for use in SystemC simulations.

class VerilatedSaifC VL_NOT_FINAL : public VerilatedTraceBaseC {
    VerilatedSaif m_sptrace;  // Trace file being created

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSaifC);

public:
    // Construct the dump. Optional argument is ignored
    explicit VerilatedSaifC(void* filep = nullptr)
        : m_sptrace{filep} {}
    // Destruct, flush, and close the dump
    virtual ~VerilatedSaifC() { close(); }

    // METHODS - User called

    // Return if file is open
    bool isOpen() const override VL_MT_SAFE { return m_sptrace.isOpen(); }
    // Open a new SAIF file
    // This includes a complete header dump each time it is called,
    // just as if this object was deleted and reconstructed.
    virtual void open(const char* filename) VL_MT_SAFE { m_sptrace.open(filename); }

    void rolloverSize(size_t size) VL_MT_SAFE {}  // NOP

    // Close dump
    void close() VL_MT_SAFE {
        m_sptrace.close();
        modelConnected(false);
    }
    // Flush dump
    void flush() VL_MT_SAFE { m_sptrace.flush(); }
    // Write one cycle of dump data
    // Call with the current context's time just after eval'ed,
    // e.g. ->dump(contextp->time())
    void dump(uint64_t timeui) VL_MT_SAFE { m_sptrace.dump(timeui); }
    // Write one cycle of dump data - backward compatible and to reduce
    // conversion warnings.  It's better to use a uint64_t time instead.
    void dump(double timestamp) { dump(static_cast<uint64_t>(timestamp)); }
    void dump(uint32_t timestamp) { dump(static_cast<uint64_t>(timestamp)); }
    void dump(int timestamp) { dump(static_cast<uint64_t>(timestamp)); }

    // METHODS - Internal/backward compatible
    // \protectedsection

    // Set time units (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propagate from the Verilated default timeunit
    void set_time_unit(const char* unit) VL_MT_SAFE { m_sptrace.set_time_unit(unit); }
    void set_time_unit(const std::string& unit) VL_MT_SAFE { m_sptrace.set_time_unit(unit); }
    // Set time resolution (s/ms, defaults to ns)
    // Users should not need to call this, as for Verilated models, these
    // propagate from the Verilated default timeprecision
    void set_time_resolution(const char* unit) VL_MT_SAFE { m_sptrace.set_time_resolution(unit); }
    void set_time_resolution(const std::string& unit) VL_MT_SAFE {
        m_sptrace.set_time_resolution(unit);
    }
    // Set variables to dump, using $dumpvars format
    // If level = 0, dump everything and hier is then ignored
    void dumpvars(int level, const std::string& hier) VL_MT_SAFE {
        m_sptrace.dumpvars(level, hier);
    }

    // Internal class access
    VerilatedSaif* spTrace() { return &m_sptrace; }
};

#endif  // guard
