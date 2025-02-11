// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
#include <vector>
#include <unordered_map>

class VerilatedSaifBuffer;
class VerilatedSaifFile;
struct ActivityBit {
    bool lastVal = false;
    uint64_t highTime = 0;
    size_t transitions = 0;

    VL_ATTR_ALWINLINE
    void aggregateVal(uint64_t dt, bool newVal) {
        transitions += newVal != lastVal ? 1 : 0;
        highTime += lastVal ? dt : 0;
        lastVal = newVal;
    }
};
struct ActivityVar {
    const char* name;
    uint32_t lsb;
    uint32_t width;
    ActivityBit* bits;
    uint64_t lastTime = 0;
};

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

    VerilatedSaifFile* m_filep;  // File we're writing to
    bool m_fileNewed;  // m_filep needs destruction
    bool m_isOpen = false;  // True indicates open file
    std::string m_filename;  // Filename we're writing to (if open)
    uint64_t m_rolloverSize = 0;  // File size to rollover at
    int m_indent = 0;  // Indentation depth

    char* m_wrBufp;  // Output buffer
    char* m_wrFlushp;  // Output buffer flush trigger location
    char* m_writep;  // Write pointer into output buffer
    size_t m_wrChunkSize;  // Output buffer size
    size_t m_maxSignalBytes = 0;  // Upper bound on number of bytes a single signal can generate
    uint64_t m_wroteBytes = 0;  // Number of bytes written to this file

    std::unordered_map<uint32_t, ActivityVar> m_activity;
    std::vector<std::vector<ActivityBit>> m_activityArena;
    uint64_t m_time;

    // Prefixes to add to signal names/scope types
    std::vector<std::pair<std::string, VerilatedTracePrefixType>> m_prefixStack{
        {"", VerilatedTracePrefixType::SCOPE_MODULE}};

    // Vector of free trace buffers as (pointer, size) pairs.
    std::vector<std::pair<char*, size_t>> m_freeBuffers;
    size_t m_numBuffers = 0;  // Number of trace buffers allocated

    void bufferResize(size_t minsize);
    void bufferFlush() VL_MT_UNSAFE_ONE;
    void bufferCheck() {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY(m_writep > m_wrFlushp)) bufferFlush();
    }
    void openNextImp(bool incFilename);
    void closePrev();
    void closeErr();
    void printStr(const char* str);
    void declare(uint32_t code, const char* name, const char* wirep, bool array, int arraynum,
                 bool bussed, int msb, int lsb);

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSaif);

protected:
    //=========================================================================
    // Implementation of VerilatedTrace interface

    // Called when the trace moves forward to a new time point
    void emitTimeChange(uint64_t timeui) override;

    // Hooks called from VerilatedTrace
    bool preFullDump() override { return isOpen(); }
    bool preChangeDump() override;

    // Trace buffer management
    Buffer* getTraceBuffer(uint32_t fidx) override;
    void commitTraceBuffer(Buffer*) override;

    // Configure sub-class
    void configure(const VerilatedTraceConfig&) override{};

public:
    //=========================================================================
    // External interface to client code

    // CONSTRUCTOR
    explicit VerilatedSaif(VerilatedSaifFile* filep = nullptr);
    ~VerilatedSaif();

    // ACCESSORS
    // Set size in bytes after which new file should be created.
    void rolloverSize(uint64_t size) VL_MT_SAFE { m_rolloverSize = size; }

    // METHODS - All must be thread safe
    // Open the file; call isOpen() to see if errors
    void open(const char* filename) VL_MT_SAFE_EXCLUDES(m_mutex);
    // Open next data-only file
    void openNext(bool incFilename) VL_MT_SAFE_EXCLUDES(m_mutex);
    // Close the file
    void close() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Flush any remaining data to this file
    void flush() VL_MT_SAFE_EXCLUDES(m_mutex);
    // Return if file is open
    bool isOpen() const VL_MT_SAFE { return m_isOpen; }

    //=========================================================================
    // Internal interface to Verilator generated code

    void pushPrefix(const std::string&, VerilatedTracePrefixType);
    void popPrefix();

    void declEvent(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                   VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                   bool array, int arraynum);
    void declBit(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                 VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                 bool array, int arraynum);
    void declBus(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                 VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                 bool array, int arraynum, int msb, int lsb);
    void declQuad(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                  VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                  bool array, int arraynum, int msb, int lsb);
    void declArray(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                   VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                   bool array, int arraynum, int msb, int lsb);
    void declDouble(uint32_t code, uint32_t fidx, const char* name, int dtypenum,
                    VerilatedTraceSigDirection, VerilatedTraceSigKind, VerilatedTraceSigType,
                    bool array, int arraynum);

// For debugging purposes
private:
    void printSignalDirection(VerilatedTraceSigDirection signalDirection);
    void printSignalKind(VerilatedTraceSigKind signalKind);
    void printSignalType(VerilatedTraceSigType signalType);
};

#ifndef DOXYGEN
// Declare specialization here as it's used in VerilatedFstC just below
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

    // Write pointer into output buffer (in parallel mode, this is set up in 'getTraceBuffer')
    char* m_writep = m_owner.parallel() ? nullptr : m_owner.m_writep;
    // Output buffer flush trigger location (only used when not parallel)
    char* const m_wrFlushp = m_owner.parallel() ? nullptr : m_owner.m_wrFlushp;

    // Additional data for parallel tracing only
    char* m_bufp = nullptr;  // The beginning of the trace buffer
    size_t m_size = 0;  // The size of the buffer at m_bufp
    char* m_growp = nullptr;  // Resize limit pointer

    // CONSTRUCTOR
    explicit VerilatedSaifBuffer(VerilatedSaif& owner)
        : m_owner{owner} {}
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
// VerilatedFile
/// Class representing a file to write to. These virtual methods can be
/// overrode for e.g. socket I/O.

class VerilatedSaifFile VL_NOT_FINAL {
private:
    int m_fd = 0;  // File descriptor we're writing to
public:
    // METHODS
    /// Construct a (as yet) closed file
    VerilatedSaifFile() = default;
    /// Close and destruct
    virtual ~VerilatedSaifFile() = default;
    /// Open a file with given filename
    virtual bool open(const std::string& name) VL_MT_UNSAFE;
    /// Close object's file
    virtual void close() VL_MT_UNSAFE;
    /// Write data to file (if it is open)
    virtual ssize_t write(const char* bufp, ssize_t len) VL_MT_UNSAFE;
};

//=============================================================================
// VerilatedSaifC
/// Class representing a SAIF dump file in C standalone (no SystemC)
/// simulations.  Also derived for use in SystemC simulations.

class VerilatedSaifC VL_NOT_FINAL : public VerilatedTraceBaseC {
    VerilatedSaif m_sptrace;  // Trace file being created

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedSaifC);

public:
    /// Construct the dump. Optional argument is a preconstructed file.
    explicit VerilatedSaifC(VerilatedSaifFile* filep = nullptr)
        : m_sptrace{filep} {}
    /// Destruct, flush, and close the dump
    virtual ~VerilatedSaifC() { close(); }

    // METHODS - User called

    /// Return if file is open
    bool isOpen() const override VL_MT_SAFE { return m_sptrace.isOpen(); }
    /// Open a new SAIF file
    /// This includes a complete header dump each time it is called,
    /// just as if this object was deleted and reconstructed.
    virtual void open(const char* filename) VL_MT_SAFE { m_sptrace.open(filename); }
    /// Continue a SAIF dump by rotating to a new file name
    /// The header is only in the first file created, this allows
    /// "cat" to be used to combine the header plus any number of data files.
    void openNext(bool incFilename = true) VL_MT_SAFE { m_sptrace.openNext(incFilename); }
    /// Set size in bytes after which new file should be created
    /// This will create a header file, followed by each separate file
    /// which might be larger than the given size (due to chunking and
    /// alignment to a start of a given time's dump).  Any file but the
    /// first may be removed.  Cat files together to create viewable saif.
    void rolloverSize(size_t size) VL_MT_SAFE { m_sptrace.rolloverSize(size); }
    /// Close dump
    void close() VL_MT_SAFE {
        m_sptrace.close();
        modelConnected(false);
    }
    /// Flush dump
    void flush() VL_MT_SAFE { m_sptrace.flush(); }
    /// Write one cycle of dump data
    /// Call with the current context's time just after eval'ed,
    /// e.g. ->dump(contextp->time())
    void dump(uint64_t timeui) VL_MT_SAFE { m_sptrace.dump(timeui); }
    /// Write one cycle of dump data - backward compatible and to reduce
    /// conversion warnings.  It's better to use a uint64_t time instead.
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
