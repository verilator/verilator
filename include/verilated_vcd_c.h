// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
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
/// \brief C++ Tracing in VCD Format
///
//=============================================================================
// SPDIFF_OFF

#ifndef _VERILATED_VCD_C_H_
#define _VERILATED_VCD_C_H_ 1

#include "verilated.h"
#include "verilated_trace.h"

#include <map>
#include <string>
#include <vector>

class VerilatedVcd;

// SPDIFF_ON
//=============================================================================
// VerilatedFile
/// File handling routines, which can be overrode for e.g. socket I/O

class VerilatedVcdFile VL_NOT_FINAL {
private:
    int m_fd = 0;  ///< File descriptor we're writing to
public:
    // METHODS
    VerilatedVcdFile() = default;
    virtual ~VerilatedVcdFile() = default;
    virtual bool open(const std::string& name) VL_MT_UNSAFE;
    virtual void close() VL_MT_UNSAFE;
    virtual ssize_t write(const char* bufp, ssize_t len) VL_MT_UNSAFE;
};

//=============================================================================
// VerilatedVcd
/// Base class to create a Verilator VCD dump
/// This is an internally used class - see VerilatedVcdC for what to call from applications

class VerilatedVcd VL_NOT_FINAL : public VerilatedTrace<VerilatedVcd> {
private:
    // Give the superclass access to private bits (to avoid virtual functions)
    friend class VerilatedTrace<VerilatedVcd>;

    //=========================================================================
    // VCD specific internals

    VerilatedVcdFile* m_filep;  ///< File we're writing to
    bool m_fileNewed;  ///< m_filep needs destruction
    bool m_isOpen = false;  ///< True indicates open file
    bool m_evcd = false;  ///< True for evcd format
    std::string m_filename;  ///< Filename we're writing to (if open)
    vluint64_t m_rolloverMB = 0;  ///< MB of file size to rollover at
    int m_modDepth = 0;  ///< Depth of module hierarchy

    char* m_wrBufp;  ///< Output buffer
    char* m_wrFlushp;  ///< Output buffer flush trigger location
    char* m_writep;  ///< Write pointer into output buffer
    vluint64_t m_wrChunkSize;  ///< Output buffer size
    vluint64_t m_wroteBytes = 0;  ///< Number of bytes written to this file

    std::vector<char> m_suffixes;  ///< VCD line end string codes + metadata
    const char* m_suffixesp;  ///< Pointer to first element of above

    typedef std::map<const std::string, const std::string> NameMap;
    NameMap* m_namemapp = nullptr;  ///< List of names for the header

    void bufferResize(vluint64_t minsize);
    void bufferFlush() VL_MT_UNSAFE_ONE;
    inline void bufferCheck() {
        // Flush the write buffer if there's not enough space left for new information
        // We only call this once per vector, so we need enough slop for a very wide "b###" line
        if (VL_UNLIKELY(m_writep > m_wrFlushp)) bufferFlush();
    }
    void closePrev();
    void closeErr();
    void openNext();
    void makeNameMap();
    void deleteNameMap();
    void printIndent(int level_change);
    void printStr(const char* str);
    void printQuad(vluint64_t n);
    void printTime(vluint64_t timeui);
    void declare(vluint32_t code, const char* name, const char* wirep, bool array, int arraynum,
                 bool tri, bool bussed, int msb, int lsb);

    void dumpHeader();

    static char* writeCode(char* writep, vluint32_t code);

    void finishLine(vluint32_t code, char* writep);

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedVcd);

protected:
    //=========================================================================
    // Implementation of VerilatedTrace interface

    // Implementations of protected virtual methods for VerilatedTrace
    virtual void emitTimeChange(vluint64_t timeui) override;

    // Hooks called from VerilatedTrace
    virtual bool preFullDump() override { return isOpen(); }
    virtual bool preChangeDump() override;

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

    explicit VerilatedVcd(VerilatedVcdFile* filep = nullptr);
    ~VerilatedVcd();

    // ACCESSORS
    /// Set size in megabytes after which new file should be created
    void rolloverMB(vluint64_t rolloverMB) { m_rolloverMB = rolloverMB; }

    // METHODS
    /// Open the file; call isOpen() to see if errors
    void open(const char* filename) VL_MT_UNSAFE_ONE;
    /// Open next data-only file
    void openNext(bool incFilename) VL_MT_UNSAFE_ONE;
    /// Close the file
    void close() VL_MT_UNSAFE_ONE;
    /// Flush any remaining data to this file
    void flush() VL_MT_UNSAFE_ONE;
    /// Is file open?
    bool isOpen() const { return m_isOpen; }

    //=========================================================================
    // Internal interface to Verilator generated code

    void declBit(vluint32_t code, const char* name, bool array, int arraynum);
    void declBus(vluint32_t code, const char* name, bool array, int arraynum, int msb, int lsb);
    void declQuad(vluint32_t code, const char* name, bool array, int arraynum, int msb, int lsb);
    void declArray(vluint32_t code, const char* name, bool array, int arraynum, int msb, int lsb);
    void declDouble(vluint32_t code, const char* name, bool array, int arraynum);

#ifdef VL_TRACE_VCD_OLD_API
    //=========================================================================
    // Note: These are only for testing for backward compatibility with foreign
    // code and is not used by Verilator. Do not use these as there is no
    // guarantee of functionality.

    void declTriBit(vluint32_t code, const char* name, bool array, int arraynum);
    void declTriBus(vluint32_t code, const char* name, bool array, int arraynum, int msb, int lsb);
    void declTriQuad(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                     int lsb);
    void declTriArray(vluint32_t code, const char* name, bool array, int arraynum, int msb,
                      int lsb);

    void fullBit(vluint32_t* oldp, CData newval) { fullBit(oldp - this->oldp(0), newval); }
    void fullCData(vluint32_t* oldp, CData newval, int bits) {
        fullBus(oldp - this->oldp(0), newval, bits);
    }
    void fullSData(vluint32_t* oldp, SData newval, int bits) {
        fullBus(oldp - this->oldp(0), newval, bits);
    }
    void fullIData(vluint32_t* oldp, IData newval, int bits) {
        fullBus(oldp - this->oldp(0), newval, bits);
    }
    void fullQData(vluint32_t* oldp, QData newval, int bits) {
        fullQuad(oldp - this->oldp(0), newval, bits);
    }
    void fullWData(vluint32_t* oldp, const WData* newvalp, int bits) {
        fullArray(oldp - this->oldp(0), newvalp, bits);
    }
    void fullDouble(vluint32_t* oldp, double newval) { fullDouble(oldp - this->oldp(0), newval); }

    inline void chgBit(vluint32_t* oldp, CData newval) { chgBit(oldp - this->oldp(0), newval); }
    inline void chgCData(vluint32_t* oldp, CData newval, int bits) {
        chgBus(oldp - this->oldp(0), newval, bits);
    }
    inline void chgSData(vluint32_t* oldp, SData newval, int bits) {
        chgBus(oldp - this->oldp(0), newval, bits);
    }
    inline void chgIData(vluint32_t* oldp, IData newval, int bits) {
        chgBus(oldp - this->oldp(0), newval, bits);
    }
    inline void chgQData(vluint32_t* oldp, QData newval, int bits) {
        chgQuad(oldp - this->oldp(0), newval, bits);
    }
    inline void chgWData(vluint32_t* oldp, const WData* newvalp, int bits) {
        chgArray(oldp - this->oldp(0), newvalp, bits);
    }
    inline void chgDouble(vluint32_t* oldp, double newval) {
        chgDouble(oldp - this->oldp(0), newval);
    }

    /// Inside dumping routines, dump one signal, faster when not inlined
    /// due to code size reduction.
    void fullBit(vluint32_t code, const vluint32_t newval);
    void fullBus(vluint32_t code, const vluint32_t newval, int bits);
    void fullQuad(vluint32_t code, const vluint64_t newval, int bits);
    void fullArray(vluint32_t code, const vluint32_t* newvalp, int bits);
    void fullArray(vluint32_t code, const vluint64_t* newvalp, int bits);
    void fullTriBit(vluint32_t code, const vluint32_t newval, const vluint32_t newtri);
    void fullTriBus(vluint32_t code, const vluint32_t newval, const vluint32_t newtri, int bits);
    void fullTriQuad(vluint32_t code, const vluint64_t newval, const vluint64_t newtri, int bits);
    void fullTriArray(vluint32_t code, const vluint32_t* newvalp, const vluint32_t* newtrip,
                      int bits);
    void fullDouble(vluint32_t code, const double newval);

    /// Inside dumping routines, dump one signal if it has changed.
    /// We do want to inline these to avoid calls when the value did not change.
    inline void chgBit(vluint32_t code, const vluint32_t newval) {
        vluint32_t diff = oldp(code)[0] ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(code, newval);
    }
    inline void chgBus(vluint32_t code, const vluint32_t newval, int bits) {
        vluint32_t diff = oldp(code)[0] ^ newval;
        if (VL_UNLIKELY(diff)) {
            if (VL_UNLIKELY(bits == 32 || (diff & ((1U << bits) - 1)))) {
                fullBus(code, newval, bits);
            }
        }
    }
    inline void chgQuad(vluint32_t code, const vluint64_t newval, int bits) {
        vluint64_t diff = (*(reinterpret_cast<vluint64_t*>(oldp(code)))) ^ newval;
        if (VL_UNLIKELY(diff)) {
            if (VL_UNLIKELY(bits == 64 || (diff & ((1ULL << bits) - 1)))) {
                fullQuad(code, newval, bits);
            }
        }
    }
    inline void chgArray(vluint32_t code, const vluint32_t* newvalp, int bits) {
        for (int word = 0; word < (((bits - 1) / 32) + 1); ++word) {
            if (VL_UNLIKELY(oldp(code)[word] ^ newvalp[word])) {
                fullArray(code, newvalp, bits);
                return;
            }
        }
    }
    inline void chgArray(vluint32_t code, const vluint64_t* newvalp, int bits) {
        for (int word = 0; word < (((bits - 1) / 64) + 1); ++word) {
            if (VL_UNLIKELY(*(reinterpret_cast<vluint64_t*>(oldp(code + 2 * word)))
                            ^ newvalp[word])) {
                fullArray(code, newvalp, bits);
                return;
            }
        }
    }
    inline void chgTriBit(vluint32_t code, const vluint32_t newval, const vluint32_t newtri) {
        vluint32_t diff = ((oldp(code)[0] ^ newval) | (oldp(code)[1] ^ newtri));
        if (VL_UNLIKELY(diff)) {
            // Verilator 3.510 and newer provide clean input, so the below
            // is only for back compatibility
            if (VL_UNLIKELY(diff & 1)) {  // Change after clean?
                fullTriBit(code, newval, newtri);
            }
        }
    }
    inline void chgTriBus(vluint32_t code, const vluint32_t newval, const vluint32_t newtri,
                          int bits) {
        vluint32_t diff = ((oldp(code)[0] ^ newval) | (oldp(code)[1] ^ newtri));
        if (VL_UNLIKELY(diff)) {
            if (VL_UNLIKELY(bits == 32 || (diff & ((1U << bits) - 1)))) {
                fullTriBus(code, newval, newtri, bits);
            }
        }
    }
    inline void chgTriQuad(vluint32_t code, const vluint64_t newval, const vluint64_t newtri,
                           int bits) {
        vluint64_t diff = (((*(reinterpret_cast<vluint64_t*>(oldp(code)))) ^ newval)
                           | ((*(reinterpret_cast<vluint64_t*>(oldp(code + 1)))) ^ newtri));
        if (VL_UNLIKELY(diff)) {
            if (VL_UNLIKELY(bits == 64 || (diff & ((1ULL << bits) - 1)))) {
                fullTriQuad(code, newval, newtri, bits);
            }
        }
    }
    inline void chgTriArray(vluint32_t code, const vluint32_t* newvalp, const vluint32_t* newtrip,
                            int bits) {
        for (int word = 0; word < (((bits - 1) / 32) + 1); ++word) {
            if (VL_UNLIKELY((oldp(code)[word * 2] ^ newvalp[word])
                            | (oldp(code)[word * 2 + 1] ^ newtrip[word]))) {
                fullTriArray(code, newvalp, newtrip, bits);
                return;
            }
        }
    }
    inline void chgDouble(vluint32_t code, const double newval) {
        // cppcheck-suppress invalidPointerCast
        if (VL_UNLIKELY((*(reinterpret_cast<double*>(oldp(code)))) != newval)) {
            fullDouble(code, newval);
        }
    }

    // METHODS
    // Old/standalone API only
    void evcd(bool flag) { m_evcd = flag; }
#endif  // VL_TRACE_VCD_OLD_API
};

// Declare specializations here they are used in VerilatedVcdC just below
template <> void VerilatedTrace<VerilatedVcd>::dump(vluint64_t timeui);
template <> void VerilatedTrace<VerilatedVcd>::set_time_unit(const char* unitp);
template <> void VerilatedTrace<VerilatedVcd>::set_time_unit(const std::string& unit);
template <> void VerilatedTrace<VerilatedVcd>::set_time_resolution(const char* unitp);
template <> void VerilatedTrace<VerilatedVcd>::set_time_resolution(const std::string& unit);

//=============================================================================
// VerilatedVcdC
/// Create a VCD dump file in C standalone (no SystemC) simulations.
/// Also derived for use in SystemC simulations.
/// Thread safety: Unless otherwise indicated, every function is VL_MT_UNSAFE_ONE

class VerilatedVcdC VL_NOT_FINAL {
    VerilatedVcd m_sptrace;  ///< Trace file being created

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedVcdC);

public:
    explicit VerilatedVcdC(VerilatedVcdFile* filep = nullptr)
        : m_sptrace{filep} {}
    ~VerilatedVcdC() { close(); }
    /// Routines can only be called from one thread; allow next call from different thread
    void changeThread() { spTrace()->changeThread(); }

public:
    // ACCESSORS
    /// Is file open?
    bool isOpen() const { return m_sptrace.isOpen(); }
    // METHODS
    /// Open a new VCD file
    /// This includes a complete header dump each time it is called,
    /// just as if this object was deleted and reconstructed.
    void open(const char* filename) VL_MT_UNSAFE_ONE { m_sptrace.open(filename); }
    /// Continue a VCD dump by rotating to a new file name
    /// The header is only in the first file created, this allows
    /// "cat" to be used to combine the header plus any number of data files.
    void openNext(bool incFilename = true) VL_MT_UNSAFE_ONE { m_sptrace.openNext(incFilename); }
    /// Set size in megabytes after which new file should be created
    void rolloverMB(size_t rolloverMB) { m_sptrace.rolloverMB(rolloverMB); }
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
    void set_time_unit(const char* unit) { m_sptrace.set_time_unit(unit); }
    void set_time_unit(const std::string& unit) { m_sptrace.set_time_unit(unit); }
    /// Set time resolution (s/ms, defaults to ns)
    /// For Verilated models, these propage from the Verilated default --timeunit
    void set_time_resolution(const char* unit) { m_sptrace.set_time_resolution(unit); }
    void set_time_resolution(const std::string& unit) { m_sptrace.set_time_resolution(unit); }

    /// Internal class access
    inline VerilatedVcd* spTrace() { return &m_sptrace; }

#ifdef VL_TRACE_VCD_OLD_API
    //=========================================================================
    // Note: These are only for testing for backward compatibility with foreign
    // code and is not used by Verilator. Do not use these as there is no
    // guarantee of functionality.
    /// Use evcd format
    void evcd(bool flag) VL_MT_UNSAFE_ONE { m_sptrace.evcd(flag); }
#endif
};

#endif  // guard
