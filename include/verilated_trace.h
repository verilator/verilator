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
/// \brief Verilated internal common-tracing header
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated tracing routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_TRACE_H_
#define VERILATOR_VERILATED_TRACE_H_

// clang-format off

#include "verilated.h"

#include <bitset>
#include <condition_variable>
#include <memory>
#include <string>
#include <type_traits>
#include <map>
#include <set>
#include <vector>

#include <deque>
#include <thread>

// clang-format on

class VlThreadPool;
template <typename T_Buffer>
class VerilatedTraceBuffer;

//=============================================================================
// Common enumerations

enum class VerilatedTracePrefixType : uint8_t {
    // Note: Entries must match VTracePrefixType (by name, not necessarily by value)
    ARRAY_PACKED,
    ARRAY_UNPACKED,
    ROOTIO_WRAPPER,  // $rootio suppressed due to name()!=""
    SCOPE_MODULE,
    SCOPE_INTERFACE,
    STRUCT_PACKED,
    STRUCT_UNPACKED,
    UNION_PACKED
};

// Direction attribute for ports
enum class VerilatedTraceSigDirection : uint8_t {
    NONE,
    INPUT,
    OUTPUT,
    INOUT,
};

// Kind of signal. Similar to nettype but with a few more alternatives
enum class VerilatedTraceSigKind : uint8_t {
    PARAMETER,
    SUPPLY0,
    SUPPLY1,
    TRI,
    TRI0,
    TRI1,
    TRIAND,
    TRIOR,
    TRIREG,
    WIRE,
    VAR,
};

// Base data type of signal
enum class VerilatedTraceSigType : uint8_t {
    DOUBLE,
    INTEGER,
    BIT,
    LOGIC,
    INT,
    SHORTINT,
    LONGINT,
    BYTE,
    EVENT,
    TIME,
};

//=============================================================================
// VerilatedTraceConfig

// Simple data representing trace configuration required by generated models.
class VerilatedTraceConfig final {
public:
    const bool m_useParallel;  // Use parallel tracing

    VerilatedTraceConfig(bool useParallel)
        : m_useParallel{useParallel} {}
};

//=============================================================================
// VerilatedTraceBaseC - base class of all Verilated*C trace classes
// Internal use only

class VerilatedTraceBaseC VL_NOT_FINAL {
    bool m_modelConnected = false;  // Model connected by calling Verilated::trace()
public:
    /// True if file currently open
    virtual bool isOpen() const VL_MT_SAFE = 0;

    // internal use only
    bool modelConnected() const VL_MT_SAFE { return m_modelConnected; }
    void modelConnected(bool flag) VL_MT_SAFE { m_modelConnected = flag; }
};

//=============================================================================
// VerilatedTrace

// T_Trace is the format-specific subclass of VerilatedTrace.
// T_Buffer is the format-specific base class of VerilatedTraceBuffer.
template <typename T_Trace, typename T_Buffer>
class VerilatedTrace VL_NOT_FINAL {
public:
    using Buffer = VerilatedTraceBuffer<T_Buffer>;

    //=========================================================================
    // Generic tracing internals

    using initCb_t = void (*)(void*, T_Trace*, uint32_t);  // Type of init callbacks
    using dumpCb_t = void (*)(void*, Buffer*);  // Type of dump callbacks
    using cleanupCb_t = void (*)(void*, T_Trace*);  // Type of cleanup callbacks

private:
    // Give the buffer (both base and derived) access to the private bits
    friend T_Buffer;
    friend Buffer;

    struct CallbackRecord final {
        union {  // The callback
            const initCb_t m_initCb;
            const dumpCb_t m_dumpCb;
            const cleanupCb_t m_cleanupCb;
        };
        const uint32_t m_fidx;  // The index of the tracing function
        void* const m_userp;  // The user pointer to pass to the callback (the symbol table)
        const bool m_isLibInstance;  // Whether the callback is for a --lib-create instance
        const std::string m_name;  // The name of the instance callback is for
        const uint32_t m_nTraceCodes;  // The number of trace codes used by callback
        CallbackRecord(initCb_t cb, void* userp, bool isLibInstance, const std::string& name,
                       uint32_t nTraceCodes)
            : m_initCb{cb}
            , m_fidx{0}
            , m_userp{userp}
            , m_isLibInstance{isLibInstance}
            , m_name{name}
            , m_nTraceCodes{nTraceCodes} {}
        CallbackRecord(dumpCb_t cb, uint32_t fidx, void* userp)
            : m_dumpCb{cb}
            , m_fidx{fidx}
            , m_userp{userp}
            , m_isLibInstance{false}  // Don't care
            , m_name{}  // Don't care
            , m_nTraceCodes{0}  // Don't care
        {}
        CallbackRecord(cleanupCb_t cb, void* userp)
            : m_cleanupCb{cb}
            , m_fidx{0}
            , m_userp{userp}
            , m_isLibInstance{false}  // Don't care
            , m_name{}  // Don't care
            , m_nTraceCodes{0}  // Don't care
        {}
    };

    bool m_parallel = false;  // Use parallel tracing

    struct ParallelWorkerData final {
        const dumpCb_t m_cb;  // The callback
        void* const m_userp;  // The use pointer to pass to the callback
        Buffer* const m_bufp;  // The buffer pointer to pass to the callback
        std::atomic<bool> m_ready{false};  // The ready flag
        mutable VerilatedMutex m_mutex;  // Mutex for suspension until ready
        std::condition_variable_any m_cv;  // Condition variable for suspension
        bool m_waiting VL_GUARDED_BY(m_mutex) = false;  // Whether a thread is suspended in wait()

        void wait();

        ParallelWorkerData(dumpCb_t cb, void* userp, Buffer* bufp)
            : m_cb{cb}
            , m_userp{userp}
            , m_bufp{bufp} {}
    };

    // Passed a ParallelWorkerData*, second argument is ignored
    static void parallelWorkerTask(void*, bool);

protected:
    uint32_t* m_sigs_oldvalp = nullptr;  // Previous value store
    EData* m_sigs_enabledp = nullptr;  // Bit vector of enabled codes (nullptr = all on)
private:
    std::vector<bool> m_sigs_enabledVec;  // Staging for m_sigs_enabledp
    std::vector<CallbackRecord> m_initCbs;  // Routines to initialize tracing
    std::vector<CallbackRecord> m_constCbs;  // Routines to perform const dump
    std::vector<CallbackRecord> m_fullCbs;  // Routines to perform full dump
    std::vector<CallbackRecord> m_chgCbs;  // Routines to perform incremental dump
    std::vector<CallbackRecord> m_cleanupCbs;  // Routines to call at the end of dump
    bool m_constDump = true;  // Whether a const dump is required on the next call to 'dump'
    bool m_fullDump = true;  // Whether a full dump is required on the next call to 'dump'
    uint32_t m_nextCode = 0;  // Next code number to assign
    uint32_t m_numSignals = 0;  // Number of distinct signals
    uint32_t m_maxBits = 0;  // Number of bits in the widest signal
    void* m_initUserp = nullptr;  // The callback userp of the instance currently being initialized
    // TODO: Should keep this as a Trie, that is how it's accessed all the time.
    std::vector<std::pair<int, std::string>> m_dumpvars;  // dumpvar() entries
    double m_timeRes = 1e-9;  // Time resolution (ns/ms etc)
    double m_timeUnit = 1e-0;  // Time units (ns/ms etc)
    uint64_t m_timeLastDump = 0;  // Last time we did a dump
    bool m_didSomeDump = false;  // Did at least one dump (i.e.: m_timeLastDump is valid)
    VerilatedContext* m_contextp = nullptr;  // The context used by the traced models
    std::set<const VerilatedModel*> m_models;  // The collection of models being traced

    void addCallbackRecord(std::vector<CallbackRecord>& cbVec, CallbackRecord&& cbRec)
        VL_MT_SAFE_EXCLUDES(m_mutex);

    // Equivalent to 'this' but is of the sub-type 'T_Trace*'. Use 'self()->'
    // to access duck-typed functions to avoid a virtual function call.
    T_Trace* self() { return static_cast<T_Trace*>(this); }

    void runCallbacks(const std::vector<CallbackRecord>& cbVec);

    // Flush any remaining data for this file
    static void onFlush(void* selfp) VL_MT_UNSAFE_ONE;
    // Close the file on termination
    static void onExit(void* selfp) VL_MT_UNSAFE_ONE;

private:
    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedTrace);

protected:
    //=========================================================================
    // Internals available to format-specific implementations

    mutable VerilatedMutex m_mutex;  // Ensure dump() etc only called from single thread

    uint32_t nextCode() const { return m_nextCode; }
    uint32_t numSignals() const { return m_numSignals; }
    uint32_t maxBits() const { return m_maxBits; }
    void* initUserp() const { return m_initUserp; }
    void constDump(bool value) { m_constDump = value; }
    void fullDump(bool value) { m_fullDump = value; }

    double timeRes() const { return m_timeRes; }
    double timeUnit() const { return m_timeUnit; }
    std::string timeResStr() const;

    void traceInit() VL_MT_UNSAFE;

    // Declare new signal and return true if enabled
    bool declCode(uint32_t code, const std::string& declName, uint32_t bits);

    void closeBase();
    void flushBase();

    bool parallel() const { return m_parallel; }

    // Return last ' ' separated word. Assumes string does not end in ' '.
    static std::string lastWord(const std::string& str) {
        const size_t idx = str.rfind(' ');
        if (idx == std::string::npos) return str;
        return str.substr(idx + 1);
    }

    //=========================================================================
    // Virtual functions to be provided by the format-specific implementation

    // Called when the trace moves forward to a new time point
    virtual void emitTimeChange(uint64_t timeui) = 0;

    // These hooks are called before a full or change based dump is produced.
    // The return value indicates whether to proceed with the dump.
    virtual bool preFullDump() = 0;
    virtual bool preChangeDump() = 0;

    // Trace buffer management
    virtual Buffer* getTraceBuffer(uint32_t fidx) = 0;
    virtual void commitTraceBuffer(Buffer*) = 0;

    // Configure sub-class
    virtual void configure(const VerilatedTraceConfig&) = 0;

public:
    //=========================================================================
    // External interface to client code

    explicit VerilatedTrace();
    ~VerilatedTrace();

    // Set time units (s/ms, defaults to ns)
    void set_time_unit(const char* unitp) VL_MT_SAFE;
    void set_time_unit(const std::string& unit) VL_MT_SAFE;
    // Set time resolution (s/ms, defaults to ns)
    void set_time_resolution(const char* unitp) VL_MT_SAFE;
    void set_time_resolution(const std::string& unit) VL_MT_SAFE;
    // Set variables to dump, using $dumpvars format
    // If level = 0, dump everything and hier is then ignored
    void dumpvars(int level, const std::string& hier) VL_MT_SAFE;

    // Call
    void dump(uint64_t timeui) VL_MT_SAFE_EXCLUDES(m_mutex);

    //=========================================================================
    // Internal interface to Verilator generated code

    //=========================================================================
    // Non-hot path internal interface to Verilator generated code

    void addModel(VerilatedModel*) VL_MT_SAFE_EXCLUDES(m_mutex);
    void addInitCb(initCb_t cb, void* userp, const std::string& name, bool isLibInstance,
                   uint32_t nTraceCodes) VL_MT_SAFE;
    void addConstCb(dumpCb_t cb, uint32_t fidx, void* userp) VL_MT_SAFE;
    void addFullCb(dumpCb_t cb, uint32_t fidx, void* userp) VL_MT_SAFE;
    void addChgCb(dumpCb_t cb, uint32_t fidx, void* userp) VL_MT_SAFE;
    void addCleanupCb(cleanupCb_t cb, void* userp) VL_MT_SAFE;
    void initLib(const std::string& name) VL_MT_UNSAFE;
};

//=============================================================================
// VerilatedTraceBuffer

// T_Buffer is the format-specific base class of VerilatedTraceBuffer.
// The format-specific hot-path methods use duck-typing via T_Buffer for performance.
template <typename T_Buffer>
class VerilatedTraceBuffer VL_NOT_FINAL : public T_Buffer {
protected:
    // Type of the owner trace file
    using Trace = typename std::remove_cv<
        typename std::remove_reference<decltype(T_Buffer::m_owner)>::type>::type;

    static_assert(std::has_virtual_destructor<T_Buffer>::value, "");
    static_assert(std::is_base_of<VerilatedTrace<Trace, T_Buffer>, Trace>::value, "");

    friend Trace;  // Give the trace file access to the private bits
    friend std::default_delete<VerilatedTraceBuffer<T_Buffer>>;

    uint32_t* const m_sigs_oldvalp;  // Previous value store
    EData* const m_sigs_enabledp;  // Bit vector of enabled codes (nullptr = all on)

    explicit VerilatedTraceBuffer(Trace& owner);
    ~VerilatedTraceBuffer() override = default;

public:
    //=========================================================================
    // Hot path internal interface to Verilator generated code

    // Implementation note: We rely on the following duck-typed implementations
    // in the derived class T_Derived. These emit* functions record a format-
    // specific trace entry. Normally one would use pure virtual functions for
    // these here, but we cannot afford dynamic dispatch for calling these as
    // this is very hot code during tracing.

    // duck-typed void emitBit(uint32_t code, CData newval) = 0;
    // duck-typed void emitCData(uint32_t code, CData newval, int bits) = 0;
    // duck-typed void emitSData(uint32_t code, SData newval, int bits) = 0;
    // duck-typed void emitIData(uint32_t code, IData newval, int bits) = 0;
    // duck-typed void emitQData(uint32_t code, QData newval, int bits) = 0;
    // duck-typed void emitWData(uint32_t code, const WData* newvalp, int bits) = 0;
    // duck-typed void emitDouble(uint32_t code, double newval) = 0;

    VL_ATTR_ALWINLINE uint32_t* oldp(uint32_t code) { return m_sigs_oldvalp + code; }

    // Write to previous value buffer value and emit trace entry.
    void fullBit(uint32_t* oldp, CData newval);
    void fullLogic(uint32_t* oldp, CData newval, CData newvalXZ);
    void fullCData(uint32_t* oldp, CData newval, int bits);
    void fullFourstateCData(uint32_t* oldp, CData newval, CData newvalXZ, int bits);
    void fullSData(uint32_t* oldp, SData newval, int bits);
    void fullFourstateSData(uint32_t* oldp, SData newval, SData newvalXZ, int bits);
    void fullIData(uint32_t* oldp, IData newval, int bits);
    void fullFourstateIData(uint32_t* oldp, IData newval, IData newvalXZ, int bits);
    void fullQData(uint32_t* oldp, QData newval, int bits);
    void fullFourstateQData(uint32_t* oldp, QData newval, QData newvalXZ, int bits);
    void fullWData(uint32_t* oldp, const WData* newvalp, int bits);
    void fullFourstateWData(uint32_t* oldp, const WData* newvalp, const WData* newvalXZp,
                            int bits);
    void fullDouble(uint32_t* oldp, double newval);
    void fullEvent(uint32_t* oldp, const VlEventBase* newvalp);
    void fullEventTriggered(uint32_t* oldp);

    // Check previous dumped value of signal. If changed, then emit trace entry
    VL_ATTR_ALWINLINE void chgBit(uint32_t* oldp, CData newval) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(oldp, newval);
    }
    VL_ATTR_ALWINLINE void chgLogic(uint32_t* oldp, CData newval, CData newvalXZ) {
        CData* oldcp = reinterpret_cast<CData*>(oldp);
        const uint32_t diff = (oldcp[0] ^ newval) | (oldcp[1] ^ newvalXZ);
        if (VL_UNLIKELY(diff)) fullLogic(oldp, newval, newvalXZ);
    }
    VL_ATTR_ALWINLINE void chgCData(uint32_t* oldp, CData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullCData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgFourstateCData(uint32_t* oldp, CData newval, CData newvalXZ,
                                             int bits) {
        CData* oldcp = reinterpret_cast<CData*>(oldp);
        const uint32_t diff = (oldcp[0] ^ newval) | (oldcp[1] ^ newvalXZ);
        if (VL_UNLIKELY(diff)) fullFourstateCData(oldp, newval, newvalXZ, bits);
    }
    VL_ATTR_ALWINLINE void chgSData(uint32_t* oldp, SData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullSData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgFourstateSData(uint32_t* oldp, SData newval, SData newvalXZ,
                                             int bits) {
        SData* oldcp = reinterpret_cast<SData*>(oldp);
        const uint32_t diff = (oldcp[0] ^ newval) | (oldcp[1] ^ newvalXZ);
        if (VL_UNLIKELY(diff)) fullFourstateSData(oldp, newval, newvalXZ, bits);
    }
    VL_ATTR_ALWINLINE void chgIData(uint32_t* oldp, IData newval, int bits) {
        const uint32_t diff = *oldp ^ newval;
        if (VL_UNLIKELY(diff)) fullIData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgFourstateIData(uint32_t* oldp, IData newval, IData newvalXZ,
                                             int bits) {
        IData* oldcp = reinterpret_cast<IData*>(oldp);
        const uint32_t diff = (oldcp[0] ^ newval) | (oldcp[1] ^ newvalXZ);
        if (VL_UNLIKELY(diff)) fullFourstateIData(oldp, newval, newvalXZ, bits);
    }
    VL_ATTR_ALWINLINE void chgQData(uint32_t* oldp, QData newval, int bits) {
        QData old;
        std::memcpy(&old, oldp, sizeof(old));
        const uint64_t diff = old ^ newval;
        if (VL_UNLIKELY(diff)) fullQData(oldp, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgFourstateQData(uint32_t* oldp, QData newval, QData newvalXZ,
                                             int bits) {
        QData* oldcp = reinterpret_cast<QData*>(oldp);
        const uint32_t diff = (oldcp[0] ^ newval) | (oldcp[1] ^ newvalXZ);
        if (VL_UNLIKELY(diff)) fullFourstateQData(oldp, newval, newvalXZ, bits);
    }
    VL_ATTR_ALWINLINE void chgWData(uint32_t* oldp, const WData* newvalp, int bits) {
        for (int i = 0; i < VL_WORDS_I(bits); ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newvalp[i])) {
                fullWData(oldp, newvalp, bits);
                return;
            }
        }
    }
    VL_ATTR_ALWINLINE void chgFourstateWData(uint32_t* oldp, const WData* newvalp,
                                             const WData* newvalXZp, int bits) {
        for (int i = 0; i < VL_WORDS_I(bits); ++i) {
            const int oldIdx = i << 1;
            if (VL_UNLIKELY((oldp[oldIdx] ^ newvalp[i]) | (oldp[oldIdx | 1] ^ newvalXZp[i]))) {
                fullFourstateWData(oldp, newvalp, newvalXZp, bits);
                return;
            }
        }
    }
    VL_ATTR_ALWINLINE void chgEvent(uint32_t* oldp, const VlEventBase* newvalp) {
        if (newvalp->isTriggered()) fullEvent(oldp, newvalp);
    }
    VL_ATTR_ALWINLINE void chgEventTriggered(uint32_t* oldp) { fullEventTriggered(oldp); }
    VL_ATTR_ALWINLINE void chgDouble(uint32_t* oldp, double newval) {
        double old;  // LCOV_EXCL_LINE  // lcov bug
        std::memcpy(&old, oldp, sizeof(old));
        if (VL_UNLIKELY(old != newval)) fullDouble(oldp, newval);
    }
};

#endif  // guard
