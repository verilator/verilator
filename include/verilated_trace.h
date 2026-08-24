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

#include "verilated_rtmd.h"

#include <atomic>
#include <condition_variable>
#include <map>
#include <memory>
#include <string>
#include <tuple>
#include <type_traits>
#include <vector>

// clang-format on

template <typename T_Buffer>
class VerilatedTraceBuffer;

//=============================================================================
// Helpers for the formats

// The number of bits in a value of the type, for --trace-max-width
inline uint64_t vlTraceTotalWidth(const VlRtmdDataType& dtype) {
    if (dtype.isUnpackedArray()) return dtype.elements() * vlTraceTotalWidth(dtype.elemType());
    if (dtype.isUnpackedStruct()) {
        uint64_t width = 0;
        for (uint32_t i = 0; i < dtype.memberCount(); ++i) {
            width += vlTraceTotalWidth(dtype.memberType(i));
        }
        return width;
    }
    return dtype.width();
}

// Whether a type is a one dimensional packed array of single bits, e.g. 'logic [7:0]'
inline bool vlTraceIsBitVector(const VlRtmdDataType& dtype) {
    if (!dtype.isPackedArray()) return false;
    const VlRtmdDataType elemType = dtype.elemType();
    return elemType.isAtom() && elemType.width() == 1;
}

// The range of a traced value as [msb:lsb]: the declared range of a vector of bits, otherwise
// [width-1:0]. Return whether to show it, i.e. false for a scalar, an event or a real.
inline bool vlTraceRange(const VlRtmdDataType& dtype, int& msb, int& lsb) {
    const VlRtmdDataType::StorageKind storage = dtype.storageKind();
    if (storage == VlRtmdDataType::StorageKind::EVENT) {
        msb = 0;
        lsb = 0;
        return false;
    }
    if (storage == VlRtmdDataType::StorageKind::DOUBLE) {
        msb = 63;
        lsb = 0;
        return false;
    }
    const VlRtmdDataType base = dtype.isEnum() ? dtype.enumBase() : dtype;
    if (vlTraceIsBitVector(base)) {
        msb = base.left();
        lsb = base.right();
        return true;
    }
    msb = static_cast<int>(dtype.width()) - 1;
    lsb = 0;
    return msb != 0;
}

//=============================================================================
// VerilatedTraceBaseC - base class of all Verilated*C trace classes
// Internal use only

class VerilatedTraceBaseC VL_NOT_FINAL {
public:
    /// True if file currently open
    virtual bool isOpen() const VL_MT_SAFE = 0;

    // The context being traced, held by the trace file
    virtual VerilatedContext* contextp() const = 0;
    virtual void contextp(VerilatedContext* contextp) = 0;
};

//=============================================================================
// VerilatedTrace

// T_Trace is the format-specific subclass of VerilatedTrace.
// T_Buffer is the format-specific base class of VerilatedTraceBuffer.
template <typename T_Trace, typename T_Buffer>
class VerilatedTrace VL_NOT_FINAL : public VlRtmdHierListener {
public:
    using Buffer = VerilatedTraceBuffer<T_Buffer>;
    using StorageKind = VlRtmdDataType::StorageKind;

private:
    // Give the buffer (both base and derived) access to the private bits
    friend T_Buffer;
    friend Buffer;

    // One whole value to dump
    struct Whole final {
        const void* m_datap;  // Address of the value
        uint32_t m_code;  // Trace code
        uint32_t m_bits;  // Width of the value
    };
    // One slice of a packed value to dump
    struct Slice final {
        const void* m_datap;  // Address of the packed value it is a slice of
        uint32_t m_code;  // Trace code
        uint32_t m_bits;  // Width of the slice
        uint32_t m_lsb;  // Bit offset of the slice within the packed value
        uint32_t m_valueBits;  // Width of the packed value
    };
    // The values of a group
    struct Group final {
        StorageKind m_storage;  // How the values are stored
        StorageKind m_valueStorage;  // How the packed values of its slices are stored
        std::vector<Whole> m_wholes;  // The whole values
        std::vector<Slice> m_slices;  // The slices of packed values
    };
    // A contiguous range of 'm_groupVec', dumped by one thread, see 'dump'
    struct Shard final {
        size_t m_begin = 0;  // Index of its first group
        size_t m_end = 0;  // Index after its last group
        std::vector<EData> m_wideSlice;  // Wide slices are extracted here when dumped
    };
    // Dumping a shard on a worker thread
    struct ParallelWorkerData final {
        VerilatedTrace& m_trace;  // The trace file being dumped
        Shard& m_shard;  // The shard to dump
        Buffer* const m_bufp;  // The buffer to dump it into
        const bool m_full;  // Dump all values, not only the changed ones
        std::atomic<bool> m_ready{false};  // The ready flag
        mutable VerilatedMutex m_mutex;  // Mutex for suspension until ready
        std::condition_variable_any m_cv;  // Condition variable for suspension
        bool m_waiting VL_GUARDED_BY(m_mutex) = false;  // Whether a thread is suspended in wait()

        void wait();

        ParallelWorkerData(VerilatedTrace& trace, Shard& shard, Buffer* bufp, bool full)
            : m_trace{trace}
            , m_shard{shard}
            , m_bufp{bufp}
            , m_full{full} {}
    };

    // Passed a ParallelWorkerData*
    static void parallelWorkerTask(void*);

    uint32_t* m_sigs_oldvalp = nullptr;  // Previous value store
    bool m_fullDump = true;  // Whether a full dump is required on the next call to 'dump'
    uint32_t m_nextCode = 0;  // Next code number to assign
    uint32_t m_maxBits = 0;  // Number of bits in the widest signal
    // TODO: Should keep this as a Trie, that is how it's accessed all the time.
    std::vector<std::pair<int, std::string>> m_dumpvars;  // dumpvar() entries
    double m_timeRes = 1e-9;  // Time resolution (ns/ms etc)
    uint64_t m_timeLastDump = 0;  // Last time we did a dump
    bool m_didSomeDump = false;  // Did at least one dump (i.e.: m_timeLastDump is valid)
    VerilatedContext* m_contextp = nullptr;  // The context being traced
    std::vector<VerilatedModel*> m_modelps;  // The traced models

    // The values to dump, grouped by activity set and how to dump them, in that order
    std::vector<std::pair<VlRtmdActSet, Group>> m_groupVec;
    // The groups dumped by each thread, a single one unless dumping in parallel
    std::vector<Shard> m_shards;

    // State while declaring the signals
    // The values to dump, grouped by activity set and how to dump them, moved to 'm_groupVec'
    // when all declared. Keyed by how the values, and the packed values of slices, are stored.
    std::map<VlRtmdActSet, std::map<std::pair<StorageKind, StorageKind>, Group>> m_groupMap;
    // Trace code of each (address, bit offset, width), shared by aliases of the same value. The
    // width is only needed for packed unions, whose members split differently share an address
    // and bit offset, e.g. a vector member and the lowest member of a struct member.
    std::map<std::tuple<const void*, uint32_t, uint32_t>, uint32_t> m_codes;
    bool m_namedRoot = false;  // The root model being declared has a name
    uint32_t m_packedBits = 0;  // Width of the outermost packed value being split
    // The trace options the root model being declared was built with, see VlRtmd
    bool m_traceStructs = false;
    bool m_traceUnderscore = false;
    uint32_t m_traceMaxArray = 0;
    uint32_t m_traceMaxWidth = 0;

    // Equivalent to 'this' but is of the sub-type 'T_Trace*'. Use 'self()->'
    // to access duck-typed functions to avoid a virtual function call.
    T_Trace* self() { return static_cast<T_Trace*>(this); }

    // Flush any remaining data for this file. This calls 'flush' on the derived class, which must
    // then get any mutex. 'selfp' is 'this', so the destructor can unregister it.
    static void onFlush(void* selfp) VL_MT_UNSAFE_ONE {
        static_cast<VerilatedTrace*>(selfp)->self()->flush();
    }
    // Close the file on termination. This calls 'close' on the derived class, which must then get
    // any mutex.
    static void onExit(void* selfp) VL_MT_UNSAFE_ONE {
        static_cast<VerilatedTrace*>(selfp)->self()->close();
    }

    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedTrace);

protected:
    //=========================================================================
    // Internals available to format-specific implementations

    mutable VerilatedMutex m_mutex;  // Ensure dump() etc only called from single thread

    void fullDump(bool value) { m_fullDump = value; }

    double timeRes() const { return m_timeRes; }
    std::string timeResStr() const;

    void traceInit() VL_MT_UNSAFE;

    bool parallel() const { return m_shards.size() > 1; }

private:
    //=========================================================================
    // Non-hot path internals

    // Whether a signal or hierarchy level is not traced, as it has a leading underscore, unless
    // --trace-underscore
    bool hidden(const char* namep) const { return !m_traceUnderscore && namep[0] == '_'; }

    // Whether an unpacked array has more elements than --trace-max-array allows, counting the
    // directly nested unpacked arrays as one array, so it is not traced
    bool tooManyElements(const VlRtmdDataType& dtype) const {
        if (!m_traceMaxArray || !dtype.isUnpackedArray()) return false;
        uint64_t elements = 1;
        for (VlRtmdDataType arrayType = dtype;; arrayType = arrayType.elemType()) {
            elements *= arrayType.elements();
            if (!arrayType.elemType().isUnpackedArray()) break;
        }
        return elements > m_traceMaxArray;
    }
    // Whether to trace a value by its components. Unpacked arrays and structs always are. Packed
    // values only with --trace-structs, except vectors of bits, which are traced whole.
    bool splitSignal(const VlRtmdDataType& dtype) const {
        if (dtype.isUnpackedArray() || dtype.isUnpackedStruct()) return true;
        if (!m_traceStructs) return false;
        if (dtype.isPackedArray()) return !vlTraceIsBitVector(dtype);
        return dtype.isPackedStruct() || dtype.isPackedUnion();
    }

    // Whether the signal 'namep' in the current hierarchy level is selected by 'dumpvars'
    bool dumpvarsSelected(const char* namep) const;
    // Declare a value reported by 'onSignal' or 'onComponent', which is not split further
    void addSignal(const char* namep, const VlRtmdSignalType& sigType, const VlRtmdDataType& dtype,
                   const VlRtmdActSet& actSet, const void* datap, uint32_t lsb) VL_MT_UNSAFE;

    //=========================================================================
    // Hot path internals

    // Dump the groups of a shard, in full, or only those that might have changed
    template <bool T_Full>
    void dumpShard(Buffer* bufp, Shard& shard) VL_MT_UNSAFE;
    // Dump the values of a group, in full, or only if changed, dispatching on how they are stored.
    // Wide slices are extracted into 'wideSlicep'.
    template <bool T_Full>
    void dumpGroupDispatch(Buffer* bufp, const Group& group, EData* wideSlicep) VL_MT_UNSAFE;
    // Dump the whole values of a group, stored as 'T_Storage', in full, or only if changed
    template <bool T_Full, StorageKind T_Storage>
    void dumpGroupWholes(Buffer* bufp, const Group& group) VL_MT_UNSAFE;
    // Dump the slices of a group, stored as 'T_Storage', in full, or only if changed,
    // dispatching on how their packed values are stored
    template <bool T_Full, StorageKind T_Storage>
    void dumpGroupSlices(Buffer* bufp, const Group& group, EData* wideSlicep) VL_MT_UNSAFE;
    // Dump the slices of a group, of packed values stored as 'T_Value'
    template <bool T_Full, StorageKind T_Storage, StorageKind T_Value>
    void dumpSlices(Buffer* bufp, const Group& group, EData* wideSlicep) VL_MT_UNSAFE;
    // The wider of two storage kinds. A slice is never wider than its packed value.
    static constexpr StorageKind wider(StorageKind a, StorageKind b) { return a < b ? b : a; }
    // Dump one value at 'datap', stored as 'T_Storage', in full, or only if changed
    template <bool T_Full, StorageKind T_Storage>
    void dumpValue(Buffer* bufp, uint32_t code, const void* datap, int bits) VL_MT_UNSAFE;

    //=========================================================================
    // VlRtmdHierListener callbacks, building the hierarchy

    bool enterRoot(const VerilatedModel& model) override final {
        // Only add root scope if the model has a name
        m_namedRoot = *model.hierName();
        // Partitions are built with the same trace options as their root
        const VlRtmd* const rtmdp = model.rtmd();
        m_traceStructs = rtmdp->m_opt.m_traceStructs;
        m_traceUnderscore = rtmdp->m_opt.m_traceUnderscore;
        m_traceMaxArray = rtmdp->m_opt.m_traceMaxArray;
        m_traceMaxWidth = rtmdp->m_opt.m_traceMaxWidth;
        if (m_namedRoot) openRoot(model.hierName());
        return true;
    }
    void exitRoot(const VerilatedModel&) override final {
        if (m_namedRoot) closeRoot();
    }
    bool enterInstance(InstanceKind kind, const char* namep, const char* modNamep,
                       HierFlags flags) override final {
        if (!flags.hasTracedSignals()) return false;  // Nothing to trace in it
        if (hidden(namep)) return false;
        openInstance(kind, namep, modNamep);
        return true;
    }
    void exitInstance(InstanceKind, const char*, const char*, HierFlags) override final {
        closeInstance();
    }
    bool enterIfaceRef(const char* namep, const char* modNamep, HierFlags flags) override final {
        if (!flags.hasTracedSignals()) return false;  // Nothing to trace in it
        if (hidden(namep)) return false;
        openIfaceRef(namep, modNamep);
        return true;
    }
    void exitIfaceRef(const char*, const char*, HierFlags) override final {  //
        closeIfaceRef();
    }
    bool enterScope(ScopeKind kind, const char* namep, HierFlags flags) override final {
        if (!flags.hasTracedSignals()) return false;  // Nothing to trace in it
        if (hidden(namep)) return false;
        // The root IO of a named model is in the root scope, otherwise in a scope of its own
        if (kind == ScopeKind::ROOTIO && m_namedRoot) return true;
        openScope(kind, namep);
        return true;
    }
    void exitScope(ScopeKind kind, const char*, HierFlags) override final {
        if (kind == ScopeKind::ROOTIO && m_namedRoot) return;
        closeScope();
    }

    bool onSignal(const char* namep, const VlRtmdSignalType& sigType, const VlRtmdDataType& dtype,
                  const VlRtmdActSet& actSet, const void* datap,
                  SignalFlags flags) override final {
        if (!flags.isTraced()) return false;
        if (hidden(namep)) return false;
        if (m_traceMaxWidth && vlTraceTotalWidth(dtype) > m_traceMaxWidth) return false;
        if (tooManyElements(dtype)) return false;
        if (!dumpvarsSelected(namep)) return false;
        if (splitSignal(dtype)) {
            // The components of a packed value are slices of it
            if (!dtype.isUnpackedArray() && !dtype.isUnpackedStruct()) {
                m_packedBits = dtype.width();
            }
            return true;
        }
        addSignal(namep, sigType, dtype, actSet, datap, NOLSB);
        return false;
    }

    void enterUnpackedArray(const char* namep, const VlRtmdDataType& dtype) override final {
        openUnpackedArray(namep, dtype.left(), dtype.right());
    }
    void exitUnpackedArray(const char*, const VlRtmdDataType&) override final {
        closeUnpackedArray();
    }
    void enterUnpackedStruct(const char* namep, const VlRtmdDataType& dtype) override final {
        openUnpackedStruct(namep, dtype.memberCount());
    }
    void exitUnpackedStruct(const char*, const VlRtmdDataType&) override final {
        closeUnpackedStruct();
    }
    void enterPackedArray(const char* namep, const VlRtmdDataType& dtype) override final {
        openPackedArray(namep, dtype.left(), dtype.right());
    }
    void exitPackedArray(const char*, const VlRtmdDataType&) override final {  //
        closePackedArray();
    }
    void enterPackedStruct(const char* namep, const VlRtmdDataType& dtype) override final {
        openPackedStruct(namep, dtype.memberCount());
    }
    void exitPackedStruct(const char*, const VlRtmdDataType&) override final {
        closePackedStruct();
    }
    void enterPackedUnion(const char* namep, const VlRtmdDataType& dtype) override final {
        openPackedUnion(namep, dtype.memberCount());
    }
    void exitPackedUnion(const char*, const VlRtmdDataType&) override final {  //
        closePackedUnion();
    }

    bool onComponent(const char* namep, const VlRtmdSignalType& sigType,
                     const VlRtmdDataType& dtype, const VlRtmdActSet& actSet, const void* datap,
                     uint32_t lsb) override final {
        if (tooManyElements(dtype)) return false;
        if (splitSignal(dtype)) {
            // The components of the outermost packed value are slices of it
            if (lsb == NOLSB && !dtype.isUnpackedArray() && !dtype.isUnpackedStruct()) {
                m_packedBits = dtype.width();
            }
            return true;
        }
        addSignal(namep, sigType, dtype, actSet, datap, lsb);
        return false;
    }

protected:
    //=========================================================================
    // Virtual functions to be provided by the format - declarations

    // Declare a hierarchy level, the signals within it, and enums. The open and close hooks are
    // called virtually. 'declareEnum' and 'declareSignal' are called through 'self()', and the
    // overrides are final, so these calls are resolved statically.
    // Open and close the root of a model. Not called for a model with an empty name, whose
    // contents are at the top level.
    virtual void openRoot(const char* namep) = 0;
    virtual void closeRoot() = 0;
    // Open and close an instance of module 'modNamep'
    virtual void openInstance(InstanceKind kind, const char* namep, const char* modNamep) = 0;
    virtual void closeInstance() = 0;
    // Open and close an interface reference, to an instance of interface 'modNamep'
    virtual void openIfaceRef(const char* namep, const char* modNamep) = 0;
    virtual void closeIfaceRef() = 0;
    // Open and close a scope within an instance
    virtual void openScope(ScopeKind kind, const char* namep) = 0;
    virtual void closeScope() = 0;
    // Open and close an unpacked array, holding the elements declared within
    virtual void openUnpackedArray(const char* namep, int left, int right) = 0;
    virtual void closeUnpackedArray() = 0;
    // Open and close an unpacked struct, holding the members declared within
    virtual void openUnpackedStruct(const char* namep, uint32_t memberCount) = 0;
    virtual void closeUnpackedStruct() = 0;
    // Open and close a packed array, holding the elements declared within
    virtual void openPackedArray(const char* namep, int left, int right) = 0;
    virtual void closePackedArray() = 0;
    // Open and close a packed struct or union, holding the members declared within
    virtual void openPackedStruct(const char* namep, uint32_t memberCount) = 0;
    virtual void closePackedStruct() = 0;
    virtual void openPackedUnion(const char* namep, uint32_t memberCount) = 0;
    virtual void closePackedUnion() = 0;

    // Declare an enum type, given by its data type handle
    virtual void declareEnum(const VlRtmdDataType& dtype) = 0;
    // Declare a signal or a component of one, traced with the codes from 'code', one per word.
    // 'sigType' is the signal's declaration, 'dtype' the type of the value. An enum type was
    // declared with 'declareEnum' already.
    virtual void declareSignal(uint32_t code, const char* namep, const VlRtmdSignalType& sigType,
                               const VlRtmdDataType& dtype)
        = 0;

    //=========================================================================
    // Virtual functions to be provided by the format - dumping

    // Called when the trace moves forward to a new time point
    virtual void emitTimeChange(uint64_t timeui) = 0;

    // These hooks are called before a full or change based dump is produced.
    // The return value indicates whether to proceed with the dump.
    virtual bool preFullDump() = 0;
    virtual bool preChangeDump() = 0;

    // Trace buffer management
    virtual Buffer* getTraceBuffer() = 0;
    virtual void commitTraceBuffer(Buffer*) = 0;

    // Whether the format can dump in parallel, into separate buffers committed in order
    virtual bool parallelCapable() const { return false; }

public:
    //=========================================================================
    // External interface to client code

    explicit VerilatedTrace() {
        set_time_resolution(Verilated::threadContextp()->timeprecisionString());
    }
    ~VerilatedTrace() {
        if (m_sigs_oldvalp) VL_DO_CLEAR(delete[] m_sigs_oldvalp, m_sigs_oldvalp = nullptr);
        Verilated::removeFlushCb(onFlush, this);
        Verilated::removeExitCb(onExit, this);
    }

    // The context being traced, see VerilatedTraceBaseC
    VerilatedContext* contextp() const { return m_contextp; }
    void contextp(VerilatedContext* contextp) { m_contextp = contextp; }

    // Set time units (s/ms, defaults to ns). Ignored, the time resolution is used for the trace.
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
    friend VerilatedTrace<Trace, T_Buffer>;  // Calls full* and chg* from dumpValue
    friend std::default_delete<VerilatedTraceBuffer<T_Buffer>>;

    uint32_t* const m_sigs_oldvalp;  // Previous value store

    explicit VerilatedTraceBuffer(Trace& owner);
    ~VerilatedTraceBuffer() override = default;

    //=========================================================================
    // Hot path internal interface to VerilatedTrace::dumpValue

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
    // duck-typed void emitWData(uint32_t code, WDataInP newval, int bits) = 0;
    // duck-typed void emitDouble(uint32_t code, double newval) = 0;

    // Write to previous value buffer value and emit trace entry.
    void fullBit(uint32_t code, CData newval);
    void fullCData(uint32_t code, CData newval, int bits);
    void fullSData(uint32_t code, SData newval, int bits);
    void fullIData(uint32_t code, IData newval, int bits);
    void fullQData(uint32_t code, QData newval, int bits);
    void fullWData(uint32_t code, WDataInP newval, int bits);
    void fullDouble(uint32_t code, double newval);
    void fullEvent(uint32_t code, const VlEventBase* newvalp);

    // Check previous dumped value of signal. If changed, then emit trace entry
    VL_ATTR_ALWINLINE void chgBit(uint32_t code, CData newval) {
        const uint32_t diff = m_sigs_oldvalp[code] ^ newval;
        if (VL_UNLIKELY(diff)) fullBit(code, newval);
    }
    VL_ATTR_ALWINLINE void chgCData(uint32_t code, CData newval, int bits) {
        const uint32_t diff = m_sigs_oldvalp[code] ^ newval;
        if (VL_UNLIKELY(diff)) fullCData(code, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgSData(uint32_t code, SData newval, int bits) {
        const uint32_t diff = m_sigs_oldvalp[code] ^ newval;
        if (VL_UNLIKELY(diff)) fullSData(code, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgIData(uint32_t code, IData newval, int bits) {
        const uint32_t diff = m_sigs_oldvalp[code] ^ newval;
        if (VL_UNLIKELY(diff)) fullIData(code, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgQData(uint32_t code, QData newval, int bits) {
        QData old;
        std::memcpy(&old, m_sigs_oldvalp + code, sizeof(old));
        const uint64_t diff = old ^ newval;
        if (VL_UNLIKELY(diff)) fullQData(code, newval, bits);
    }
    VL_ATTR_ALWINLINE void chgWData(uint32_t code, WDataInP newval, int bits) {
        const uint32_t* const oldp = m_sigs_oldvalp + code;
        for (int i = 0; i < (bits + 31) / 32; ++i) {
            if (VL_UNLIKELY(oldp[i] ^ newval[i])) {
                fullWData(code, newval, bits);
                return;
            }
        }
    }
    VL_ATTR_ALWINLINE void chgEvent(uint32_t code, const VlEventBase* newvalp) {
        if (newvalp->isTriggered()) fullEvent(code, newvalp);
    }
    VL_ATTR_ALWINLINE void chgDouble(uint32_t code, double newval) {
        double old;  // LCOV_EXCL_LINE  // lcov bug
        std::memcpy(&old, m_sigs_oldvalp + code, sizeof(old));
        if (VL_UNLIKELY(old != newval)) fullDouble(code, newval);
    }
};

#endif  // guard
