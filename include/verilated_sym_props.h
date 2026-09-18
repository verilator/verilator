// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilated symbol inspection header
///
/// This file is for inclusion by internal files that need to inspect
/// specific symbols.  Applications typically use the VPI instead.
///
/// User wrapper code wanting to inspect the symbol table should use
/// verilated_syms.h instead.
///
//*************************************************************************
// These classes are thread safe, and read only.

#ifndef VERILATOR_VERILATED_SYM_PROPS_H_
#define VERILATOR_VERILATED_SYM_PROPS_H_

#include "verilatedos.h"

#include "verilated.h"

#include <cstring>
#include <vector>

//===========================================================================
// Verilator range
// Thread safety: Assume is constructed only with model, then any number of readers

// See also V3Ast::VNumRange
class VerilatedRange final {
    int m_left = 0;
    int m_right = 0;

protected:
    friend class VerilatedVarProps;
    friend class VerilatedScope;
    VerilatedRange() = default;
    void init(int left, int right) {
        m_left = left;
        m_right = right;
    }

public:
    VerilatedRange(int left, int right)
        : m_left{left}
        , m_right{right} {}
    ~VerilatedRange() = default;
    int left() const VL_PURE { return m_left; }
    int right() const VL_PURE { return m_right; }
    int low() const VL_PURE { return (m_left < m_right) ? m_left : m_right; }
    int high() const VL_PURE { return (m_left > m_right) ? m_left : m_right; }
    int elements() const VL_PURE {
        return (VL_LIKELY(m_left >= m_right) ? (m_left - m_right + 1) : (m_right - m_left + 1));
    }
    int increment() const VL_PURE { return (m_left >= m_right) ? 1 : -1; }
};

//===========================================================================
// Verilator variable
// Thread safety: Assume is constructed only with model, then any number of readers

class VerilatedVarProps VL_NOT_FINAL {
    // TYPES
    static constexpr uint32_t MAGIC = 0xddc4f829UL;
    // MEMBERS
    const uint32_t m_magic;  // Magic number
    const VerilatedVarType m_vltype;  // Data type
    const VerilatedVarFlags m_vlflags;  // Direction
    const uint32_t m_entSize;  // Element size in bytes, or 0 to derive from type
    std::vector<VerilatedRange> m_unpacked;  // Unpacked array ranges
    std::vector<VerilatedRange> m_packed;  // Packed array ranges
    VerilatedRange m_packedDpi;  // Flattened packed array range
    void initUnpacked(int udims, const int* ulims) {
        for (int i = 0; i < udims; ++i) {
            const int uleft = ulims ? ulims[2 * i + 0] : 0;
            const int uright = ulims ? ulims[2 * i + 1] : 0;
            m_unpacked.emplace_back(uleft, uright);
        }
    }
    void initPacked(int pdims, const int* plims) {
        int packedSize = 1;
        for (int i = 0; i < pdims; ++i) {
            const int pleft = plims ? plims[2 * i + 0] : 0;
            const int pright = plims ? plims[2 * i + 1] : 0;
            m_packed.emplace_back(pleft, pright);
            packedSize *= abs(pleft - pright) + 1;
        }
        if (pdims == 1) {
            // Preserve packed array range if the packed component is 1-D
            m_packedDpi = m_packed.front();
        } else {
            m_packedDpi = VerilatedRange{packedSize - 1, 0};
        }
    }
    // CONSTRUCTORS
protected:
    friend class VerilatedScope;
    VerilatedVarProps(VerilatedVarType vltype, VerilatedVarFlags vlflags, int udims, int pdims,
                      uint32_t entSize = 0)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags{vlflags}
        , m_entSize{entSize} {
        // Only preallocate the ranges
        initUnpacked(udims, nullptr);
        initPacked(pdims, nullptr);
    }

public:
    class Unpacked {};
    // Without packed
    VerilatedVarProps(VerilatedVarType vltype, int vlflags)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_entSize{0} {}

    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Unpacked, int udims, const int* ulims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_entSize{0} {
        initUnpacked(udims, ulims);
    }
    // With packed
    class Packed {};
    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Packed, int pdims, const int* plims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_entSize{0} {
        initPacked(pdims, plims);
    }
    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Unpacked, int udims, const int* ulims,
                      Packed, int pdims, const int* plims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_entSize{0} {
        initUnpacked(udims, ulims);
        initPacked(pdims, plims);
    }

    ~VerilatedVarProps() = default;
    // METHODS
    bool magicOk() const { return m_magic == MAGIC; }
    VerilatedVarType vltype() const VL_MT_SAFE { return m_vltype; }
    VerilatedVarFlags vldir() const {
        return static_cast<VerilatedVarFlags>(static_cast<int>(m_vlflags) & VLVF_MASK_DIR);
    }
    // Inline: VerilatedVar::datapRefresh's copy/fold path calls totalSize() per VPI access.
    uint32_t entSize() const VL_MT_SAFE {
        if (m_entSize) return m_entSize;
        switch (vltype()) {
        case VLVT_PTR: return sizeof(void*);
        case VLVT_UINT8: return sizeof(CData);
        case VLVT_UINT16: return sizeof(SData);
        case VLVT_UINT32: return sizeof(IData);
        case VLVT_UINT64: return sizeof(QData);
        case VLVT_WDATA: return VL_WORDS_I(entBits()) * sizeof(IData);
        default: return 0;  // LCOV_EXCL_LINE
        }
    }
    uint32_t entBits() const VL_MT_SAFE {
        uint32_t bits = 1;
        for (auto it : m_packed) bits *= it.elements();
        return bits;
    }
    bool isPublicRW() const { return ((m_vlflags & VLVF_PUB_RW) != 0); }
    bool isLazyPublicRW() const { return ((m_vlflags & VLVF_LAZY_PUBLIC_RW) != 0); }
    bool isLazyRetained() const { return ((m_vlflags & VLVF_LAZY_RETAINED) != 0); }
    uint32_t lazyShape() const { return m_vlflags & VLVF_LAZY_SHAPE_MASK; }
    bool isForceable() const { return ((m_vlflags & VLVF_FORCEABLE) != 0); }
    bool isContinuously() const { return ((m_vlflags & VLVF_CONTINUOUSLY) != 0); }
    // DPI compatible C standard layout
    bool isDpiCLayout() const { return ((m_vlflags & VLVF_DPI_CLAY) != 0); }
    bool isSigned() const { return ((m_vlflags & VLVF_SIGNED) != 0); }
    bool isBitVar() const { return ((m_vlflags & VLVF_BITVAR) != 0); }
    bool isNet() const { return ((m_vlflags & VLVF_NET) != 0); }
    int udims() const VL_MT_SAFE { return m_unpacked.size(); }
    int pdims() const VL_MT_SAFE { return m_packed.size(); }
    int dims() const VL_MT_SAFE { return pdims() + udims(); }
    const std::vector<VerilatedRange>& packedRanges() const VL_MT_SAFE { return m_packed; }
    const std::vector<VerilatedRange>& unpackedRanges() const VL_MT_SAFE { return m_unpacked; }
    const VerilatedRange* range(int dim) const VL_MT_SAFE {
        if (dim < udims()) return &m_unpacked[dim];
        if (dim < dims()) return &m_packed[dim - udims()];
        return nullptr;
    }
    // DPI accessors (with packed dimensions flattened!)
    int left(int dim) const VL_MT_SAFE {
        return dim == 0                                ? m_packedDpi.left()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].left()
                                                       : 0;
    }
    int right(int dim) const VL_MT_SAFE {
        return dim == 0                                ? m_packedDpi.right()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].right()
                                                       : 0;
    }
    int low(int dim) const VL_MT_SAFE {
        return dim == 0                                ? m_packedDpi.low()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].low()
                                                       : 0;
    }
    int high(int dim) const VL_MT_SAFE {
        return dim == 0                                ? m_packedDpi.high()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].high()
                                                       : 0;
    }
    int increment(int dim) const {
        return dim == 0                                ? m_packedDpi.increment()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].increment()
                                                       : 0;
    }
    int elements(int dim) const VL_MT_SAFE {
        return dim == 0                                ? m_packedDpi.elements()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].elements()
                                                       : 0;
    }
    // Total size in bytes (note DPI limited to 4GB)
    size_t totalSize() const {
        size_t size = entSize();
        for (int udim = 0; udim < udims(); ++udim) size *= m_unpacked[udim].elements();
        return size;
    }
    // Adjust a data pointer to access a given array element, NULL if something goes bad
    void* datapAdjustIndex(void* datap, int dim, int indx) const VL_MT_SAFE;
};

//===========================================================================
// Verilator DPI open array variable

class VerilatedDpiOpenVar final {
    // MEMBERS
    const VerilatedVarProps* const m_propsp;  // Variable properties
    void* const m_datap;  // Location of data (local to thread always, so safe)
public:
    // CONSTRUCTORS
    VerilatedDpiOpenVar(const VerilatedVarProps* propsp, void* datap)
        : m_propsp{propsp}
        , m_datap{datap} {}
    VerilatedDpiOpenVar(const VerilatedVarProps* propsp, const void* datap)
        : m_propsp{propsp}
        , m_datap{const_cast<void*>(datap)} {}
    ~VerilatedDpiOpenVar() = default;
    // METHODS
    void* datap() const VL_MT_SAFE { return m_datap; }
    // METHODS - from VerilatedVarProps
    bool magicOk() const { return m_propsp->magicOk(); }
    VerilatedVarType vltype() const { return m_propsp->vltype(); }
    bool isDpiStdLayout() const { return m_propsp->isDpiCLayout(); }
    int entBits() const { return m_propsp->entBits(); }
    int udims() const VL_MT_SAFE { return m_propsp->udims(); }
    int left(int dim) const VL_MT_SAFE { return m_propsp->left(dim); }
    int right(int dim) const VL_MT_SAFE { return m_propsp->right(dim); }
    int low(int dim) const { return m_propsp->low(dim); }
    int high(int dim) const { return m_propsp->high(dim); }
    int increment(int dim) const { return m_propsp->increment(dim); }
    int elements(int dim) const { return m_propsp->elements(dim); }
    size_t totalSize() const { return m_propsp->totalSize(); }
    void* datapAdjustIndex(void* datap, int dim, int indx) const VL_MT_SAFE {
        return m_propsp->datapAdjustIndex(datap, dim, indx);
    }
};

//===========================================================================
// Verilator variable
// Thread safety: Assume is constructed only with model, then any number of readers

struct VerilatedForceControlSignals;
class VerilatedVpioVar;

class VerilatedVar final : public VerilatedVarProps {
    // MEMBERS
    void* const m_datap;  // Location of data
    const char* const m_namep;  // Name - slowpath
    std::unique_ptr<const VerilatedForceControlSignals>
        m_forceControlSignals;  // Force control signals

protected:
    const bool m_isParam;
    friend class VerilatedScope;
    // CONSTRUCTORS
    VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                 VerilatedVarFlags vlflags, int udims, int pdims, bool isParam);
    VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                 VerilatedVarFlags vlflags, int udims, int pdims, bool isParam, uint32_t entSize);
    VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                 VerilatedVarFlags vlflags, int udims, int pdims, bool isParam,
                 std::unique_ptr<const VerilatedForceControlSignals> forceControlSignals);

public:
    ~VerilatedVar();
    VerilatedVar(VerilatedVar&&);
    // ACCESSORS
    void* datap() const {
        // A --vpi-lazy row's m_datap is a VerilatedVarLazyDatap, so returning it as the value
        // would hand back the descriptor; such a row is readable only through VPI. Debug-only,
        // as datap() is on the VPI read path of every model, lazy or not.
        VL_DEBUG_IF(  // LCOV_EXCL_START
            if (VL_UNCOVERABLE(isLazyPublicRW())) {
                VL_FATAL_MT(__FILE__, __LINE__, m_namep,
                            "VerilatedVar::datap() on a --vpi-lazy reconstructed signal,"
                            " read it through VPI");
            });  // LCOV_EXCL_STOP
        return m_datap;
    }
    // Reconstruct a --vpi-lazy row, or nothing for a plain one, and return a READ view of the
    // storage. Const because it is otherwise the shortest route to a mutable pointer into a
    // lazy row, and a store through such a pointer would skip the deposit claim.
    inline const void* datapRefresh(VerilatedLazyStamps stamps) const VL_MT_UNSAFE_ONE;
    inline void datapClaimDeposit(VerilatedLazyStamps stamps) const VL_MT_UNSAFE_ONE;
    const char* name() const { return m_namep; }
    bool isParam() const { return m_isParam; }
    const VerilatedForceControlSignals* forceControlSignals() const {
        return m_forceControlSignals.get();
    }

private:
    // The --vpi-lazy descriptor; only meaningful when isLazyPublicRW(). Private, because selfp
    // plus storageOffset is a mutable pointer into a lazy row, and only VlVpiWriteAccess may
    // hold one; VerilatedVpioVar::storagep() is the single friend that computes that address.
    VerilatedVarLazyDatap* lazyDatap() const {
        VL_DEBUG_IFDEF(assert(isLazyPublicRW()););
        return static_cast<VerilatedVarLazyDatap*>(m_datap);
    }
    friend class VerilatedVpioVar;
};

//===========================================================================
// Force control signals of a VerilatedVar

struct VerilatedForceControlSignals final {
    const VerilatedVar* forceEnableSignalp{nullptr};  // __VforceEn signal
    const VerilatedVar* forceValueSignalp{nullptr};  // __VforceVal signal
    const VerilatedVar forceReadSignal;  // __VforceRd signal
};

inline VerilatedVar::VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                                  VerilatedVarFlags vlflags, int udims, int pdims, bool isParam)
    : VerilatedVarProps{vltype, vlflags, udims, pdims}
    , m_datap{datap}
    , m_namep{namep}
    , m_isParam{isParam} {}
inline VerilatedVar::VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                                  VerilatedVarFlags vlflags, int udims, int pdims, bool isParam,
                                  uint32_t entSize)
    : VerilatedVarProps{vltype, vlflags, udims, pdims, entSize}
    , m_datap{datap}
    , m_namep{namep}
    , m_isParam{isParam} {}
inline VerilatedVar::VerilatedVar(
    const char* namep, void* datap, VerilatedVarType vltype, VerilatedVarFlags vlflags, int udims,
    int pdims, bool isParam,
    std::unique_ptr<const VerilatedForceControlSignals> forceControlSignals)
    : VerilatedVarProps{vltype, vlflags, udims, pdims}
    , m_datap{datap}
    , m_namep{namep}
    , m_forceControlSignals{std::move(forceControlSignals)}
    , m_isParam{isParam} {}
inline VerilatedVar::~VerilatedVar() = default;
inline VerilatedVar::VerilatedVar(VerilatedVar&&) = default;
// Not MT safe: runs generated reconstruction code and writes the model's shadow storage
const void* VerilatedVar::datapRefresh(VerilatedLazyStamps stamps) const VL_MT_UNSAFE_ONE {
    if (!isLazyPublicRW()) return m_datap;
    auto* const lazyDatap = static_cast<VerilatedVarLazyDatap*>(m_datap);
    uint8_t* const basep = static_cast<uint8_t*>(lazyDatap->selfp);
    if (lazyShape() == VLVF_LAZY_CONE) {
        // The func would skip its commit to a deposited row anyway; skipping the call keeps a
        // deposited read at a single load and does not rebuild a cone nobody asked for.
        const uint64_t* const depp
            = reinterpret_cast<const uint64_t*>(basep + lazyDatap->srcOffset);
        if (VL_LIKELY(*depp != stamps.deposited)) (lazyDatap->refreshp)(lazyDatap->selfp);
        return basep + lazyDatap->storageOffset;
    }
    // Copy and fold rows have no generated body, so nothing can take a deposit back and the
    // descriptor's own stamp carries it. A deposit outranks the copy: the shadow is this row's
    // value until the next eval step, however many epochs other deposits burn through.
    if (VL_UNLIKELY(lazyDatap->stamp == stamps.deposited)) return basep + lazyDatap->storageOffset;
    if (lazyDatap->stamp != stamps.refreshed) {
        lazyDatap->stamp = stamps.refreshed;
        // A folded row copies the cone shadow this call rebuilds, deposit preserved and all
        if (lazyShape() == VLVF_LAZY_FOLD) (lazyDatap->refreshp)(lazyDatap->selfp);
        std::memcpy(basep + lazyDatap->storageOffset, basep + lazyDatap->srcOffset, totalSize());
    }
    return basep + lazyDatap->storageOffset;
}
// Claim this row's shadow as a deposit, so reads return it and a cone body skips the commit that
// would take it back, until the next lazyEvalEnd() moves the deposit generation. Called once the
// store has committed: a put rejected between the pre-store refresh and here must leave no claim.
void VerilatedVar::datapClaimDeposit(VerilatedLazyStamps stamps) const VL_MT_UNSAFE_ONE {
    if (!isLazyPublicRW()) return;
    VerilatedVarLazyDatap* const datap = lazyDatap();
    if (lazyShape() != VLVF_LAZY_CONE) {
        datap->stamp = stamps.deposited;
        return;
    }
    // varsInsertFromTable() rejects a cone row whose srcOffset is not a usable word offset, so
    // this write cannot land on an arbitrary byte of the instance
    *reinterpret_cast<uint64_t*>(static_cast<uint8_t*>(datap->selfp) + datap->srcOffset)
        = stamps.deposited;
}

#endif  // Guard
