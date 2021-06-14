// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
    int left() const { return m_left; }
    int right() const { return m_right; }
    int low() const { return (m_left < m_right) ? m_left : m_right; }
    int high() const { return (m_left > m_right) ? m_left : m_right; }
    int elements() const {
        return (VL_LIKELY(m_left >= m_right) ? (m_left - m_right + 1) : (m_right - m_left + 1));
    }
    int increment() const { return (m_left >= m_right) ? 1 : -1; }
};

//===========================================================================
// Verilator variable
// Thread safety: Assume is constructed only with model, then any number of readers

class VerilatedVarProps VL_NOT_FINAL {
    // TYPES
    static constexpr vluint32_t MAGIC = 0xddc4f829UL;
    // MEMBERS
    const vluint32_t m_magic;  // Magic number
    const VerilatedVarType m_vltype;  // Data type
    const VerilatedVarFlags m_vlflags;  // Direction
    const int m_pdims;  // Packed dimensions, 0 = none
    const int m_udims;  // Unpacked dimensions, 0 = none
    VerilatedRange m_packed;  // Packed array range
    std::vector<VerilatedRange> m_unpacked;  // Unpacked array ranges
    void initUnpacked(const int* ulims) {
        for (int i = 0; i < m_udims; ++i) {
            const int uleft = ulims ? ulims[2 * i + 0] : 0;
            const int uright = ulims ? ulims[2 * i + 1] : 0;
            m_unpacked.emplace_back(uleft, uright);
        }
    }
    // CONSTRUCTORS
protected:
    friend class VerilatedScope;
    VerilatedVarProps(VerilatedVarType vltype, VerilatedVarFlags vlflags, int pdims, int udims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags{vlflags}
        , m_pdims{pdims}
        , m_udims{udims} {
        initUnpacked(nullptr);
    }

public:
    class Unpacked {};
    // Without packed
    VerilatedVarProps(VerilatedVarType vltype, int vlflags)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_pdims{0}
        , m_udims{0} {}
    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Unpacked, int udims, const int* ulims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_pdims{0}
        , m_udims{udims} {
        initUnpacked(ulims);
    }
    // With packed
    class Packed {};
    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Packed, int pl, int pr)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_pdims{1}
        , m_udims{0}
        , m_packed{pl, pr} {}
    VerilatedVarProps(VerilatedVarType vltype, int vlflags, Packed, int pl, int pr, Unpacked,
                      int udims, const int* ulims)
        : m_magic{MAGIC}
        , m_vltype{vltype}
        , m_vlflags(VerilatedVarFlags(vlflags))  // Need () or GCC 4.8 false warning
        , m_pdims{1}
        , m_udims{udims}
        , m_packed{pl, pr} {
        initUnpacked(ulims);
    }

public:
    ~VerilatedVarProps() = default;
    // METHODS
    bool magicOk() const { return m_magic == MAGIC; }
    VerilatedVarType vltype() const { return m_vltype; }
    VerilatedVarFlags vldir() const {
        return static_cast<VerilatedVarFlags>(static_cast<int>(m_vlflags) & VLVF_MASK_DIR);
    }
    vluint32_t entSize() const;
    bool isPublicRW() const { return ((m_vlflags & VLVF_PUB_RW) != 0); }
    // DPI compatible C standard layout
    bool isDpiCLayout() const { return ((m_vlflags & VLVF_DPI_CLAY) != 0); }
    int udims() const { return m_udims; }
    int dims() const { return m_pdims + m_udims; }
    const VerilatedRange& packed() const { return m_packed; }
    const VerilatedRange& unpacked() const { return m_unpacked[0]; }
    // DPI accessors
    int left(int dim) const {
        return dim == 0                                ? m_packed.left()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].left()
                                                       : 0;
    }
    int right(int dim) const {
        return dim == 0                                ? m_packed.right()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].right()
                                                       : 0;
    }
    int low(int dim) const {
        return dim == 0                                ? m_packed.low()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].low()
                                                       : 0;
    }
    int high(int dim) const {
        return dim == 0                                ? m_packed.high()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].high()
                                                       : 0;
    }
    int increment(int dim) const {
        return dim == 0                                ? m_packed.increment()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].increment()
                                                       : 0;
    }
    int elements(int dim) const {
        return dim == 0                                ? m_packed.elements()
               : VL_LIKELY(dim >= 1 && dim <= udims()) ? m_unpacked[dim - 1].elements()
                                                       : 0;
    }
    // Total size in bytes (note DPI limited to 4GB)
    size_t totalSize() const;
    // Adjust a data pointer to access a given array element, NuLL if something goes bad
    void* datapAdjustIndex(void* datap, int dim, int indx) const;
};

//===========================================================================
// Verilator DPI open array variable

class VerilatedDpiOpenVar final {
    // MEMBERS
    const VerilatedVarProps* m_propsp;  // Variable properties
    void* m_datap;  // Location of data (local to thread always, so safe)
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
    void* datap() const { return m_datap; }
    // METHODS - from VerilatedVarProps
    bool magicOk() const { return m_propsp->magicOk(); }
    VerilatedVarType vltype() const { return m_propsp->vltype(); }
    bool isDpiStdLayout() const { return m_propsp->isDpiCLayout(); }
    const VerilatedRange& packed() const { return m_propsp->packed(); }
    const VerilatedRange& unpacked() const { return m_propsp->unpacked(); }
    int udims() const { return m_propsp->udims(); }
    int left(int dim) const { return m_propsp->left(dim); }
    int right(int dim) const { return m_propsp->right(dim); }
    int low(int dim) const { return m_propsp->low(dim); }
    int high(int dim) const { return m_propsp->high(dim); }
    int increment(int dim) const { return m_propsp->increment(dim); }
    int elements(int dim) const { return m_propsp->elements(dim); }
    size_t totalSize() const { return m_propsp->totalSize(); }
    void* datapAdjustIndex(void* datap, int dim, int indx) const {
        return m_propsp->datapAdjustIndex(datap, dim, indx);
    }
};

//===========================================================================
// Verilator variable
// Thread safety: Assume is constructed only with model, then any number of readers

class VerilatedVar final : public VerilatedVarProps {
    // MEMBERS
    void* m_datap;  // Location of data
    const char* m_namep;  // Name - slowpath
protected:
    bool m_isParam;
    friend class VerilatedScope;
    // CONSTRUCTORS
    VerilatedVar(const char* namep, void* datap, VerilatedVarType vltype,
                 VerilatedVarFlags vlflags, int dims, bool isParam)
        : VerilatedVarProps{vltype, vlflags, (dims > 0 ? 1 : 0), ((dims > 1) ? dims - 1 : 0)}
        , m_datap{datap}
        , m_namep{namep}
        , m_isParam{isParam} {}

public:
    ~VerilatedVar() = default;
    // ACCESSORS
    void* datap() const { return m_datap; }
    const VerilatedRange& range() const { return packed(); }  // Deprecated
    const VerilatedRange& array() const { return unpacked(); }  // Deprecated
    const char* name() const { return m_namep; }
    bool isParam() const { return m_isParam; }
};

#endif  // Guard
