// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Include to provide information about symbol inspection
///
///     This file is for inclusion by internal files that need to inspect
///     specific symbols.
///
///     User routines wanting to inspect the symbol table should use
///     verilated_syms.h instead.
///
///     These classes are thread safe, and read only.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_SYM_PROPS_H_
#define _VERILATED_SYM_PROPS_H_ 1 ///< Header Guard

//===========================================================================
/// Verilator range
/// Thread safety: Assume is constructed only with model, then any number of readers

// See also V3Ast::VNumRange
class VerilatedRange {
    int         m_left;
    int         m_right;
protected:
    friend class VerilatedVar;
    friend class VerilatedScope;
    VerilatedRange() : m_left(0), m_right(0) {}
    void init(int left, int right) { m_left=left; m_right=right; }
public:
    ~VerilatedRange() {}
    int left() const { return m_left; }
    int right() const { return m_right; }
    int elements() const { return (VL_LIKELY(m_left>=m_right)?(m_left-m_right+1):(m_right-m_left+1)); }
};

//===========================================================================
/// Verilator variable
/// Thread safety: Assume is constructed only with model, then any number of readers

class VerilatedVar {
    void*               m_datap;        // Location of data
    VerilatedVarType    m_vltype;       // Data type
    VerilatedVarFlags   m_vlflags;      // Direction
    VerilatedRange      m_packed;       // Packed array range
    VerilatedRange      m_unpacked[1];  // Unpacked array range
    int                 m_dims;         // Dimensions
    const char*         m_namep;        // Name - slowpath
protected:
    friend class VerilatedScope;
    VerilatedVar(const char* namep, void* datap,
                 VerilatedVarType vltype, VerilatedVarFlags vlflags, int dims)
        : m_datap(datap), m_vltype(vltype), m_vlflags(vlflags), m_dims(dims), m_namep(namep) {}
public:
    ~VerilatedVar() {}
    void* datap() const { return m_datap; }
    VerilatedVarType vltype() const { return m_vltype; }
    VerilatedVarFlags vldir() const { return static_cast<VerilatedVarFlags>(static_cast<int>(m_vlflags) & VLVF_MASK_DIR); }
    vluint32_t entSize() const;
    bool isPublicRW() const { return ((m_vlflags & VLVF_PUB_RW) != 0); }
    const VerilatedRange& packed() const { return m_packed; }
    const VerilatedRange& unpacked() const { return m_unpacked[0]; }
    const VerilatedRange& range() const { return packed(); }  // Deprecated
    const VerilatedRange& array() const { return unpacked(); }  // Deprecated
    const char* name() const { return m_namep; }
    int dims() const { return m_dims; }
};

#endif // Guard
