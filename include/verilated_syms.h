// -*- C++ -*-
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder. This program is free software; you can
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
/// \brief Verilator: Include to allow symbol inspection
///
///	This file is for inclusion by files that need to inspect
///	the symbol table.  It is not included in verilated.h
///	as it requires some heavyweight C++ classes.
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_SYMS_H_
#define _VERILATED_SYMS_H_ 1 ///< Header Guard

#include "verilated_heavy.h"

#include <map>

//======================================================================
// Types

struct VerilatedCStrCmp {
    /// Ordering maps keyed by const char*'s
    bool operator() (const char *a, const char *b) const {
	return std::strcmp(a, b) < 0;
    }
};

//===========================================================================
/// Verilator range

class VerilatedRange { 
    int		m_lhs;
    int		m_rhs;
protected:
    friend class VerilatedVar;
    friend class VerilatedScope;
    VerilatedRange() : m_lhs(0), m_rhs(0) {}
    void sets(int lhs, int rhs) { m_lhs=lhs; m_rhs=rhs; }
public:
    ~VerilatedRange() {}
    int lhs() const { return m_lhs; }
    int rhs() const { return m_rhs; }
    int bits() const { return (VL_LIKELY(m_lhs>=m_rhs)?(m_lhs-m_rhs+1):(m_rhs-m_lhs+1)); }
};

//===========================================================================
/// Verilator variable

class VerilatedVar {
    void*		m_datap;	// Location of data
    VerilatedVarType	m_vltype;	// Data type
    VerilatedVarFlags	m_vlflags;	// Direction
    VerilatedRange	m_range;	// First range
    VerilatedRange	m_array;	// Array
    int			m_dims;		// Dimensions
    const char*		m_namep;	// Name - slowpath
protected:
    friend class VerilatedScope;
    VerilatedVar(const char* namep, void* datap,
		 VerilatedVarType vltype, VerilatedVarFlags vlflags, int dims)
	: m_datap(datap), m_vltype(vltype), m_vlflags(vlflags), m_dims(dims), m_namep(namep) {}
public:
    ~VerilatedVar() {}
    void* datap() const { return m_datap; }
    VerilatedVarType vltype() const { return m_vltype; }
    VerilatedVarFlags vldir() const { return (VerilatedVarFlags)((int)m_vlflags & VLVF_MASK_DIR); }
    vluint32_t entSize() const;
    bool isPublicRW() const { return ((m_vlflags & VLVF_PUB_RW) != 0); }
    const VerilatedRange& range() const { return m_range; }
    const VerilatedRange& array() const { return m_array; }
    const char* name() const { return m_namep; }
    int dims() const { return m_dims; }
};

//======================================================================
/// Types

struct VerilatedVarNameMap : public map<const char*, VerilatedVar, VerilatedCStrCmp> {
    VerilatedVarNameMap() {}
    ~VerilatedVarNameMap() {}
};

#endif // Guard
