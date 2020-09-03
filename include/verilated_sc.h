// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Common include for all Verilated SystemC files
///
///     This file is included automatically by Verilator at the top of
///     all SystemC files it generates.
///
/// Code available from: https://verilator.org
///
//*************************************************************************

#ifndef _VERILATED_SC_H_
#define _VERILATED_SC_H_ 1  ///< Header Guard

#include "verilatedos.h"

#include "systemc.h"

//=============================================================================
// VL_SC_BV_DATAP
// We want to get a pointer to m_data in the sc_bv_base class,
// but it is protected.  So make an exposing class, then use
// cast magic to get at it.  Saves patching get_datap in SystemC.
// This class is thread safe (though most of SystemC is not).

#define VL_SC_BV_DATAP(bv) (VlScBvExposer::sp_datap(bv))
class VlScBvExposer : public sc_bv_base {
public:
    static const vluint32_t* sp_datap(const sc_bv_base& base) VL_MT_SAFE {
        return static_cast<const VlScBvExposer*>(&base)->sp_datatp();
    }
    const vluint32_t* sp_datatp() const { return reinterpret_cast<vluint32_t*>(m_data); }
    // Above reads this protected element in sc_bv_base:
    //   sc_digit* m_data; // data array
};

//=========================================================================

#endif  // Guard
