// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Copyright 2001-2022 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated tracing in VCD format for SystemC header
///
/// User wrapper code should use this header when creating VCD SystemC
/// traces.
///
/// This class is not threadsafe, as the SystemC kernel is not threadsafe.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_VCD_SC_H_
#define VERILATOR_VERILATED_VCD_SC_H_

#include "verilatedos.h"

#include "verilated_sc.h"
#include "verilated_vcd_c.h"

#include <string>

//=============================================================================
// VerilatedVcdSc
///
/// Class representing a Verilator-friendly VCD trace format registered
/// with the SystemC simulation kernel, just like a SystemC-documented
/// trace format.

class VerilatedVcdSc final : sc_trace_file, public VerilatedVcdC {
    // CONSTRUCTORS
    VL_UNCOPYABLE(VerilatedVcdSc);

public:
    /// Construct a SC trace object, and register with the SystemC kernel
    VerilatedVcdSc() {
        sc_get_curr_simcontext()->add_trace_file(this);
        // We want to avoid a depreciated warning, but still be back compatible.
        // Turning off the message just for this still results in an
        // annoying "to turn off" message.
        const sc_time t1sec{1, SC_SEC};
        if (t1sec.to_default_time_units() != 0) {
            const sc_time tunits{1.0 / t1sec.to_default_time_units(), SC_SEC};
            spTrace()->set_time_unit(tunits.to_string());
        }
        spTrace()->set_time_resolution(sc_get_time_resolution().to_string());
    }
    /// Destruct, flush, and close the dump
    virtual ~VerilatedVcdSc() /*override*/ { close(); }

    // METHODS - for SC kernel
    // Called by SystemC simulate()
    virtual void cycle(bool delta_cycle) {
        if (!delta_cycle) this->dump(sc_time_stamp().to_double());
    }

    // Override VerilatedVcdC. Must be called after starting simulation.
    // cppcheck-suppress missingOverride  // GCC won't accept override
    virtual void open(const char* filename) /*override*/ VL_MT_SAFE;

private:
    // METHODS - Fake outs for linker

#ifdef NC_SYSTEMC
    // Cadence Incisive has these as abstract functions so we must create them
    virtual void set_time_unit(int exponent10_seconds) {}  // deprecated
#endif
    virtual void set_time_unit(double v, sc_time_unit tu) {}  // LCOV_EXCL_LINE

//--------------------------------------------------
// SystemC 2.1.v1
#define DECL_TRACE_METHOD_A(tp) virtual void trace(const tp& object, const std::string& name);
#define DECL_TRACE_METHOD_B(tp) \
    virtual void trace(const tp& object, const std::string& name, int width);

    virtual void write_comment(const std::string&);
    virtual void trace(const unsigned int&, const std::string&, const char**);

    // clang-format off
    // Formatting matches that of sc_trace.h
#if (SYSTEMC_VERSION >= 20171012)
    DECL_TRACE_METHOD_A( sc_event )
    DECL_TRACE_METHOD_A( sc_time )
#endif

    DECL_TRACE_METHOD_A( bool )
    DECL_TRACE_METHOD_A( sc_dt::sc_bit )
    DECL_TRACE_METHOD_A( sc_dt::sc_logic )

    DECL_TRACE_METHOD_B( unsigned char )
    DECL_TRACE_METHOD_B( unsigned short )
    DECL_TRACE_METHOD_B( unsigned int )
    DECL_TRACE_METHOD_B( unsigned long )
    DECL_TRACE_METHOD_B( char )
    DECL_TRACE_METHOD_B( short )
    DECL_TRACE_METHOD_B( int )
    DECL_TRACE_METHOD_B( long )
    DECL_TRACE_METHOD_B( sc_dt::int64 )
    DECL_TRACE_METHOD_B( sc_dt::uint64 )

    DECL_TRACE_METHOD_A( float )
    DECL_TRACE_METHOD_A( double )
    DECL_TRACE_METHOD_A( sc_dt::sc_int_base )
    DECL_TRACE_METHOD_A( sc_dt::sc_uint_base )
    DECL_TRACE_METHOD_A( sc_dt::sc_signed )
    DECL_TRACE_METHOD_A( sc_dt::sc_unsigned )

    DECL_TRACE_METHOD_A( sc_dt::sc_fxval )
    DECL_TRACE_METHOD_A( sc_dt::sc_fxval_fast )
    DECL_TRACE_METHOD_A( sc_dt::sc_fxnum )
    DECL_TRACE_METHOD_A( sc_dt::sc_fxnum_fast )

    DECL_TRACE_METHOD_A( sc_dt::sc_bv_base )
    DECL_TRACE_METHOD_A( sc_dt::sc_lv_base )
    // clang-format on

#undef DECL_TRACE_METHOD_A
#undef DECL_TRACE_METHOD_B
};

#endif  // Guard
