// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2015 by Wilson Snyder.  This program is free software;
// you can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.
//
// This is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
//=============================================================================
///
/// \file
/// \brief Verilator tracing in VCD format
///
//=============================================================================
// SPDIFF_OFF

#ifndef _VERILATED_VCD_SC_H_
#define _VERILATED_VCD_SC_H_ 1

#include "verilated_sc.h"
#include "verilated_vcd_c.h"

// SPDIFF_ON
//=============================================================================
// VerilatedVcdSc
///
/// This class is passed to the SystemC simulation kernel, just like a
/// documented SystemC trace format.

class VerilatedVcdSc
    : sc_trace_file
    , public VerilatedVcdC
{
public:
    VerilatedVcdSc() {
	sc_get_curr_simcontext()->add_trace_file(this);
# if (SYSTEMC_VERSION>=20060505)
	// We want to avoid a depreciated warning, but still be back compatible.
	// Turning off the message just for this still results in an annoying "to turn off" message.
	sc_time t1sec(1,SC_SEC);
	if (t1sec.to_default_time_units()!=0) {
	    sc_time tunits(1.0/t1sec.to_default_time_units(),SC_SEC);
	    spTrace()->set_time_unit(tunits.to_string());
	}
	spTrace()->set_time_resolution(sc_get_time_resolution().to_string());
# elif (SYSTEMC_VERSION>20011000)
	// To confuse matters 2.1.beta returns a char* here, while 2.1.v1 returns a std::string
	// we allow both flavors with overloaded set_time_* functions.
	spTrace()->set_time_unit(sc_get_default_time_unit().to_string());
	spTrace()->set_time_resolution(sc_get_time_resolution().to_string());
# endif
    }

    virtual ~VerilatedVcdSc() {}
    /// Called by SystemC simulate()
    virtual void cycle (bool delta_cycle) {
# if (SYSTEMC_VERSION>20011000)
	if (!delta_cycle) { this->dump(sc_time_stamp().to_double()); }
# else
	// VCD files must have integer timestamps, so we write all times in increments of time_resolution
	if (!delta_cycle) { this->dump(sc_time_stamp().to_double()); }
# endif
    }

private:
    /// Fake outs for linker

#ifdef NC_SYSTEMC
    // Cadence Incisive has these as abstract functions so we must create them
    virtual void set_time_unit( int exponent10_seconds ) {} // deprecated
#endif
#if defined(NC_SYSTEMC) || (SYSTEMC_VERSION>=20111100)
    virtual void set_time_unit( double v, sc_time_unit tu ) {}
#endif


//--------------------------------------------------
# if (SYSTEMC_VERSION>=20050714)
    // SystemC 2.1.v1
# define DECL_TRACE_METHOD_A(tp) \
    virtual void trace( const tp& object, const std::string& name );
# define DECL_TRACE_METHOD_B(tp) \
    virtual void trace( const tp& object, const std::string& name, int width );

    virtual void write_comment (const std::string &);
    virtual void trace (const unsigned int &, const std::string &, const char **);

    DECL_TRACE_METHOD_A( bool )
    DECL_TRACE_METHOD_A( sc_dt::sc_bit )
    DECL_TRACE_METHOD_A( sc_dt::sc_logic )

    DECL_TRACE_METHOD_B( unsigned char )
    DECL_TRACE_METHOD_B( unsigned short )
    DECL_TRACE_METHOD_B( unsigned int )
    DECL_TRACE_METHOD_B( unsigned long )
#ifdef SYSTEMC_64BIT_PATCHES
    DECL_TRACE_METHOD_B( unsigned long long)
#endif
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

//--------------------------------------------------
# elif (SYSTEMC_VERSION>20011000)
    // SystemC 2.0.1
# define DECL_TRACE_METHOD_A(tp) \
    virtual void trace( const tp& object, const sc_string& name );
# define DECL_TRACE_METHOD_B(tp) \
    virtual void trace( const tp& object, const sc_string& name, int width );

    virtual void write_comment (const sc_string &);
    virtual void trace (const unsigned int &, const sc_string &, const char **);
    virtual void delta_cycles (bool) {}
    virtual void space( int n ) {}

    DECL_TRACE_METHOD_A( bool )
    DECL_TRACE_METHOD_A( sc_bit )
    DECL_TRACE_METHOD_A( sc_logic )
    DECL_TRACE_METHOD_B( unsigned char )
    DECL_TRACE_METHOD_B( unsigned short )
    DECL_TRACE_METHOD_B( unsigned int )
    DECL_TRACE_METHOD_B( unsigned long )
#ifdef SYSTEMC_64BIT_PATCHES
    DECL_TRACE_METHOD_B( unsigned long long)
#endif
#if (SYSTEMC_VERSION>20041000)
    DECL_TRACE_METHOD_B( unsigned long long)
    DECL_TRACE_METHOD_B( long long)
#endif
    DECL_TRACE_METHOD_B( char )
    DECL_TRACE_METHOD_B( short )
    DECL_TRACE_METHOD_B( int )
    DECL_TRACE_METHOD_B( long )
    DECL_TRACE_METHOD_A( float )
    DECL_TRACE_METHOD_A( double )
    DECL_TRACE_METHOD_A( sc_int_base )
    DECL_TRACE_METHOD_A( sc_uint_base )
    DECL_TRACE_METHOD_A( sc_signed )
    DECL_TRACE_METHOD_A( sc_unsigned )
    DECL_TRACE_METHOD_A( sc_fxval )
    DECL_TRACE_METHOD_A( sc_fxval_fast )
    DECL_TRACE_METHOD_A( sc_fxnum )
    DECL_TRACE_METHOD_A( sc_fxnum_fast )
    DECL_TRACE_METHOD_A( sc_bv_base )
    DECL_TRACE_METHOD_A( sc_lv_base )

//--------------------------------------------------
# else
    // SystemC 1.2.1beta
# define DECL_TRACE_METHOD_A(tp) \
    virtual void trace( const tp& object, const sc_string& name );
# define DECL_TRACE_METHOD_B(tp) \
    virtual void trace( const tp& object, const sc_string& name, int width );

    virtual void write_comment (const sc_string &);
    virtual void trace (const unsigned int &, const sc_string &, const char **);

    DECL_TRACE_METHOD_A( bool )
    DECL_TRACE_METHOD_B( unsigned char )
    DECL_TRACE_METHOD_B( short unsigned int )
    DECL_TRACE_METHOD_B( unsigned int )
    DECL_TRACE_METHOD_B( long unsigned int )
    DECL_TRACE_METHOD_B( char )
    DECL_TRACE_METHOD_B( short int )
    DECL_TRACE_METHOD_B( int )
    DECL_TRACE_METHOD_B( long int )
    DECL_TRACE_METHOD_A( float )
    DECL_TRACE_METHOD_A( double )
    DECL_TRACE_METHOD_A( sc_bit )
    DECL_TRACE_METHOD_A( sc_logic )
    DECL_TRACE_METHOD_A( sc_bool_vector )
    DECL_TRACE_METHOD_A( sc_logic_vector )
    DECL_TRACE_METHOD_A( sc_signal_bool_vector )
    DECL_TRACE_METHOD_A( sc_signal_logic_vector )
    DECL_TRACE_METHOD_A( sc_uint_base )
    DECL_TRACE_METHOD_A( sc_int_base )
    DECL_TRACE_METHOD_A( sc_unsigned )
    DECL_TRACE_METHOD_A( sc_signed )
    DECL_TRACE_METHOD_A( sc_signal_resolved )
    DECL_TRACE_METHOD_A( sc_signal_resolved_vector )
    DECL_TRACE_METHOD_A( sc_bv_ns::sc_bv_base )
    DECL_TRACE_METHOD_A( sc_bv_ns::sc_lv_base )
# endif

# undef DECL_TRACE_METHOD_A
# undef DECL_TRACE_METHOD_B
};

#endif // guard
