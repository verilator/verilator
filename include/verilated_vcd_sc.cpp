// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilator tracing in VCD Format
///
//=============================================================================
// SPDIFF_OFF

#include "verilatedos.h"
#include "verilated_vcd_sc.h"

// SPDIFF_ON
//======================================================================
//======================================================================

//--------------------------------------------------
#if (SYSTEMC_VERSION>=20050714)
    // SystemC 2.1.v1
// cppcheck-suppress unusedFunction
void VerilatedVcdSc::write_comment(const std::string &) {}
void VerilatedVcdSc::trace(const unsigned int &, const std::string &, const char**) {}

# define DECL_TRACE_METHOD_A(tp) \
    void VerilatedVcdSc::trace( const tp& object, const std::string& name ) {}
# define DECL_TRACE_METHOD_B(tp) \
    void VerilatedVcdSc::trace( const tp& object, const std::string& name, int width ) {}

#if (SYSTEMC_VERSION>=20171012)
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
#elif (SYSTEMC_VERSION>20011000)
    // SystemC 2.0.1
// cppcheck-suppress unusedFunction
void VerilatedVcdSc::write_comment(const sc_string &) {}
void VerilatedVcdSc::trace(const unsigned int&, const sc_string&, const char**) {}

#define DECL_TRACE_METHOD_A(tp) \
    void VerilatedVcdSc::trace( const tp& object, const sc_string& name ) {}
#define DECL_TRACE_METHOD_B(tp) \
    void VerilatedVcdSc::trace( const tp& object, const sc_string& name, int width ) {}

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
#else
    // SystemC 1.2.1beta
// cppcheck-suppress unusedFunction
void VerilatedVcdSc::write_comment(const sc_string &) {}
void VerilatedVcdSc::trace(const unsigned int&, const sc_string&, const char**) {}

#define DECL_TRACE_METHOD_A(tp) \
    void VerilatedVcdSc::trace( const tp& object, const sc_string& name ) {}
#define DECL_TRACE_METHOD_B(tp) \
    void VerilatedVcdSc::trace( const tp& object, const sc_string& name, int width ) {}

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
#endif

#undef DECL_TRACE_METHOD_A
#undef DECL_TRACE_METHOD_B

//********************************************************************
