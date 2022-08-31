// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2001-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated tracing in FST for SystemC implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use --sc --trace-fst.
///
/// Use "verilator --sc --trace-fst" to add this to the Makefile for the linker.
///
//=============================================================================

#include "verilatedos.h"

#include "verilated_fst_sc.h"

//======================================================================
//======================================================================

void VerilatedFstSc::open(const char* filename) {
    if (!sc_core::sc_get_curr_simcontext()->elaboration_done()) {
        vl_fatal(__FILE__, __LINE__, "VerilatedFstSc",
                 ("%Error: VerilatedFstSc::open(\"" + std::string{filename}
                  + "\") is called before sc_core::sc_start(). "
                    "Run sc_core::sc_start(sc_core::SC_ZERO_TIME) before opening a wave file.")
                     .c_str());
    }
    VerilatedFstC::open(filename);
}

//--------------------------------------------------
// SystemC 2.1.v1
// cppcheck-suppress unusedFunction
void VerilatedFstSc::write_comment(const std::string&) {}
void VerilatedFstSc::trace(const unsigned int&, const std::string&, const char**) {}

#define DECL_TRACE_METHOD_A(tp) \
    void VerilatedFstSc::trace(const tp& object, const std::string& name) {}
#define DECL_TRACE_METHOD_B(tp) \
    void VerilatedFstSc::trace(const tp& object, const std::string& name, int width) {}

// clang-format off
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

//********************************************************************
