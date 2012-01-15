// -*- C++ -*-
//*************************************************************************
//
// Copyright 2009-2012 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
///
/// \file
/// \brief Verilator: VPI implementation code
///
///	This file must be compiled and linked against all objects
///	created from Verilator or called by Verilator that use the VPI.
///
/// Code available from: http://www.veripool.org/verilator
///
//=========================================================================

#include "verilated_vpi.h"

//======================================================================

VerilatedVpi VerilatedVpi::s_s;  // Singleton
vluint8_t* VerilatedVpio::s_freeHead = NULL;

//======================================================================
