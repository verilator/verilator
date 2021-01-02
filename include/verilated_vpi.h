// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2009-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=========================================================================
///
/// \file
/// \brief Verilator: VPI implementation code
///
///     This file must be compiled and linked against all objects
///     created from Verilator or called by Verilator that use the VPI.
///
/// Code available from: https://verilator.org
///
//=========================================================================

#ifndef _VERILATED_VPI_H_
#define _VERILATED_VPI_H_ 1  ///< Header Guard

#include "verilatedos.h"
#include "verilated.h"
#include "verilated_syms.h"

//======================================================================
// From IEEE 1800-2009 annex K

#include "vltstd/vpi_user.h"

//======================================================================

class VerilatedVpi final {
public:
    /// Call timed callbacks
    /// Users should call this from their main loops
    static void callTimedCbs() VL_MT_UNSAFE_ONE;
    /// Call value based callbacks
    /// Users should call this from their main loops
    static bool callValueCbs() VL_MT_UNSAFE_ONE;
    /// Call callbacks of arbitrary types
    /// Users can call this from their application code
    static bool callCbs(vluint32_t reason) VL_MT_UNSAFE_ONE;
    /// Returns time of the next registered VPI callback, or
    /// ~(0) if none are registered
    static QData cbNextDeadline() VL_MT_UNSAFE_ONE;
    /// Self test, for internal use only
    static void selfTest() VL_MT_UNSAFE_ONE;
};

#endif  // Guard
