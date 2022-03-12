// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
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
/// \brief Verilated tracing types
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated tracing routines.
///
//=============================================================================
#ifndef VERILATOR_VERILATED_TRACE_DEFS_H_
#define VERILATOR_VERILATED_TRACE_DEFS_H_

// Verilator tracing scope types:
// The values should match FST_ST_VCD_* from fstScopeType in gtkwave/fstapi.h
// verilated_fst_c.cpp contains assertions to enforce this
enum VltTraceScope {
    VLT_TRACE_SCOPE_MODULE = 0,
    VLT_TRACE_SCOPE_TASK = 1,
    VLT_TRACE_SCOPE_FUNCTION = 2,
    VLT_TRACE_SCOPE_BEGIN = 3,
    VLT_TRACE_SCOPE_FORK = 4,
    VLT_TRACE_SCOPE_GENERATE = 5,
    VLT_TRACE_SCOPE_STRUCT = 6,
    VLT_TRACE_SCOPE_UNION = 7,
    VLT_TRACE_SCOPE_CLASS = 8,
    VLT_TRACE_SCOPE_INTERFACE = 9,
    VLT_TRACE_SCOPE_PACKAGE = 10,
    VLT_TRACE_SCOPE_PROGRAM = 11
};

#endif  // guard
