// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2001-2021 by Wilson Snyder. This program is free software; you
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

enum vltscope_t {
    VLT_SCOPE_MODULE = 0,
    VLT_SCOPE_TASK = 1,
    VLT_SCOPE_FUNCTION = 2,
    VLT_SCOPE_BEGIN = 3,
    VLT_SCOPE_FORK = 4,
    VLT_SCOPE_GENERATE = 5,
    VLT_SCOPE_STRUCT = 6,
    VLT_SCOPE_UNION = 7,
    VLT_SCOPE_CLASS = 8,
    VLT_SCOPE_INTERFACE = 9,
    VLT_SCOPE_PACKAGE = 10,
    VLT_SCOPE_PROGRAM = 11
};

#endif  // guard
