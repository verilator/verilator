// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Definitions for thread safety checking
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3THREADSAFETY_H_
#define VERILATOR_V3THREADSAFETY_H_

#include <verilatedos.h>

// Annotated function can be called only in MT_DISABLED context, i.e. either in a code unit
// compiled with VL_MT_DISABLED_CODE_UNIT preprocessor definition, or in the main thread.
#define VL_MT_DISABLED VL_CLANG_ATTR(annotate("MT_DISABLED"))

#endif  // guard
