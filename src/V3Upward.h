// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve upward task/function references
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3UPWARD_H_
#define VERILATOR_V3UPWARD_H_

#include "verilatedos.h"

//============================================================================

class AstNetlist;

class V3Upward final {
public:
    static void uniquify(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
