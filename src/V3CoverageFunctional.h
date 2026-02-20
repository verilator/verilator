// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Functional coverage implementation
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

#ifndef VERILATOR_V3COVERAGEFUNCTIONAL_H_
#define VERILATOR_V3COVERAGEFUNCTIONAL_H_

#include "V3Ast.h"
#include "V3Error.h"

//============================================================================

class V3CoverageFunctional final {
public:
    static void coverageFunctional(AstNetlist* nodep);
};

#endif  // Guard
