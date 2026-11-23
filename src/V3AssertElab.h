// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inline SVA property and sequence instances
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3ASSERTELAB_H_
#define VERILATOR_V3ASSERTELAB_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

//============================================================================

class V3AssertElab final {
public:
    static void assertElabAll(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
