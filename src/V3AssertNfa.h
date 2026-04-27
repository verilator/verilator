// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: NFA-based multi-cycle SVA assertion evaluation
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

#ifndef VERILATOR_V3ASSERTNFA_H_
#define VERILATOR_V3ASSERTNFA_H_

#include "config_build.h"
#include "verilatedos.h"

class AstClocking;
class AstDefaultDisable;
class AstNetlist;
class AstNodeModule;

// Module defaults shared with V3AssertPre. First-found wins; multi-default
// diagnostics and event-var creation live in V3AssertPre.
struct V3AssertModuleDefaults final {
    AstClocking* defaultClockingp = nullptr;
    AstDefaultDisable* defaultDisablep = nullptr;
};

class V3AssertNfa final {
public:
    static void assertNfaAll(AstNetlist* nodep) VL_MT_DISABLED;
    static V3AssertModuleDefaults collectModuleDefaults(AstNodeModule* modp) VL_MT_DISABLED;
};

#endif  // Guard
