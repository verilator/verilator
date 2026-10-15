// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity inst domains
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

#ifndef VERILATOR_V3INST_H_
#define VERILATOR_V3INST_H_

#include "config_build.h"
#include "verilatedos.h"

#include <functional>

class AstAssignW;
class AstCell;
class AstNetlist;
class AstNodeExpr;
class AstNodeVarRef;
class AstPin;

//============================================================================

class V3Inst final {
public:
    static void instAll(AstNetlist* nodep) VL_MT_DISABLED;
    static AstAssignW* pinReconnectSimple(AstPin* pinp, AstCell* cellp, bool forTristate,
                                          bool alwaysCvt = false) VL_MT_DISABLED;
    static void checkOutputShort(const AstPin* nodep) VL_MT_DISABLED;
    // Call 'leaff' on each variable a pin connection would drive if it were assigned
    // (through bit/part/array selects, concatenations and single replications).
    // Returns false if the connection cannot be driven (e.g. arithmetic), or 'leaff'
    // returned false for a leaf. All leaves are visited either way.
    static bool forEachDrivenLeaf(AstNodeExpr* nodep,
                                  const std::function<bool(AstNodeVarRef*)>& leaff) VL_MT_DISABLED;
};

#endif  // Guard
