// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Structured partition-local RepCut programs
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#ifndef VERILATOR_V3REPCUTPROGRAM_H_
#define VERILATOR_V3REPCUTPROGRAM_H_

#include "config_build.h"
#include "verilatedos.h"

#include <set>
#include <vector>

class AstNodeStmt;
class AstScope;
class AstVarScope;
class V3DfgContext;

namespace V3RepCut {
// Compile a complete evaluation program before state release, storage layout or
// function construction. Assigned values must denote immutable phase versions;
// the only repeated writes admitted are deferred-store candidate initialization.
// 'preserve' names the phase interface, not every temporary crossing a branch.
// No operation leaves its guard and no memory publication occurs in this IR.
void optimizeProgram(AstScope& scope, std::vector<AstNodeStmt*>& statements,
                     const std::set<AstVarScope*>& preserve, size_t expressionLimit,
                     V3DfgContext& context) VL_MT_DISABLED;
void selfTestProgram(AstScope& scope) VL_MT_DISABLED;
}  // namespace V3RepCut

#endif  // Guard
