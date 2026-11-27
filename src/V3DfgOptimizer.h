// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dataflow based optimization of combinational logic
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

#ifndef VERILATOR_V3DFGOPTIMIZER_H_
#define VERILATOR_V3DFGOPTIMIZER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <set>

//============================================================================

class V3DfgContext;
namespace V3DfgOptimizer {
// Optimize the design
void optimize(AstNetlist*) VL_MT_DISABLED;
// Optimize only this straight-line block. 'liveOuts' includes assigned bindings
// referenced outside it, including guards, other writers, and publication.
// Other private assigned bindings may be eliminated; input identities remain.
// Caller keeps inputs stable during execution and owns the shared statistics/
// deferred-deletion context until all blocks in the enclosing phase are built.
// 'availableInputs' proves initialization at block entry for external leaf
// operands of Cond expressions. Other Cond operands must be defined earlier in
// the block; computations inside Cond arms are not admitted by this interface.
// Returns false without changing statements if the block is not representable.
bool optimizeBlock(AstScope&, std::vector<AstNodeStmt*>&, const std::set<AstVarScope*>& liveOuts,
                   const std::set<AstVarScope*>& availableInputs, size_t expressionLimit,
                   V3DfgContext&) VL_MT_DISABLED;
}  // namespace V3DfgOptimizer

#endif  // Guard
