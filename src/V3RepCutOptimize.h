// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Optimize guarded RepCut evaluation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3REPCUTOPTIMIZE_H_
#define VERILATOR_V3REPCUTOPTIMIZE_H_

#include "config_build.h"
#include "verilatedos.h"

#include <map>
#include <set>
#include <vector>

class AstNodeStmt;
class AstScope;
class AstVarScope;

namespace V3RepCut {
struct DfgBlock final {
    std::set<AstVarScope*> m_liveOuts;  // Definitions observable outside this dataflow block
    // Values initialized on every path reaching this block, used by selections.
    std::set<AstVarScope*> m_availableInputs;
};
// Recover selections between already available leaf values without speculating
// their defining computations. 'inputs' must be initialized phase inputs or
// explicitly valid reuse boundaries, never arbitrary temporaries from old calls.
// Return metadata in the same depth-first block order as blockLiveOuts.
std::vector<DfgBlock> prepareDfg(std::vector<AstNodeStmt*>& statements,
                                 const std::set<AstVarScope*>& inputs,
                                 const std::set<AstVarScope*>& preserve) VL_MT_DISABLED;
// Replace a root candidate write with a direct state or output write after the
// final old-value read. The caller must prove destinations have no other partition
// readers during this phase. Returns the candidates whose publication is elided.
std::set<AstVarScope*>
releaseStateCandidates(std::vector<AstNodeStmt*>& statements,
                       const std::map<AstVarScope*, AstVarScope*>& destinations) VL_MT_DISABLED;
// Release guarded scalar candidates in a closed native evaluation. The caller
// must exclude all other old-state observers. Every non-hold write must follow
// the destination's last old-value read; opaque operations retain all staging.
std::set<AstVarScope*> releaseGuardedStateCandidates(
    const std::vector<AstNodeStmt*>& statements,
    const std::map<AstVarScope*, AstVarScope*>& destinations) VL_MT_DISABLED;
// Eliminate typed copies in one loop-free evaluation phase. Inputs are stable
// for the phase. Snapshot/publication bindings in 'preserve' must keep storage.
// Only references move across guards, never computations. Variables remain in
// their scopes for the ordinary dead-variable passes to remove later.
size_t eliminateCopies(std::vector<AstNodeStmt*>& statements,
                       const std::set<AstVarScope*>& preserve) VL_MT_DISABLED;
// Move a pure packed expression to its sole use in the same straight-line block.
// All operands must retain their definition-time values. Guard/call/memory
// boundaries, external consumers and oversized expressions retain storage.
size_t substituteLocalExpressions(std::vector<AstNodeStmt*>& statements,
                                  const std::set<AstVarScope*>& preserve,
                                  size_t limit) VL_MT_DISABLED;
// Enumerate straight-line blocks depth first, visiting then before else, and
// compute conservative live-outs. References in guards or other blocks (reads
// OR writes) preserve binding identity. Phase publication roots stay live too.
std::vector<std::set<AstVarScope*>>
blockLiveOuts(const std::vector<AstNodeStmt*>& statements,
              const std::set<AstVarScope*>& preserve) VL_MT_DISABLED;
void selfTestCopies(AstScope& scope) VL_MT_DISABLED;
void selfTestStateRelease(AstScope& scope) VL_MT_DISABLED;
void selfTestSelections(AstScope& scope) VL_MT_DISABLED;
void selfTestLocalExpressions(AstScope& scope) VL_MT_DISABLED;
}  // namespace V3RepCut

#endif  // Guard
