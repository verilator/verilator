// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Extract state-aware RepCut dependency graphs
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

#ifndef VERILATOR_V3REPCUT_H_
#define VERILATOR_V3REPCUT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Order.h"

#include <vector>

class AstNetlist;
class AstVarScope;
namespace V3Sched {
class ProcessList;
}

namespace V3RepCut {
// Each role has a separate cache-line boundary. Direct state is written during
// next evaluation, while published state can still be read by other workers.
enum class StorageRole : uint32_t { PRIVATE_EVAL, PUBLISHED_STATE, DIRECT_STATE };
static constexpr uint32_t STORAGE_ROLES = 3;
constexpr uint32_t storageGroup(size_t owner, StorageRole role) {
    return static_cast<uint32_t>(owner) * STORAGE_ROLES + static_cast<uint32_t>(role) + 1;
}
// Group zero denotes ordinary layout and has no RepCut owner.
constexpr uint32_t storageOwner(uint32_t group) { return (group - 1) / STORAGE_ROLES; }

// Export before NBA lowering; native mode follows DFG/Gate optimization.
// Partition and materialize kernels while their AST bindings are live.
// Incomplete graphs are explicitly marked and are not partitioner inputs.
void partitionAll(AstNetlist* netlistp) VL_MT_DISABLED;
// Remove native kernel dependency operands after scheduling and optimization.
void removeDependencyArgs(AstNetlist* netlistp) VL_MT_DISABLED;
// Move terminal output words after proven owner-local publication, after wide lowering.
void placeNativeOutputWords(AstNetlist* netlistp) VL_MT_DISABLED;
// Coalesce RepCut domain graphs after the scheduler assigned trigger indices.
void batchNativeKernels(AstNetlist* netlistp, const std::vector<V3Sched::ProcessList*>& logic,
                        AstVarScope* trigVscp) VL_MT_DISABLED;
}  // namespace V3RepCut

#endif  // Guard
