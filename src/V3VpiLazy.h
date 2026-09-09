// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Reconstruct optimizer-eliminated VPI signals
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

#ifndef VERILATOR_V3VPILAZY_H_
#define VERILATOR_V3VPILAZY_H_

#include "config_build.h"
#include "verilatedos.h"

#include <string>

class AstNetlist;
class AstVar;

//============================================================================

class V3VpiLazy final {
public:
    // Reconstruction function stem; suffixed with the group id to cap name size
    static const char* const RECONSTRUCT_FUNC_NAME;
    // Shadow member prefix; suffixed with that same group id and the target's slot
    static const char* const SHADOW_PREFIX;
    // Per-module freshness stamp array, indexed by the group's module-local epoch slot
    static const char* const EPOCH_NAME;
    // Must match VlVarTableEntry::kMaxDims in verilated.h, which compiler code cannot include
    static constexpr int VPI_TABLE_MAX_DIMS = 3;
    // Shadow lazy signals' defining expressions so the optimizer may delete the originals
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
    // Split oversized reconstruction functions, once the optimizer has settled their size
    static void finalize(AstNetlist* nodep) VL_MT_DISABLED;
    // Recovered from the shadow's name, as the preparer's state is gone by V3EmitCSyms
    static std::string reconFuncNameOf(const AstVar* shadowVarp) VL_MT_DISABLED;
};

#endif  // Guard
