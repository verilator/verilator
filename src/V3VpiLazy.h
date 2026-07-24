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

class AstNetlist;

//============================================================================

class V3VpiLazy final {
public:
    // Name of the generated reconstruction function.
    static const char* const RECONSTRUCT_FUNC_NAME;
    // Max packed+unpacked dims a VlVarTableEntry row holds (must match
    // VlVarTableEntry::kMaxDims in verilated.h - not includable from compiler
    // code). Shared with V3EmitCSyms so its table/residual-path split agrees
    // with lazy-reconstructability classification here.
    static constexpr int VPI_TABLE_MAX_DIMS = 3;
    // Before optimization: move lazy VPI signals' defining expressions into
    // cold shadow storage and force their referenced signals to survive,
    // freeing the optimizer to delete the originals.
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
    // After scheduling: split oversized reconstruction functions per
    // --output-split-cfuncs and bump the freshness epoch at eval() end.
    static void finalize(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // Guard
