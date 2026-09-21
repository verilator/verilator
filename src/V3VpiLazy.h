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
class AstScope;
class AstVar;
class V3VpiLazyContext;

//============================================================================

class V3VpiLazy final {
public:
    // Must match VlVarTableEntry::kMaxDims in verilated.h, which compiler code cannot include
    static constexpr int VPI_TABLE_MAX_DIMS = 3;
    // A copy row's source, as a (scope, var) pair rather than an AstVarScope: after V3Descope
    // the variable is a module member, and which instance of that module holds it is the scope.
    struct CrossScopeSrc final {
        const AstScope* scopep;
        const AstVar* varp;
    };
    // The __Vlazydep word a reconstructed row is guarded by: the cone body skips its commit to
    // that row while the word equals vlSymsp->__Vm_lazyDepStamp, and the VPI runtime writes it
    // through VerilatedVarLazyDatap::srcOffset. Emitter and runtime must address the same word,
    // so the descriptor row for a cone carries this offset and nothing else.
    struct DepWord final {
        const AstVar* arrayVarp;  // The module's deposit-generation array member
        int slot;  // Index into it; the byte offset is slot * sizeof(uint64_t)
    };
    // Null unless 'shadowVarp' is a reconstructed (cone) row with a deposit word. Valid only
    // between resolveCrossScopeSrcs(), which binds it, and the next tree change.
    static const DepWord* depWordOf(const AstNetlist* nodep,
                                    const AstVar* shadowVarp) VL_MT_DISABLED;
    // Bind the cross-scope copy rows and the deposit slots prepare() recorded, which it records
    // by name because V3Dead may free an AstVar and the slot be reused, to the surviving tree.
    // Call once, after the last pass that can delete a variable and before crossScopeCopySrc()
    // or depWordOf().
    static void resolveCrossScopeSrcs(AstNetlist* nodep) VL_MT_DISABLED;
    // Null unless prepare() made (scopep, shadowVarp) a cross-scope copy row whose source
    // survived. Valid only between resolveCrossScopeSrcs() and the next tree change: both the
    // arguments and the returned nodes are matched as live nodes, not by name.
    static const CrossScopeSrc* crossScopeCopySrc(const AstNetlist* nodep, const AstScope* scopep,
                                                  const AstVar* shadowVarp) VL_MT_DISABLED;
    // Shadow lazy signals' defining expressions so the optimizer may delete the originals
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
    // Check prepare()'s storagePinnedElsewhere() forecast held, once the optimizer has run
    static void verifyRetention(AstNetlist* nodep) VL_MT_DISABLED;
    // Split oversized reconstruction functions, once the optimizer has settled their size
    static void finalize(AstNetlist* nodep) VL_MT_DISABLED;
    // AstNetlist owns the context but cannot see its definition; it allocates through these
    static V3VpiLazyContext* newContext() VL_MT_DISABLED;
    static void deleteContext(V3VpiLazyContext* ctxp) VL_MT_DISABLED;
};

#endif  // Guard
