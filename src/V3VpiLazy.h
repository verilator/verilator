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
    // Must match the runtime table limit.
    static constexpr int VPI_TABLE_MAX_DIMS = 3;
    // Copy source after V3Descope.
    struct CrossScopeSrc final {
        const AstScope* scopep;
        const AstVar* varp;
    };
    // Deposit-generation word for a reconstruct cone.
    struct DepWord final {
        const AstVar* arrayVarp;  // Deposit-generation array
        int slot;
    };
    // Valid after resolveCrossScopeSrcs() until the next tree change.
    static const DepWord* depWordOf(const AstNetlist* nodep,
                                    const AstVar* shadowVarp) VL_MT_DISABLED;
    // Bind prepare() records after the final deleting pass.
    static void resolveCrossScopeSrcs(AstNetlist* nodep) VL_MT_DISABLED;
    // Valid after resolveCrossScopeSrcs() until the next tree change.
    static const CrossScopeSrc* crossScopeCopySrc(const AstNetlist* nodep, const AstScope* scopep,
                                                  const AstVar* shadowVarp) VL_MT_DISABLED;
    // Preserve reconstructable lazy signals before optimisation.
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
    // Split reconstruction functions after optimisation.
    static void finalize(AstNetlist* nodep) VL_MT_DISABLED;
    // AstNetlist owns this opaque context.
    static V3VpiLazyContext* newContext() VL_MT_DISABLED;
    static void deleteContext(V3VpiLazyContext* ctxp) VL_MT_DISABLED;
};

#endif  // Guard
