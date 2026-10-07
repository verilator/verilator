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

#include <vector>

class AstNetlist;
class AstScope;
class AstVar;
class V3VpiLazyContext;
class VVpiLazyComb;

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
    // Combinationally driven bits of one flat unpacked element; see VVpiLazyComb::PARTIAL.
    struct CombRun final {
        uint32_t elem;
        uint32_t lsb;
        uint32_t width;
        bool operator==(const CombRun& other) const {
            return elem == other.elem && lsb == other.lsb && width == other.width;
        }
    };
    // One instance's class: a PARTIAL variable's instances may differ.
    static VVpiLazyComb combOf(const AstNetlist* nodep, const AstScope* scopep,
                               const AstVar* varp) VL_MT_DISABLED;
    // A PARTIAL combOf() instance's runs, ordered by element then bit.
    static const std::vector<CombRun>& combRuns(const AstNetlist* nodep, const AstScope* scopep,
                                                const AstVar* varp) VL_MT_DISABLED;
    // Point the calls V3Descope gave an instance's self pointer at the shared func.
    static void retargetInstanceCalls(AstNetlist* nodep) VL_MT_DISABLED;
    // Bind prepare() records after the final deleting pass.
    static void resolveCrossScopeSrcs(AstNetlist* nodep) VL_MT_DISABLED;
    // Valid after resolveCrossScopeSrcs() until the next tree change.
    static const CrossScopeSrc* crossScopeCopySrc(const AstNetlist* nodep, const AstScope* scopep,
                                                  const AstVar* shadowVarp) VL_MT_DISABLED;
    // Preserve reconstructable lazy signals before optimisation.
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
    // Split reconstruction functions after optimisation.
    static void finalize(AstNetlist* nodep) VL_MT_DISABLED;
    // Make single-func temp shadows func locals, once V3DepthBlock and V3Localize have run.
    static void localizeTemps(AstNetlist* nodep) VL_MT_DISABLED;
    // AstNetlist owns this opaque context.
    static V3VpiLazyContext* newContext() VL_MT_DISABLED;
    static void deleteContext(V3VpiLazyContext* ctxp) VL_MT_DISABLED;
};

#endif  // Guard
