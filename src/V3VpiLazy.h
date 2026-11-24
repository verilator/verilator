// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Rematerialize optimizer-eliminated VPI signals
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

#include "V3Ast.h"

#include <map>
#include <set>
#include <string>
#include <vector>

//============================================================================

class V3VpiLazy final {
public:
    // Combinationally driven bits of one flat unpacked element; see VVpiLazyComb::PARTIAL.
    struct CombRun final {
        uint32_t elem;  // Flat unpacked element index
        uint32_t lsb;  // First driven bit within the element
        uint32_t width;  // Driven bits from lsb
        bool operator==(const CombRun& other) const {
            return elem == other.elem && lsb == other.lsb && width == other.width;
        }
    };
    // One instance's class: a PARTIAL variable's instances may differ.
    static VVpiLazyComb combOf(const AstScope* scopep, const AstVar* varp) VL_MT_DISABLED;
    // A PARTIAL combOf() instance's runs, ordered by element then bit.
    static const std::vector<CombRun>& combRuns(const AstScope* scopep,
                                                const AstVar* varp) VL_MT_DISABLED;
    // Func a rematerialized row in 'scopep' calls to rematerialize 'shadowVarp', empty for a
    // stored copy.
    static std::string rematFuncName(const AstScope* scopep,
                                     const AstVar* shadowVarp) VL_MT_DISABLED;
    // False where 'varp' has no instance in 'scopep': it is kept apart from its other instances.
    static bool hasRow(const AstScope* scopep, const AstVar* varp) VL_MT_DISABLED;
    // Mark candidates' combinationally driven bits after V3Active, ahead of V3Decompose and
    // V3BitBlast; prepare() re-marks them.
    static void classifyComb(AstNetlist* nodep) VL_MT_DISABLED;
    // Preserve rematerializable lazy signals before optimization.
    static void prepare(AstNetlist* nodep) VL_MT_DISABLED;
};

// The classification V3EmitCSyms reads, owned by AstNetlist
class V3VpiLazyContext final {
public:
    // By name, not node: a node deleted before V3EmitCSyms reads these may have its address
    // reused. V3Name has already settled the names.
    using VarKey = std::pair<std::string, std::string>;  // Module or scope name, variable name
    // PARTIAL variable -> its masked bits, where every instance agrees
    std::map<VarKey, std::vector<V3VpiLazy::CombRun>> m_combRuns;
    // One instance of a PARTIAL variable whose instances differ.
    struct InstComb final {
        VVpiLazyComb m_comb;  // This instance's class
        std::vector<V3VpiLazy::CombRun> m_runs;  // Its masked bits, if PARTIAL
    };
    std::map<VarKey, InstComb> m_instComb;
    // Rematerialization func name of a shadow's row in a scope other than its group's; see
    // rowStub()
    std::map<VarKey, std::string> m_rowRemat;
    // A split variable's or its shadow's instances held by the other; see splitKeptInstances()
    std::set<VarKey> m_noRow;

    VVpiLazyComb combOf(const AstScope* scopep, const AstVar* varp) const;
    const std::vector<V3VpiLazy::CombRun>& combRunsOf(const AstScope* scopep,
                                                      const AstVar* varp) const;
};

#endif  // Guard
