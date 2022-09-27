// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"

#include "V3DfgPasses.h"

#include "V3Dfg.h"
#include "V3Global.h"
#include "V3String.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

V3DfgCseContext::~V3DfgCseContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " CSE, expressions eliminated",
                     m_eliminated);
}

DfgRemoveVarsContext::~DfgRemoveVarsContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " Remove vars, variables removed",
                     m_removed);
}

static std::string getPrefix(const std::string& label) {
    if (label.empty()) return "";
    std::string str = VString::removeWhitespace(label);
    std::transform(str.begin(), str.end(), str.begin(), [](unsigned char c) {  //
        return c == ' ' ? '-' : std::tolower(c);
    });
    str += "-";
    return str;
}

V3DfgOptimizationContext::V3DfgOptimizationContext(const std::string& label)
    : m_label{label}
    , m_prefix{getPrefix(label)} {}

V3DfgOptimizationContext::~V3DfgOptimizationContext() {
    const string prefix = "Optimizations, DFG " + m_label + " ";
    V3Stats::addStat(prefix + "General, modules", m_modules);
    V3Stats::addStat(prefix + "Ast2Dfg, coalesced assignments", m_coalescedAssignments);
    V3Stats::addStat(prefix + "Ast2Dfg, input equations", m_inputEquations);
    V3Stats::addStat(prefix + "Ast2Dfg, representable", m_representable);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (dtype)", m_nonRepDType);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (impure)", m_nonRepImpure);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (timing)", m_nonRepTiming);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (lhs)", m_nonRepLhs);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (node)", m_nonRepNode);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (unknown)", m_nonRepUnknown);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (var ref)", m_nonRepVarRef);
    V3Stats::addStat(prefix + "Ast2Dfg, non-representable (width)", m_nonRepWidth);
    V3Stats::addStat(prefix + "Dfg2Ast, intermediate variables", m_intermediateVars);
    V3Stats::addStat(prefix + "Dfg2Ast, replaced variables", m_replacedVars);
    V3Stats::addStat(prefix + "Dfg2Ast, result equations", m_resultEquations);

    // Check the stats are consistent
    UASSERT(m_inputEquations
                == m_representable + m_nonRepDType + m_nonRepImpure + m_nonRepTiming + m_nonRepLhs
                       + m_nonRepNode + m_nonRepUnknown + m_nonRepVarRef + m_nonRepWidth,
            "Inconsistent statistics");
}

// Common subexpression elimination
void V3DfgPasses::cse(DfgGraph& dfg, V3DfgCseContext& ctx) {
    DfgVertex::HashCache hashCache;
    DfgVertex::EqualsCache equalsCache;
    std::unordered_multimap<V3Hash, DfgVertex*> verticesWithEqualHashes;

    // In reverse, as the graph is sometimes in reverse topological order already
    dfg.forEachVertexInReverse([&](DfgVertex& vtx) {
        // Don't merge constants
        if (vtx.is<DfgConst>()) return;
        // For everything else...
        const V3Hash hash = vtx.hash(hashCache);
        auto pair = verticesWithEqualHashes.equal_range(hash);
        for (auto it = pair.first, end = pair.second; it != end; ++it) {
            DfgVertex* const candidatep = it->second;
            if (candidatep->equals(vtx, equalsCache)) {
                ++ctx.m_eliminated;
                vtx.replaceWith(candidatep);
                vtx.unlinkDelete(dfg);
                return;
            }
        }
        verticesWithEqualHashes.emplace(hash, &vtx);
    });
}

void V3DfgPasses::removeVars(DfgGraph& dfg, DfgRemoveVarsContext& ctx) {
    dfg.forEachVertex([&](DfgVertex& vtx) {
        // We can eliminate certain redundant DfgVar vertices
        DfgVar* const varp = vtx.cast<DfgVar>();
        if (!varp) return;

        // Can't remove if it has consumers
        if (varp->hasSinks()) return;

        // Can't remove if read in the module and driven here (i.e.: it's an output of the DFG)
        if (varp->hasModRefs() && varp->isDrivenByDfg()) return;

        // Can't remove if only partially driven by the DFG
        if (varp->isDrivenByDfg() && !varp->isDrivenFullyByDfg()) return;

        // Can't remove if referenced externally, or other special reasons
        if (varp->keep()) return;

        // If the driver of this variable has multiple non-variable sinks, then we would need
        // a temporary when rendering the graph. Instead of introducing a temporary, keep the
        // first variable that is driven by that driver
        if (varp->isDrivenByDfg()) {
            DfgVertex* const driverp = varp->source(0);
            unsigned nonVarSinks = 0;
            const DfgVar* firstSinkVarp = nullptr;
            const bool keepFirst = driverp->findSink<DfgVertex>([&](const DfgVertex& sink) {
                if (const DfgVar* const sinkVarp = sink.cast<DfgVar>()) {
                    if (!firstSinkVarp) firstSinkVarp = sinkVarp;
                } else {
                    ++nonVarSinks;
                }
                // We can stop as soon as we found the first var, and 2 non-var sinks
                return firstSinkVarp && nonVarSinks >= 2;
            });
            // Keep this DfgVar if needed
            if (keepFirst && firstSinkVarp == varp) return;
        }

        // OK, we can delete this DfgVar
        ++ctx.m_removed;

        // If not referenced outside the DFG, then also delete the referenced AstVar,
        // as it is now unused.
        if (!varp->hasRefs()) varp->varp()->unlinkFrBack()->deleteTree();

        // Unlink and delete vertex
        vtx.unlinkDelete(dfg);
    });
}

void V3DfgPasses::removeUnused(DfgGraph& dfg) {
    const auto processVertex = [&](DfgVertex& vtx) {
        // Keep variables
        if (vtx.is<DfgVar>()) return false;
        // Keep if it has sinks
        if (vtx.hasSinks()) return false;
        // Unlink and delete vertex
        vtx.unlinkDelete(dfg);
        return true;
    };

    dfg.runToFixedPoint(processVertex);
}

void V3DfgPasses::optimize(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    // There is absolutely nothing useful we can do with a graph of size 2 or less
    if (dfg.size() <= 2) return;

    int passNumber = 0;

    const auto apply = [&](int dumpLevel, const string name, std::function<void()> pass) {
        pass();
        if (dumpDfg() >= dumpLevel) {
            const string strippedName = VString::removeWhitespace(name);
            const string label
                = ctx.prefix() + "pass-" + cvtToStr(passNumber) + "-" + strippedName;
            dfg.dumpDotFilePrefixed(label);
        }
        ++passNumber;
    };

    if (dumpDfg() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "input");
    apply(3, "input         ", [&]() {});
    apply(4, "cse           ", [&]() { cse(dfg, ctx.m_cseContext0); });
    if (v3Global.opt.fDfgPeephole()) {
        apply(4, "peephole      ", [&]() { peephole(dfg, ctx.m_peepholeContext); });
        // Without peephole no variables will be redundant, and we just did CSE, so skip these
        apply(4, "removeVars    ", [&]() { removeVars(dfg, ctx.m_removeVarsContext); });
        apply(4, "cse           ", [&]() { cse(dfg, ctx.m_cseContext1); });
    }
    apply(3, "optimized     ", [&]() { removeUnused(dfg); });
    if (dumpDfg() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "optimized");
}
