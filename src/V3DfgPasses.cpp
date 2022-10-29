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
    DfgVertex::EqualsCache equalsCache;
    std::unordered_map<V3Hash, std::vector<DfgVertex*>> verticesWithEqualHashes;
    verticesWithEqualHashes.reserve(dfg.size());

    // Used by DfgVertex::hash
    const auto userDataInUse = dfg.userDataInUse();

    // Pre-hash variables for speed, these are all unique, so just set their hash to a unique value
    uint32_t varHash = 0;
    for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();
        vtxp->user<V3Hash>() = V3Hash{++varHash};
    }

    // Similarly pre-hash constants for speed. While we don't combine constants, we do want
    // expressions using the same constants to be combined, so we do need to hash equal constants
    // to equal values.
    for (DfgConst *vtxp = dfg.constVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();
        // Get rid of unused constants while we are at it
        if (!vtxp->hasSinks()) {
            vtxp->unlinkDelete(dfg);
            continue;
        }
        vtxp->user<V3Hash>() = vtxp->num().toHash();
    }

    // Combine operation vertices
    for (DfgVertex *vtxp = dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();
        // Get rid of unused operations while we are at it
        if (!vtxp->hasSinks()) {
            vtxp->unlinkDelete(dfg);
            continue;
        }
        const V3Hash hash = vtxp->hash();
        if (VL_LIKELY(nextp)) VL_PREFETCH_RW(nextp);
        std::vector<DfgVertex*>& vec = verticesWithEqualHashes[hash];
        bool replaced = false;
        for (DfgVertex* const candidatep : vec) {
            if (candidatep->equals(*vtxp, equalsCache)) {
                ++ctx.m_eliminated;
                vtxp->replaceWith(candidatep);
                vtxp->unlinkDelete(dfg);
                replaced = true;
                break;
            }
        }
        if (replaced) continue;
        vec.push_back(vtxp);
    }
}

void V3DfgPasses::inlineVars(DfgGraph& dfg) {
    for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();
        if (DfgVarPacked* const varp = vtxp->cast<DfgVarPacked>()) {
            // Don't inline SystemC variables, as SystemC types are not interchangeable with
            // internal types, and hence the variables are not interchangeable either.
            if (varp->hasSinks() && varp->isDrivenFullyByDfg() && !varp->varp()->isSc()) {
                DfgVertex* const driverp = varp->source(0);

                // If driven from a SystemC variable, don't inline this variable
                if (DfgVertexVar* const driverVarp = driverp->cast<DfgVarPacked>()) {
                    if (driverVarp->varp()->isSc()) continue;
                }

                varp->forEachSinkEdge([=](DfgEdge& edge) {
                    // If sink is a SystemC variable, don't inline that sink
                    if (DfgVertexVar* const sinkVarp = edge.sinkp()->cast<DfgVarPacked>()) {
                        if (sinkVarp->varp()->isSc()) return;
                    }
                    edge.relinkSource(driverp);
                });
            }
        }
    }
}

void V3DfgPasses::removeVars(DfgGraph& dfg, DfgRemoveVarsContext& ctx) {
    for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();

        // We can only eliminate DfgVarPacked vertices at the moment
        DfgVarPacked* const varp = vtxp->cast<DfgVarPacked>();
        if (!varp) continue;

        // Can't remove if it has consumers
        if (varp->hasSinks()) continue;

        // Can't remove if read in the module and driven here (i.e.: it's an output of the DFG)
        if (varp->hasModRefs() && varp->isDrivenByDfg()) continue;

        // Can't remove if only partially driven by the DFG
        if (varp->isDrivenByDfg() && !varp->isDrivenFullyByDfg()) continue;

        // Can't remove if referenced externally, or other special reasons
        if (varp->keep()) continue;

        // If the driver of this variable has multiple non-variable sinks, then we would need
        // a temporary when rendering the graph. Instead of introducing a temporary, keep the
        // first variable that is driven by that driver
        if (varp->isDrivenByDfg()) {
            DfgVertex* const driverp = varp->source(0);
            unsigned nonVarSinks = 0;
            const DfgVarPacked* firstSinkVarp = nullptr;
            const bool keepFirst = driverp->findSink<DfgVertex>([&](const DfgVertex& sink) {
                if (const DfgVarPacked* const sinkVarp = sink.cast<DfgVarPacked>()) {
                    if (!firstSinkVarp) firstSinkVarp = sinkVarp;
                } else {
                    ++nonVarSinks;
                }
                // We can stop as soon as we found the first var, and 2 non-var sinks
                return firstSinkVarp && nonVarSinks >= 2;
            });
            // Keep this DfgVarPacked if needed
            if (keepFirst && firstSinkVarp == varp) continue;
        }

        // OK, we can delete this DfgVarPacked
        ++ctx.m_removed;

        // If not referenced outside the DFG, then also delete the referenced AstVar,
        // as it is now unused.
        if (!varp->hasRefs()) varp->varp()->unlinkFrBack()->deleteTree();

        // Unlink and delete vertex
        varp->unlinkDelete(dfg);
    }
}

void V3DfgPasses::removeUnused(DfgGraph& dfg) {
    // Iteratively remove operation vertices
    while (true) {
        // Do one pass over the graph.
        bool changed = false;
        for (DfgVertex *vtxp = dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            if (!vtxp->hasSinks()) {
                changed = true;
                vtxp->unlinkDelete(dfg);
            }
        }
        if (!changed) break;
        // Do another pass in the opposite direction. Alternating directions reduces
        // the pathological complexity with left/right leaning trees.
        changed = false;
        for (DfgVertex *vtxp = dfg.opVerticesRbeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesPrev();
            if (!vtxp->hasSinks()) {
                changed = true;
                vtxp->unlinkDelete(dfg);
            }
        }
        if (!changed) break;
    }

    // Finally remove unused constants
    for (DfgConst *vtxp = dfg.constVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
        nextp = vtxp->verticesNext();
        if (!vtxp->hasSinks()) vtxp->unlinkDelete(dfg);
    }
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
    apply(4, "inlineVars    ", [&]() { inlineVars(dfg); });
    if (v3Global.opt.fDfgPeephole()) {
        apply(4, "peephole      ", [&]() { peephole(dfg, ctx.m_peepholeContext); });
    }
    apply(4, "cse           ", [&]() { cse(dfg, ctx.m_cseContext1); });
    apply(4, "removeVars    ", [&]() { removeVars(dfg, ctx.m_removeVarsContext); });
    apply(3, "optimized     ", [&]() { removeUnused(dfg); });
    if (dumpDfg() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "optimized");
}
