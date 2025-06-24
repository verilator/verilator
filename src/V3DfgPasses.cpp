// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3DfgPasses.h"

#include "V3Dfg.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3String.h"

VL_DEFINE_DEBUG_FUNCTIONS;

V3DfgBinToOneHotContext::~V3DfgBinToOneHotContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " BinToOneHot, decoders created",
                     m_decodersCreated);
}

V3DfgBreakCyclesContext::~V3DfgBreakCyclesContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " BreakCycles, made acyclic", m_nFixed);
    V3Stats::addStat("Optimizations, DFG " + m_label + " BreakCycles, improved", m_nImproved);
    V3Stats::addStat("Optimizations, DFG " + m_label + " BreakCycles, left unchanged",
                     m_nUnchanged);
    V3Stats::addStat("Optimizations, DFG " + m_label + " BreakCycles, trivial", m_nTrivial);
    V3Stats::addStat("Optimizations, DFG " + m_label + " BreakCycles, changes applied",
                     m_nImprovements);
}

V3DfgCseContext::~V3DfgCseContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " CSE, expressions eliminated",
                     m_eliminated);
}

V3DfgRegularizeContext::~V3DfgRegularizeContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " Regularize, temporaries introduced",
                     m_temporariesIntroduced);
}

V3DfgEliminateVarsContext::~V3DfgEliminateVarsContext() {
    V3Stats::addStat("Optimizations, DFG " + m_label + " EliminateVars, variables replaced",
                     m_varsReplaced);
    V3Stats::addStat("Optimizations, DFG " + m_label + " EliminateVars, variables removed",
                     m_varsRemoved);
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
    V3Stats::addStat(prefix + "Dfg2Ast, result equations", m_resultEquations);

    // Print the collected patterns
    if (v3Global.opt.stats()) {
        // Label to lowercase, without spaces
        std::string ident = m_label;
        std::transform(ident.begin(), ident.end(), ident.begin(), [](unsigned char c) {  //
            return c == ' ' ? '_' : std::tolower(c);
        });

        // File to dump to
        const std::string filename = v3Global.opt.hierTopDataDir() + "/" + v3Global.opt.prefix()
                                     + "__stats_dfg_patterns__" + ident + ".txt";
        // Open, write, close
        const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
        if (ofp->fail()) v3fatal("Can't write file: " << filename);
        m_patternStats.dump(m_label, *ofp);
    }

    // Check the stats are consistent
    UASSERT(m_inputEquations
                == m_representable + m_nonRepDType + m_nonRepImpure + m_nonRepTiming + m_nonRepLhs
                       + m_nonRepNode + m_nonRepUnknown + m_nonRepVarRef + m_nonRepWidth,
            "Inconsistent statistics");
}

// Common sub-expression elimination
void V3DfgPasses::cse(DfgGraph& dfg, V3DfgCseContext& ctx) {
    // Remove common sub-expressions
    {
        // Used by DfgVertex::hash
        const auto userDataInUse = dfg.userDataInUse();

        DfgVertex::EqualsCache equalsCache;
        std::unordered_map<V3Hash, std::vector<DfgVertex*>> verticesWithEqualHashes;
        verticesWithEqualHashes.reserve(dfg.size());

        // Pre-hash variables, these are all unique, so just set their hash to a unique value
        uint32_t varHash = 0;
        for (DfgVertexVar& vtx : dfg.varVertices()) vtx.user<V3Hash>() = V3Hash{++varHash};

        // Similarly pre-hash constants for speed. While we don't combine constants, we do want
        // expressions using the same constants to be combined, so we do need to hash equal
        // constants to equal values.
        for (DfgConst* const vtxp : dfg.constVertices().unlinkable()) {
            // Delete unused constants while we are at it.
            if (!vtxp->hasSinks()) {
                VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                continue;
            }
            vtxp->user<V3Hash>() = vtxp->num().toHash() + varHash;
        }

        // Combine operation vertices
        for (DfgVertex* const vtxp : dfg.opVertices().unlinkable()) {
            // Delete unused nodes while we are at it.
            if (!vtxp->hasSinks()) {
                vtxp->unlinkDelete(dfg);
                continue;
            }
            const V3Hash hash = vtxp->hash();
            std::vector<DfgVertex*>& vec = verticesWithEqualHashes[hash];
            bool replaced = false;
            for (DfgVertex* const candidatep : vec) {
                if (candidatep->equals(*vtxp, equalsCache)) {
                    ++ctx.m_eliminated;
                    vtxp->replaceWith(candidatep);
                    VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
                    replaced = true;
                    break;
                }
            }
            if (replaced) continue;
            vec.push_back(vtxp);
        }
    }

    // Prune unused nodes
    removeUnused(dfg);
}

void V3DfgPasses::inlineVars(DfgGraph& dfg) {
    for (DfgVertexVar& vtx : dfg.varVertices()) {
        if (DfgVarPacked* const varp = vtx.cast<DfgVarPacked>()) {
            // Don't inline SystemC variables, as SystemC types are not interchangeable with
            // internal types, and hence the variables are not interchangeable either.
            if (varp->hasSinks() && varp->isDrivenFullyByDfg() && !varp->varp()->isSc()) {
                DfgVertex* const driverp = varp->source(0);

                // We must keep the original driver in certain cases, when swapping them would
                // not be functionally or technically (implementation reasons) equivalent:
                // 1. If driven from a SystemC variable (assignment is non-trivial)
                if (DfgVertexVar* const driverVarp = driverp->cast<DfgVarPacked>()) {
                    if (driverVarp->varp()->isSc()) continue;
                }

                varp->forEachSinkEdge([=](DfgEdge& edge) { edge.relinkSource(driverp); });
            }
        }
    }
}

void V3DfgPasses::removeUnused(DfgGraph& dfg) {
    // DfgVertex::user is the next pointer of the work list elements
    const auto userDataInUse = dfg.userDataInUse();

    // Head of work list. Note that we want all next pointers in the list to be non-zero (including
    // that of the last element). This allows as to do two important things: detect if an element
    // is in the list by checking for a non-zero next pointer, and easy prefetching without
    // conditionals. The address of the graph is a good sentinel as it is a valid memory address,
    // and we can easily check for the end of the list.
    DfgVertex* const sentinelp = reinterpret_cast<DfgVertex*>(&dfg);
    DfgVertex* workListp = sentinelp;

    // Add all unused vertices to the work list. This also allocates all DfgVertex::user.
    for (DfgVertex& vtx : dfg.opVertices()) {
        if (vtx.hasSinks()) {
            // This vertex is used. Allocate user, but don't add to work list.
            vtx.setUser<DfgVertex*>(nullptr);
        } else {
            // This vertex is unused. Add to work list.
            vtx.setUser<DfgVertex*>(workListp);
            workListp = &vtx;
        }
    }

    // Process the work list
    while (workListp != sentinelp) {
        // Pick up the head
        DfgVertex* const vtxp = workListp;
        // Detach the head
        workListp = vtxp->getUser<DfgVertex*>();
        // Prefetch next item
        VL_PREFETCH_RW(workListp);
        // If used, then nothing to do, so move on
        if (vtxp->hasSinks()) continue;
        // Add sources of unused vertex to work list
        vtxp->forEachSource([&](DfgVertex& src) {
            // We only remove actual operation vertices in this loop
            if (src.is<DfgConst>() || src.is<DfgVertexVar>()) return;
            // If already in work list then nothing to do
            if (src.getUser<DfgVertex*>()) return;
            // Actually add to work list.
            src.setUser<DfgVertex*>(workListp);
            workListp = &src;
        });
        // Remove the unused vertex
        vtxp->unlinkDelete(dfg);
    }

    // Finally remove unused constants
    for (DfgConst* const vtxp : dfg.constVertices().unlinkable()) {
        if (!vtxp->hasSinks()) VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
    }
}

void V3DfgPasses::binToOneHot(DfgGraph& dfg, V3DfgBinToOneHotContext& ctx) {
    UASSERT(dfg.modulep(), "binToOneHot only works with unscoped DfgGraphs for now");

    const auto userDataInUse = dfg.userDataInUse();

    // Structure to keep track of comparison details
    struct Term final {
        DfgVertex* m_vtxp;  // Vertex to replace
        bool m_inv;  // '!=', instead of '=='
        Term() = default;
        Term(DfgVertex* vtxp, bool inv)
            : m_vtxp{vtxp}
            , m_inv{inv} {}
    };

    // Map from 'value beign compared' -> 'terms', stored in DfgVertex::user()
    using Val2Terms = std::map<uint32_t, std::vector<Term>>;
    // Allocator for Val2Terms, so it's cleaned up on return
    std::deque<Val2Terms> val2TermsAllocator;
    // List of vertices that are used as sources
    std::vector<DfgVertex*> srcps;

    // Only consider input variables from a reasonable range:
    // - not too big to avoid huge tables, you are doomed anyway at that point..
    // - not too small, as it's probably not worth it
    constexpr uint32_t WIDTH_MIN = 7;
    constexpr uint32_t WIDTH_MAX = 20;
    const auto widthOk = [](const DfgVertex* vtxp) {
        const uint32_t width = vtxp->width();
        return WIDTH_MIN <= width && width <= WIDTH_MAX;
    };

    // Do not convert terms that look like they are in a Cond tree
    // the C++ compiler can generate jump tables for these
    const std::function<bool(const DfgVertex*, bool)> useOk
        = [&](const DfgVertex* vtxp, bool inv) -> bool {
        // Go past a single 'Not' sink, which is common
        if (DfgVertex* const sinkp = vtxp->singleSink()) {
            if (sinkp->is<DfgNot>()) return useOk(sinkp, !inv);
        }
        return !vtxp->findSink<DfgCond>([vtxp, inv](const DfgCond& sink) {
            if (sink.condp() != vtxp) return false;
            return inv ? sink.thenp()->is<DfgCond>() : sink.elsep()->is<DfgCond>();
        });
    };

    // Look at all comparison nodes and build the 'Val2Terms' map for each source vertex
    uint32_t nTerms = 0;
    for (DfgVertex& vtx : dfg.opVertices()) {
        DfgVertex* srcp = nullptr;
        uint32_t val = 0;
        bool inv = false;
        if (DfgEq* const eqp = vtx.cast<DfgEq>()) {
            DfgConst* const constp = eqp->lhsp()->cast<DfgConst>();
            if (!constp || !widthOk(constp) || !useOk(eqp, false)) continue;
            srcp = eqp->rhsp();
            val = constp->toU32();
            inv = false;
        } else if (DfgNeq* const neqp = vtx.cast<DfgNeq>()) {
            DfgConst* const constp = neqp->lhsp()->cast<DfgConst>();
            if (!constp || !widthOk(constp) || !useOk(neqp, true)) continue;
            srcp = neqp->rhsp();
            val = constp->toU32();
            inv = true;
        } else if (DfgRedAnd* const redAndp = vtx.cast<DfgRedAnd>()) {
            srcp = redAndp->srcp();
            if (!widthOk(srcp) || !useOk(redAndp, false)) continue;
            val = (1U << srcp->width()) - 1;
            inv = false;
        } else if (DfgRedOr* const redOrp = vtx.cast<DfgRedOr>()) {
            srcp = redOrp->srcp();
            if (!widthOk(srcp) || !useOk(redOrp, true)) continue;
            val = 0;
            inv = true;
        } else {
            // Not a comparison-like vertex
            continue;
        }
        // Grab the Val2Terms entry
        Val2Terms*& val2Termspr = srcp->user<Val2Terms*>();
        if (!val2Termspr) {
            // Remeber and allocate on first encounter
            srcps.emplace_back(srcp);
            val2TermsAllocator.emplace_back();
            val2Termspr = &val2TermsAllocator.back();
        }
        // Record term
        (*val2Termspr)[val].emplace_back(&vtx, inv);
        ++nTerms;
    }

    // Somewhat arbitrarily, only apply if more than 64 unique comparisons are required
    constexpr uint32_t TERM_LIMIT = 65;
    // This should hold, otherwise we do redundant work gathering terms that will never be used
    static_assert((1U << WIDTH_MIN) >= TERM_LIMIT, "TERM_LIMIT too big relative to 2**WIDTH_MIN");

    // Fast path exit if we surely don't need to convet anything
    if (nTerms < TERM_LIMIT) return;

    // Sequence numbers for name generation
    size_t nTables = 0;

    // Create decoders for each srcp
    for (DfgVertex* const srcp : srcps) {
        const Val2Terms& val2Terms = *srcp->getUser<Val2Terms*>();

        // If not enough terms in this vertex, ignore
        if (val2Terms.size() < TERM_LIMIT) continue;

        // Width of the decoded binary value
        const uint32_t width = srcp->width();
        // Number of bits in the input operand
        const uint32_t nBits = 1U << width;

        // Construct the decoder by converting many "const == vtx" by:
        // - Adding a single decoder block, where 'tab' is zero initialized:
        //     always_comb begin
        //        tab[pre] = 0;
        //        tab[vtx] = 1;
        //        pre = vtx;
        //     end
        //   We mark 'pre' so the write is ignored during scheduling, so this
        //   won't cause a combinational cycle.
        //   Note that albeit this looks like partial udpates to 'tab', the
        //   actual result is that only one value in 'tab' is ever one, while
        //   all the others are always zero.
        // - and replace the comparisons with 'tab[const]'

        FileLine* const flp = srcp->fileline();

        // Required data types
        AstNodeDType* const idxDTypep = srcp->dtypep();
        AstNodeDType* const bitDTypep = DfgVertex::dtypeForWidth(1);
        AstUnpackArrayDType* const tabDTypep = new AstUnpackArrayDType{
            flp, bitDTypep, new AstRange{flp, static_cast<int>(nBits - 1), 0}};
        v3Global.rootp()->typeTablep()->addTypesp(tabDTypep);

        // The index variable
        DfgVarPacked* const idxVtxp = [&]() {
            // If there is an existing result variable, use that, otherwise create a new variable
            DfgVarPacked* varp = srcp->getResultVar();
            if (!varp) {
                const std::string name = dfg.makeUniqueName("BinToOneHot_Idx", nTables);
                varp = dfg.makeNewVar(flp, name, idxDTypep, nullptr)->as<DfgVarPacked>();
                varp->varp()->isInternal(true);
                varp->addDriver(flp, 0, srcp);
            }
            varp->setHasModRefs();
            return varp;
        }();
        // The previous index variable - we don't need a vertex for this
        AstVar* const preVarp = [&]() {
            const std::string name = dfg.makeUniqueName("BinToOneHot_Pre", nTables);
            AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, idxDTypep};
            dfg.modulep()->addStmtsp(varp);
            varp->isInternal(true);
            varp->noReset(true);
            varp->setIgnoreSchedWrite();
            return varp;
        }();
        // The table variable
        DfgVarArray* const tabVtxp = [&]() {
            const std::string name = dfg.makeUniqueName("BinToOneHot_Tab", nTables);
            DfgVarArray* const varp
                = dfg.makeNewVar(flp, name, tabDTypep, nullptr)->as<DfgVarArray>();
            varp->varp()->isInternal(true);
            varp->varp()->noReset(true);
            varp->setHasModRefs();
            return varp;
        }();

        ++nTables;
        ++ctx.m_decodersCreated;

        // Initialize 'tab' and 'pre' variables statically
        AstInitialStatic* const initp = new AstInitialStatic{flp, nullptr};
        dfg.modulep()->addStmtsp(initp);
        {  // pre = 0
            initp->addStmtsp(new AstAssign{
                flp,  //
                new AstVarRef{flp, preVarp, VAccess::WRITE},  //
                new AstConst{flp, AstConst::WidthedValue{}, static_cast<int>(width), 0}});
        }
        {  // tab.fill(0)
            AstCMethodHard* const callp = new AstCMethodHard{
                flp, new AstVarRef{flp, tabVtxp->varp(), VAccess::WRITE}, "fill"};
            callp->addPinsp(new AstConst{flp, AstConst::BitFalse{}});
            callp->dtypeSetVoid();
            initp->addStmtsp(callp->makeStmt());
        }

        // Build the decoder logic
        AstAlways* const logicp = new AstAlways{flp, VAlwaysKwd::ALWAYS_COMB, nullptr, nullptr};
        dfg.modulep()->addStmtsp(logicp);
        {  // tab[pre] = 0;
            logicp->addStmtsp(new AstAssign{
                flp,  //
                new AstArraySel{flp, new AstVarRef{flp, tabVtxp->varp(), VAccess::WRITE},
                                new AstVarRef{flp, preVarp, VAccess::READ}},  //
                new AstConst{flp, AstConst::BitFalse{}}});
        }
        {  // tab[idx] = 1
            logicp->addStmtsp(new AstAssign{
                flp,  //
                new AstArraySel{flp, new AstVarRef{flp, tabVtxp->varp(), VAccess::WRITE},
                                new AstVarRef{flp, idxVtxp->varp(), VAccess::READ}},  //
                new AstConst{flp, AstConst::BitTrue{}}});
        }
        {  // pre = idx
            logicp->addStmtsp(new AstAssign{flp,  //
                                            new AstVarRef{flp, preVarp, VAccess::WRITE},  //
                                            new AstVarRef{flp, idxVtxp->varp(), VAccess::READ}});
        }

        // Replace terms with ArraySels
        for (const auto& pair : val2Terms) {
            const uint32_t val = pair.first;
            const std::vector<Term>& terms = pair.second;
            // Create the ArraySel
            FileLine* const aflp = terms.front().m_vtxp->fileline();
            DfgArraySel* const aselp = new DfgArraySel{dfg, aflp, bitDTypep};
            aselp->fromp(tabVtxp);
            aselp->bitp(new DfgConst{dfg, aflp, width, val});
            // The inverted value, if needed
            DfgNot* notp = nullptr;
            // Repalce the terms
            for (const Term& term : terms) {
                if (term.m_inv) {
                    if (!notp) {
                        notp = new DfgNot{dfg, aflp, bitDTypep};
                        notp->srcp(aselp);
                    }
                    term.m_vtxp->replaceWith(notp);
                } else {
                    term.m_vtxp->replaceWith(aselp);
                }
                VL_DO_DANGLING(term.m_vtxp->unlinkDelete(dfg), term.m_vtxp);
            }
        }
    }
}

void V3DfgPasses::eliminateVars(DfgGraph& dfg, V3DfgEliminateVarsContext& ctx) {
    const auto userDataInUse = dfg.userDataInUse();

    // Head of work list. Note that we want all next pointers in the list to be non-zero
    // (including that of the last element). This allows us to do two important things: detect
    // if an element is in the list by checking for a non-zero next pointer, and easy
    // prefetching without conditionals. The address of the graph is a good sentinel as it is a
    // valid memory address, and we can easily check for the end of the list.
    DfgVertex* const sentinelp = reinterpret_cast<DfgVertex*>(&dfg);
    DfgVertex* workListp = sentinelp;

    // Add all variables to the initial work list
    for (DfgVertexVar& vtx : dfg.varVertices()) {
        vtx.setUser<DfgVertex*>(workListp);
        workListp = &vtx;
    }

    const auto addToWorkList = [&](DfgVertex& vtx) {
        // If already in work list then nothing to do
        DfgVertex*& nextInWorklistp = vtx.user<DfgVertex*>();
        if (nextInWorklistp) return;
        // Actually add to work list.
        nextInWorklistp = workListp;
        workListp = &vtx;
    };

    // List of variables (AstVar or AstVarScope) we are replacing
    std::vector<AstNode*> replacedVariables;
    // AstVar::user1p() : AstVar* -> The replacement variables
    // AstVarScope::user1p() : AstVarScope* -> The replacement variables
    const VNUser1InUse user1InUse;

    // Process the work list
    while (workListp != sentinelp) {
        // Pick up the head of the work list
        DfgVertex* const vtxp = workListp;
        // Detach the head
        workListp = vtxp->getUser<DfgVertex*>();
        // Reset user pointer so it can be added back to the work list later
        vtxp->setUser<DfgVertex*>(nullptr);
        // Prefetch next item
        VL_PREFETCH_RW(workListp);

        // Remove unused non-variable vertices
        if (!vtxp->is<DfgVertexVar>() && !vtxp->hasSinks()) {
            // Add sources of removed vertex to work list
            vtxp->forEachSource(addToWorkList);
            // Remove the unused vertex
            vtxp->unlinkDelete(dfg);
            continue;
        }

        // We can only eliminate DfgVarPacked vertices at the moment
        DfgVarPacked* const varp = vtxp->cast<DfgVarPacked>();
        if (!varp) continue;

        // Can't remove if it has external drivers
        if (!varp->isDrivenFullyByDfg()) continue;

        // Can't remove if must be kept (including external, non module references)
        if (varp->keep()) continue;

        // Can't remove if referenced in other DFGs of the same module (otherwise might rm twice)
        if (varp->hasDfgRefs()) continue;

        // If it has multiple sinks, it can't be eliminated
        if (varp->hasMultipleSinks()) continue;

        if (!varp->hasModRefs()) {
            // If it is only referenced in this DFG, it can be removed
            ++ctx.m_varsRemoved;
            varp->replaceWith(varp->source(0));
            varp->nodep()->unlinkFrBack()->deleteTree();
        } else if (DfgVarPacked* const driverp = varp->source(0)->cast<DfgVarPacked>()) {
            // If it's driven from another variable, it can be replaced by that. However, we do not
            // want to propagate SystemC variables into the design.
            if (driverp->varp()->isSc()) continue;
            // Mark it for replacement
            ++ctx.m_varsReplaced;
            UASSERT_OBJ(!varp->hasSinks(), varp, "Variable inlining should make this impossible");
            // Grab the AstVar/AstVarScope
            AstNode* const nodep = varp->nodep();
            UASSERT_OBJ(!nodep->user1p(), nodep, "Replacement already exists");
            replacedVariables.emplace_back(nodep);
            nodep->user1p(driverp->nodep());
        } else {
            // Otherwise this *is* the canonical var
            continue;
        }

        // Add sources of redundant variable to the work list
        vtxp->forEachSource(addToWorkList);
        // Remove the redundant variable
        vtxp->unlinkDelete(dfg);
    }

    // Job done if no replacements possible
    if (replacedVariables.empty()) return;

    // Apply variable replacements
    if (AstModule* const modp = dfg.modulep()) {
        modp->foreach([&](AstVarRef* refp) {
            AstVar* varp = refp->varp();
            while (AstVar* const replacep = VN_AS(varp->user1p(), Var)) varp = replacep;
            refp->varp(varp);
        });
    } else {
        v3Global.rootp()->foreach([&](AstVarRef* refp) {
            AstVarScope* vscp = refp->varScopep();
            while (AstVarScope* const replacep = VN_AS(vscp->user1p(), VarScope)) vscp = replacep;
            refp->varScopep(vscp);
            refp->varp(vscp->varp());
        });
    }

    // Remove the replaced variables
    for (AstNode* const nodep : replacedVariables) nodep->unlinkFrBack()->deleteTree();
}

void V3DfgPasses::optimize(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    // There is absolutely nothing useful we can do with a graph of size 2 or less
    if (dfg.size() <= 2) return;

    int passNumber = 0;

    const auto apply = [&](int dumpLevel, const string& name, std::function<void()> pass) {
        pass();
        if (dumpDfgLevel() >= dumpLevel) {
            const string strippedName = VString::removeWhitespace(name);
            const string label
                = ctx.prefix() + "pass-" + cvtToStr(passNumber) + "-" + strippedName;
            dfg.dumpDotFilePrefixed(label);
        }
        ++passNumber;
    };

    if (dumpDfgLevel() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "input");
    apply(3, "input           ", [&]() {});
    apply(4, "inlineVars      ", [&]() { inlineVars(dfg); });
    apply(4, "cse0            ", [&]() { cse(dfg, ctx.m_cseContext0); });
    if (dfg.modulep()) {
        apply(4, "binToOneHot     ", [&]() { binToOneHot(dfg, ctx.m_binToOneHotContext); });
    }
    if (v3Global.opt.fDfgPeephole()) {
        apply(4, "peephole        ", [&]() { peephole(dfg, ctx.m_peepholeContext); });
        // We just did CSE above, so without peephole there is no need to run it again these
        apply(4, "cse1            ", [&]() { cse(dfg, ctx.m_cseContext1); });
    }
    // Accumulate patterns for reporting
    if (v3Global.opt.stats()) ctx.m_patternStats.accumulate(dfg);
    apply(4, "regularize", [&]() { regularize(dfg, ctx.m_regularizeContext); });
    if (dumpDfgLevel() >= 8) dfg.dumpDotAllVarConesPrefixed(ctx.prefix() + "optimized");
}
