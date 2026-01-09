// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementations of simple passes over DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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

void V3DfgPasses::inlineVars(DfgGraph& dfg) {
    for (DfgVertexVar& vtx : dfg.varVertices()) {
        // Nothing to inline it into
        if (!vtx.hasSinks()) continue;
        // Nohting to inline
        DfgVertex* const srcp = vtx.srcp();
        if (!srcp) continue;
        // Value can differ from driver
        if (vtx.isVolatile()) continue;
        // Partial driver cannot be inlined
        if (srcp->is<DfgVertexSplice>()) continue;
        if (srcp->is<DfgUnitArray>()) continue;
        // Okie dokie, here we go ...
        vtx.replaceWith(srcp);
    }
}

void V3DfgPasses::removeUnused(DfgGraph& dfg) {
    // Worklist based algoritm
    DfgWorklist workList{dfg};

    // Add all unused operation vertices to the work list
    for (DfgVertex& vtx : dfg.opVertices()) {
        if (vtx.hasSinks()) continue;
        // This vertex is unused. Add to work list.
        workList.push_front(vtx);
    }

    // Also add all unused temporaries created during synthesis
    for (DfgVertexVar& vtx : dfg.varVertices()) {
        if (!vtx.tmpForp()) continue;
        if (vtx.hasSinks()) continue;
        if (vtx.hasDfgRefs()) continue;
        // This vertex is unused. Add to work list.
        workList.push_front(vtx);
    }

    // Process the work list
    workList.foreach([&](DfgVertex& vtx) {
        // DfgLogic should have been synthesized or removed
        UASSERT_OBJ(!vtx.is<DfgLogic>(), &vtx, "Should not be DfgLogic");
        // If used, then nothing to do, so move on
        if (vtx.hasSinks()) return;
        // If temporary used in another graph, we need to keep it
        if (const DfgVertexVar* const varp = vtx.cast<DfgVertexVar>()) {
            UASSERT_OBJ(varp->tmpForp(), varp, "Non-temporary variable should not be visited");
            if (varp->hasDfgRefs()) return;
        }
        // Add sources of unused vertex to work list
        vtx.foreachSource([&](DfgVertex& src) {
            // We only remove actual operation vertices and synthesis temporaries in this loop
            if (src.is<DfgConst>()) return false;
            const DfgVertexVar* const varp = src.cast<DfgVertexVar>();
            if (varp && !varp->tmpForp()) return false;
            // Add source to workList
            workList.push_front(src);
            return false;
        });
        // Remove the unused vertex
        vtx.unlinkDelete(dfg);
    });

    // Remove unused and undriven variable vertices
    for (DfgVertexVar* const vtxp : dfg.varVertices().unlinkable()) {
        if (!vtxp->hasSinks() && !vtxp->srcp()) VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
    }

    // Finally remove unused constants
    for (DfgConst* const vtxp : dfg.constVertices().unlinkable()) {
        if (!vtxp->hasSinks()) VL_DO_DANGLING(vtxp->unlinkDelete(dfg), vtxp);
    }
}

void V3DfgPasses::binToOneHot(DfgGraph& dfg, V3DfgBinToOneHotContext& ctx) {
    if (!dfg.modulep()) return;  // binToOneHot only works with unscoped DfgGraphs for now

    // Structure to keep track of comparison details
    struct Term final {
        DfgVertex* m_vtxp = nullptr;  // Vertex to replace
        bool m_inv = false;  // '!=', instead of '=='
        Term() = default;
        Term(DfgVertex* vtxp, bool inv)
            : m_vtxp{vtxp}
            , m_inv{inv} {}
    };

    // List of vertices that are used as sources
    std::vector<DfgVertex*> srcps;

    // Map from 'vertices' -> 'value beign compared' -> 'terms'
    using Val2Terms = std::map<uint32_t, std::vector<Term>>;
    DfgUserMap<Val2Terms> vtx2Val2Terms = dfg.makeUserMap<Val2Terms>();

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
        const bool condTree = vtxp->foreachSink([&](const DfgVertex& sink) {
            const DfgCond* const condp = sink.cast<DfgCond>();
            if (!condp) return false;
            if (condp->condp() != vtxp) return false;
            return inv ? condp->thenp()->is<DfgCond>() : condp->elsep()->is<DfgCond>();
        });
        return !condTree;
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
        } else if (DfgSel* const selp = vtx.cast<DfgSel>()) {
            // Special case: Sel(ShiftL(1, src),lsb,width=1)
            if (selp->width() != 1) continue;
            DfgShiftL* const shiftLp = selp->fromp()->cast<DfgShiftL>();
            if (!shiftLp) continue;
            DfgConst* const constp = shiftLp->lhsp()->cast<DfgConst>();
            if (!constp || !useOk(selp, false)) continue;
            if (!constp->hasValue(1)) continue;
            srcp = shiftLp->rhsp();
            if (!widthOk(srcp)) continue;
            val = selp->lsb();
            inv = false;
        } else {
            // Not a comparison-like vertex
            continue;
        }
        // Grab Val2Terms for this vertex
        Val2Terms& val2Terms = vtx2Val2Terms[srcp];
        // Remeber and on first encounter
        if (val2Terms.empty()) srcps.emplace_back(srcp);
        // Record term
        val2Terms[val].emplace_back(&vtx, inv);
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
        const Val2Terms& val2Terms = vtx2Val2Terms[srcp];

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
        const DfgDataType& idxDType = srcp->dtype();
        const DfgDataType& bitDType = DfgDataType::packed(1);
        const DfgDataType& tabDType = DfgDataType::array(bitDType, nBits);

        // The index variable
        AstVar* const idxVarp = [&]() {
            // If there is an existing result variable, use that, otherwise create a new variable
            DfgVarPacked* varp = nullptr;
            if (DfgVertexVar* const vp = srcp->getResultVar()) {
                varp = vp->as<DfgVarPacked>();
            } else {
                const std::string name = dfg.makeUniqueName("BinToOneHot_Idx", nTables);
                varp = dfg.makeNewVar(flp, name, idxDType, nullptr)->as<DfgVarPacked>();
                varp->varp()->isInternal(true);
                varp->srcp(srcp);
            }
            varp->setHasModRdRefs();
            return varp->varp();
        }();
        // The previous index variable - we don't need a vertex for this
        AstVar* const preVarp = [&]() {
            const std::string name = dfg.makeUniqueName("BinToOneHot_Pre", nTables);
            AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, idxDType.astDtypep()};
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
                = dfg.makeNewVar(flp, name, tabDType, nullptr)->as<DfgVarArray>();
            varp->varp()->isInternal(true);
            varp->varp()->noReset(true);
            varp->setHasModWrRefs();
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
                flp, new AstVarRef{flp, tabVtxp->varp(), VAccess::WRITE}, VCMethod::UNPACKED_FILL};
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
                                new AstVarRef{flp, idxVarp, VAccess::READ}},  //
                new AstConst{flp, AstConst::BitTrue{}}});
        }
        {  // pre = idx
            logicp->addStmtsp(new AstAssign{flp,  //
                                            new AstVarRef{flp, preVarp, VAccess::WRITE},  //
                                            new AstVarRef{flp, idxVarp, VAccess::READ}});
        }

        // Replace terms with ArraySels
        for (const auto& pair : val2Terms) {
            const uint32_t val = pair.first;
            const std::vector<Term>& terms = pair.second;
            // Create the ArraySel
            FileLine* const aflp = terms.front().m_vtxp->fileline();
            DfgArraySel* const aselp = new DfgArraySel{dfg, aflp, bitDType};
            aselp->fromp(tabVtxp);
            aselp->bitp(new DfgConst{dfg, aflp, width, val});
            // The inverted value, if needed
            DfgNot* notp = nullptr;
            // Repalce the terms
            for (const Term& term : terms) {
                if (term.m_inv) {
                    if (!notp) {
                        notp = new DfgNot{dfg, aflp, bitDType};
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

void V3DfgPasses::optimize(DfgGraph& dfg, V3DfgContext& ctx) {
    // There is absolutely nothing useful we can do with a graph of size 2 or less
    if (dfg.size() <= 2) return;

    const auto run = [&](const std::string& name, bool dump, std::function<void()> pass) {
        // Apply the pass
        pass();
        // Debug dump
        if (dump) dfg.dumpDotFilePrefixed(ctx.prefix() + "opt-" + VString::removeWhitespace(name));
        // Internal type check
        if (v3Global.opt.debugCheck()) V3DfgPasses::typeCheck(dfg);
    };

    // Currend debug dump level
    const uint32_t dumpLvl = dumpDfgLevel();

    // Run passes
    run("input       ", dumpLvl >= 3, [&]() { /* debug dump only */ });
    run("inlineVars  ", dumpLvl >= 4, [&]() { inlineVars(dfg); });
    run("cse0        ", dumpLvl >= 4, [&]() { cse(dfg, ctx.m_cseContext0); });
    run("binToOneHot ", dumpLvl >= 4, [&]() { binToOneHot(dfg, ctx.m_binToOneHotContext); });
    run("peephole    ", dumpLvl >= 4, [&]() { peephole(dfg, ctx.m_peepholeContext); });
    run("cse1        ", dumpLvl >= 4, [&]() { cse(dfg, ctx.m_cseContext1); });
    run("output      ", dumpLvl >= 3, [&]() { /* debug dump only */ });

    // Accumulate patterns for reporting
    if (v3Global.opt.stats()) ctx.m_patternStats.accumulate(dfg);
}
