// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Convert DfgGraph back to AstModule. We recursively construct AstNodeExpr expressions for each
// DfgVertex which represents a storage location (e.g.: DfgVarPacked), or has multiple sinks
// without driving a storage location (and hence needs a temporary variable to duplication). The
// recursion stops when we reach a DfgVertex representing a storage location (e.g.: DfgVarPacked),
// or a vertex that that has multiple sinks (as these nodes will have a [potentially new temporary]
// corresponding// storage location). Redundant variables (those whose source vertex drives
// multiple variables) are eliminated when possible. Vertices driving multiple variables are
// rendered once, driving an arbitrarily (but deterministically) chosen canonical variable, and the
// corresponding redundant variables are assigned from the canonical variable.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3UniqueNames.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create an AstNodeExpr out of a DfgVertex. For most AstNodeExpr subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename Node, typename Vertex, typename... Ops>
Node* makeNode(const Vertex* vtxp, Ops... ops) {
    Node* const nodep = new Node{vtxp->fileline(), ops...};
    UASSERT_OBJ(nodep->width() == static_cast<int>(vtxp->width()), vtxp,
                "Incorrect width in AstNode created from DfgVertex "
                    << vtxp->typeName() << ": " << nodep->width() << " vs " << vtxp->width());
    return nodep;
}

//======================================================================
// Vertices needing special conversion

template <>
AstCountOnes* makeNode<AstCountOnes, DfgCountOnes, AstNodeExpr*>(  //
    const DfgCountOnes* vtxp, AstNodeExpr* op1) {
    AstCountOnes* const nodep = new AstCountOnes{vtxp->fileline(), op1};
    // Set dtype same as V3Width
    nodep->dtypeSetLogicSized(32, VSigning::UNSIGNED);
    return nodep;
}

template <>
AstExtend* makeNode<AstExtend, DfgExtend, AstNodeExpr*>(  //
    const DfgExtend* vtxp, AstNodeExpr* op1) {
    return new AstExtend{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstExtendS* makeNode<AstExtendS, DfgExtendS, AstNodeExpr*>(  //
    const DfgExtendS* vtxp, AstNodeExpr* op1) {
    return new AstExtendS{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstShiftL* makeNode<AstShiftL, DfgShiftL, AstNodeExpr*, AstNodeExpr*>(  //
    const DfgShiftL* vtxp, AstNodeExpr* op1, AstNodeExpr* op2) {
    return new AstShiftL{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftR* makeNode<AstShiftR, DfgShiftR, AstNodeExpr*, AstNodeExpr*>(  //
    const DfgShiftR* vtxp, AstNodeExpr* op1, AstNodeExpr* op2) {
    return new AstShiftR{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftRS* makeNode<AstShiftRS, DfgShiftRS, AstNodeExpr*, AstNodeExpr*>(  //
    const DfgShiftRS* vtxp, AstNodeExpr* op1, AstNodeExpr* op2) {
    return new AstShiftRS{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

//======================================================================
// Currently unhandled nodes - see corresponding AstToDfg functions
// LCOV_EXCL_START
template <>
AstCCast* makeNode<AstCCast, DfgCCast, AstNodeExpr*>(const DfgCCast* vtxp, AstNodeExpr*) {
    vtxp->v3fatalSrc("not implemented");
    VL_UNREACHABLE;
    return nullptr;  // LCOV_EXCL_LINE
}
template <>
AstAtoN* makeNode<AstAtoN, DfgAtoN, AstNodeExpr*>(const DfgAtoN* vtxp, AstNodeExpr*) {
    vtxp->v3fatalSrc("not implemented");
    VL_UNREACHABLE;
    return nullptr;  // LCOV_EXCL_LINE
}
template <>
AstCompareNN*
makeNode<AstCompareNN, DfgCompareNN, AstNodeExpr*, AstNodeExpr*>(const DfgCompareNN* vtxp,
                                                                 AstNodeExpr*, AstNodeExpr*) {
    vtxp->v3fatalSrc("not implemented");
    VL_UNREACHABLE;
    return nullptr;  // LCOV_EXCL_LINE
}
template <>
AstSliceSel* makeNode<AstSliceSel, DfgSliceSel, AstNodeExpr*, AstNodeExpr*, AstNodeExpr*>(
    const DfgSliceSel* vtxp, AstNodeExpr*, AstNodeExpr*, AstNodeExpr*) {
    vtxp->v3fatalSrc("not implemented");
    VL_UNREACHABLE;
    return nullptr;  // LCOV_EXCL_LINE
}
// LCOV_EXCL_STOP

}  // namespace

class DfgToAstVisitor final : DfgVisitor {
    // STATE

    AstModule* const m_modp;  // The parent/result module
    V3DfgOptimizationContext& m_ctx;  // The optimization context for stats
    AstNodeExpr* m_resultp = nullptr;  // The result node of the current traversal
    // Map from DfgVertex to the AstVar holding the value of that DfgVertex after conversion
    std::unordered_map<const DfgVertex*, AstVar*> m_resultVars;
    // Map from an AstVar, to the canonical AstVar that can be substituted for that AstVar
    std::unordered_map<AstVar*, AstVar*> m_canonVars;
    V3UniqueNames m_tmpNames{"__VdfgTmp"};  // For generating temporary names

    // METHODS

    AstNodeExpr* convertDfgVertexToAstNodeExpr(DfgVertex* vtxp) {
        UASSERT_OBJ(!m_resultp, vtxp, "Result already computed");
        UASSERT_OBJ(!vtxp->hasMultipleSinks() || vtxp->is<DfgVertexVar>()
                        || vtxp->is<DfgArraySel>() || vtxp->is<DfgConst>(),
                    vtxp, "Intermediate DFG value with multiple uses");
        iterate(vtxp);
        UASSERT_OBJ(m_resultp, vtxp, "Missing result");
        AstNodeExpr* const resultp = m_resultp;
        m_resultp = nullptr;
        return resultp;
    }

    void addResultEquation(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        m_modp->addStmtsp(new AstAssignW{flp, lhsp, rhsp});
        ++m_ctx.m_resultEquations;
    }

    void convertVarDriver(const DfgVarPacked* dfgVarp) {
        if (dfgVarp->isDrivenFullyByDfg()) {
            // Whole variable is driven. Render driver and assign directly to whole variable.
            FileLine* const flp = dfgVarp->driverFileLine(0);
            AstVarRef* const lhsp = new AstVarRef{flp, dfgVarp->varp(), VAccess::WRITE};
            AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(dfgVarp->source(0));
            addResultEquation(flp, lhsp, rhsp);
        } else {
            // Variable is driven partially. Render each driver as a separate assignment.
            dfgVarp->forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {
                UASSERT_OBJ(edge.sourcep(), dfgVarp, "Should have removed undriven sources");
                // Render the rhs expression
                AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(edge.sourcep());
                // Create select LValue
                FileLine* const flp = dfgVarp->driverFileLine(idx);
                AstVarRef* const refp = new AstVarRef{flp, dfgVarp->varp(), VAccess::WRITE};
                AstConst* const lsbp = new AstConst{flp, dfgVarp->driverLsb(idx)};
                AstConst* const widthp = new AstConst{flp, edge.sourcep()->width()};
                AstSel* const lhsp = new AstSel{flp, refp, lsbp, widthp};
                // Add assignment of the value to the selected bits
                addResultEquation(flp, lhsp, rhsp);
            });
        }
    }

    void convertArrayDiver(const DfgVarArray* dfgVarp) {
        // Variable is driven partially. Assign from parts of the canonical var.
        dfgVarp->forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {
            UASSERT_OBJ(edge.sourcep(), dfgVarp, "Should have removed undriven sources");
            // Render the rhs expression
            AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(edge.sourcep());
            // Create select LValue
            FileLine* const flp = dfgVarp->driverFileLine(idx);
            AstVarRef* const refp = new AstVarRef{flp, dfgVarp->varp(), VAccess::WRITE};
            AstConst* const idxp = new AstConst{flp, dfgVarp->driverIndex(idx)};
            AstArraySel* const lhsp = new AstArraySel{flp, refp, idxp};
            // Add assignment of the value to the selected bits
            addResultEquation(flp, lhsp, rhsp);
        });
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatal("Unhandled DfgVertex: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgVarPacked* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), vtxp->varp(), VAccess::READ};
    }

    void visit(DfgVarArray* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), vtxp->varp(), VAccess::READ};
    }

    void visit(DfgConst* vtxp) override {  //
        m_resultp = new AstConst{vtxp->fileline(), vtxp->num()};
    }

    void visit(DfgSel* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertDfgVertexToAstNodeExpr(vtxp->fromp());
        AstConst* const lsbp = new AstConst{flp, vtxp->lsb()};
        AstConst* const widthp = new AstConst{flp, vtxp->width()};
        m_resultp = new AstSel{flp, fromp, lsbp, widthp};
    }

    void visit(DfgMux* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertDfgVertexToAstNodeExpr(vtxp->fromp());
        AstNodeExpr* const lsbp = convertDfgVertexToAstNodeExpr(vtxp->lsbp());
        AstConst* const widthp = new AstConst{flp, vtxp->width()};
        m_resultp = new AstSel{flp, fromp, lsbp, widthp};
    }

    // The rest of the 'visit' methods are generated by 'astgen'
#include "V3Dfg__gen_dfg_to_ast.h"

    // Constructor
    explicit DfgToAstVisitor(DfgGraph& dfg, V3DfgOptimizationContext& ctx)
        : m_modp{dfg.modulep()}
        , m_ctx{ctx} {
        // Convert the graph back to combinational assignments

        // The graph must have been regularized, so we only need to render assignments
        for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();

            // If there is no driver (this vertex is an input to the graph), then nothing to do.
            if (!vtxp->isDrivenByDfg()) continue;

            // Render packed variable assignments
            if (const DfgVarPacked* const dfgVarp = vtxp->cast<DfgVarPacked>()) {
                convertVarDriver(dfgVarp);
                continue;
            }

            // Render array variable assignments
            convertArrayDiver(vtxp->as<DfgVarArray>());
        }
    }

public:
    static AstModule* apply(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
        return DfgToAstVisitor{dfg, ctx}.m_modp;
    }
};

AstModule* V3DfgPasses::dfgToAst(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    return DfgToAstVisitor::apply(dfg, ctx);
}
