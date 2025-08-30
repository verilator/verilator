// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
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
template <typename T_Node, typename T_Vertex, typename... Ops>
T_Node* makeNode(const T_Vertex* vtxp, Ops... ops) {
    T_Node* const nodep = new T_Node{vtxp->fileline(), ops...};
    UASSERT_OBJ(nodep->width() == static_cast<int>(vtxp->width()), vtxp,
                "Incorrect width in AstNode created from DfgVertex "
                    << vtxp->typeName() << ": " << nodep->width() << " vs " << vtxp->width());
    return nodep;
}

//======================================================================
// Vertices needing special conversion

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

}  // namespace

template <bool T_Scoped>
class DfgToAstVisitor final : DfgVisitor {
    // NODE STATE

    // AstScope::user2p  // The combinational AstActive under this scope
    const VNUser2InUse m_user2InUse;

    // TYPES
    using VariableType = std::conditional_t<T_Scoped, AstVarScope, AstVar>;
    struct Assignment final {
        FileLine* m_flp;
        AstNodeExpr* m_lhsp;
        AstNodeExpr* m_rhsp;
        Assignment() = delete;
        Assignment(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* m_rhsp)
            : m_flp{flp}
            , m_lhsp{lhsp}
            , m_rhsp{m_rhsp} {}
    };

    // STATE
    AstModule* const m_modp;  // The parent/result module - This is nullptr when T_Scoped
    V3DfgDfgToAstContext& m_ctx;  // The context for stats
    AstNodeExpr* m_resultp = nullptr;  // The result node of the current traversal
    std::vector<Assignment> m_assignments;  // Assignments to currently rendered variable
    std::vector<Assignment> m_defaults;  // Default assignments to currently rendered variable

    // METHODS

    static VariableType* getNode(const DfgVertexVar* vtxp) {
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<VariableType*>(vtxp->varScopep());
        } else {
            return reinterpret_cast<VariableType*>(vtxp->varp());
        }
    }

    static AstActive* getCombActive(AstScope* scopep) {
        if (!scopep->user2p()) {
            // Try to find the existing combinational AstActive
            for (AstNode* nodep = scopep->blocksp(); nodep; nodep = nodep->nextp()) {
                AstActive* const activep = VN_CAST(nodep, Active);
                if (!activep) continue;
                if (activep->hasCombo()) {
                    scopep->user2p(activep);
                    break;
                }
            }
            // If there isn't one, create a new one
            if (!scopep->user2p()) {
                FileLine* const flp = scopep->fileline();
                AstSenTree* const senTreep
                    = new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}};
                AstActive* const activep = new AstActive{flp, "", senTreep};
                activep->senTreeStorep(senTreep);
                scopep->addBlocksp(activep);
                scopep->user2p(activep);
            }
        }
        return VN_AS(scopep->user2p(), Active);
    }

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

    void convertDriver(std::vector<Assignment>& assignments, FileLine* flp, AstNodeExpr* lhsp,
                       DfgVertex* driverp) {
        if (DfgSplicePacked* const sPackedp = driverp->cast<DfgSplicePacked>()) {
            // Render defaults first
            if (DfgVertex* const defaultp = sPackedp->defaultp()) {
                convertDriver(m_defaults, flp, lhsp, defaultp);
            }
            // Render partial assignments of packed value
            sPackedp->forEachSourceEdge([&](const DfgEdge& edge, size_t i) {
                DfgVertex* const srcp = edge.sourcep();
                if (srcp == sPackedp->defaultp()) return;
                // Create Sel
                FileLine* const dflp = sPackedp->driverFileLine(i);
                AstConst* const lsbp = new AstConst{dflp, sPackedp->driverLo(i)};
                const int width = static_cast<int>(srcp->width());
                AstSel* const nLhsp = new AstSel{dflp, lhsp->cloneTreePure(false), lsbp, width};
                // Convert source
                convertDriver(assignments, dflp, nLhsp, srcp);
                // Delete Sel - was cloned
                VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
            });
            return;
        }

        if (DfgSpliceArray* const sArrayp = driverp->cast<DfgSpliceArray>()) {
            UASSERT_OBJ(!sArrayp->defaultp(), flp, "Should not have a default assignment yet");
            // Partial assignment of array variable
            sArrayp->forEachSourceEdge([&](const DfgEdge& edge, size_t i) {
                DfgVertex* const driverp = edge.sourcep();
                UASSERT_OBJ(driverp, sArrayp, "Should have removed undriven sources");
                UASSERT_OBJ(driverp->size() == 1, driverp, "We only handle single elements");
                // Create ArraySel
                FileLine* const dflp = sArrayp->driverFileLine(i);
                AstConst* const idxp = new AstConst{dflp, sArrayp->driverLo(i)};
                AstArraySel* const nLhsp = new AstArraySel{dflp, lhsp->cloneTreePure(false), idxp};
                // Convert source
                if (const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>()) {
                    convertDriver(assignments, dflp, nLhsp, uap->srcp());
                } else {
                    convertDriver(assignments, dflp, nLhsp, driverp);
                }
                // Delete ArraySel - was cloned
                VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
            });
            return;
        }

        if (const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>()) {
            // Single element array being assigned a unit array. Needs an ArraySel.
            AstConst* const idxp = new AstConst{flp, 0};
            AstArraySel* const nLhsp = new AstArraySel{flp, lhsp->cloneTreePure(false), idxp};
            // Convert source
            convertDriver(assignments, flp, nLhsp, uap->srcp());
            // Delete ArraySel - was cloned
            VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
            return;
        }

        // Base case: assign vertex to current lhs
        AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(driverp);
        assignments.emplace_back(flp, lhsp->cloneTreePure(false), rhsp);
        ++m_ctx.m_resultEquations;
        return;
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatalSrc("Unhandled DfgVertex: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgVarPacked* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), getNode(vtxp), VAccess::READ};
    }

    void visit(DfgVarArray* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), getNode(vtxp), VAccess::READ};
    }

    void visit(DfgConst* vtxp) override {  //
        m_resultp = new AstConst{vtxp->fileline(), vtxp->num()};
    }

    void visit(DfgSel* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertDfgVertexToAstNodeExpr(vtxp->fromp());
        AstConst* const lsbp = new AstConst{flp, vtxp->lsb()};
        m_resultp = new AstSel{flp, fromp, lsbp, static_cast<int>(vtxp->width())};
    }

    void visit(DfgMux* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertDfgVertexToAstNodeExpr(vtxp->fromp());
        AstNodeExpr* const lsbp = convertDfgVertexToAstNodeExpr(vtxp->lsbp());
        m_resultp = new AstSel{flp, fromp, lsbp, static_cast<int>(vtxp->width())};
    }

    // The rest of the 'visit' methods are generated by 'astgen'
#include "V3Dfg__gen_dfg_to_ast.h"

    // Constructor
    explicit DfgToAstVisitor(DfgGraph& dfg, V3DfgDfgToAstContext& ctx)
        : m_modp{dfg.modulep()}
        , m_ctx{ctx} {
        // Convert the graph back to combinational assignments

        // The graph must have been regularized, so we only need to render assignments
        for (DfgVertexVar& vtx : dfg.varVertices()) {
            // If there is no driver (this vertex is an input to the graph), then nothing to do.
            if (!vtx.srcp()) continue;

            ++m_ctx.m_outputVariables;

            // Render variable assignments
            FileLine* const flp = vtx.driverFileLine() ? vtx.driverFileLine() : vtx.fileline();
            AstVarRef* const lhsp = new AstVarRef{flp, getNode(&vtx), VAccess::WRITE};
            convertDriver(m_assignments, flp, lhsp, vtx.srcp());
            // convetDriver always clones lhsp
            VL_DO_DANGLING(lhsp->deleteTree(), lhsp);

            if (m_defaults.empty()) {
                // If there are no default assignments, render each driver as an AssignW
                for (const Assignment& a : m_assignments) {
                    AstAssignW* const assignp = new AstAssignW{a.m_flp, a.m_lhsp, a.m_rhsp};
                    a.m_lhsp->foreach([&a](AstNode* nodep) { nodep->fileline(a.m_flp); });
                    if VL_CONSTEXPR_CXX17 (T_Scoped) {
                        // Add it to the scope holding the target variable
                        getCombActive(vtx.varScopep()->scopep())->addStmtsp(assignp);
                    } else {
                        // Add it to the parent module of the DfgGraph
                        m_modp->addStmtsp(assignp);
                    }
                }
            } else {
                ++m_ctx.m_outputVariablesWithDefault;
                // If there are default assignments, render all drivers under an AstAlways
                AstAlways* const alwaysp
                    = new AstAlways{vtx.fileline(), VAlwaysKwd::ALWAYS_COMB, nullptr, nullptr};
                if VL_CONSTEXPR_CXX17 (T_Scoped) {
                    // Add it to the scope holding the target variable
                    getCombActive(vtx.varScopep()->scopep())->addStmtsp(alwaysp);
                } else {
                    // Add it to the parent module of the DfgGraph
                    m_modp->addStmtsp(alwaysp);
                }
                for (const Assignment& a : m_defaults) {
                    AstAssign* const assignp = new AstAssign{a.m_flp, a.m_lhsp, a.m_rhsp};
                    a.m_lhsp->foreach([&a](AstNode* nodep) { nodep->fileline(a.m_flp); });
                    alwaysp->addStmtsp(assignp);
                }
                for (const Assignment& a : m_assignments) {
                    AstAssign* const assignp = new AstAssign{a.m_flp, a.m_lhsp, a.m_rhsp};
                    a.m_lhsp->foreach([&a](AstNode* nodep) { nodep->fileline(a.m_flp); });
                    alwaysp->addStmtsp(assignp);
                }
            }
            m_assignments.clear();
            m_defaults.clear();
        }
    }

public:
    static void apply(DfgGraph& dfg, V3DfgDfgToAstContext& ctx) { DfgToAstVisitor{dfg, ctx}; }
};

void V3DfgPasses::dfgToAst(DfgGraph& dfg, V3DfgContext& ctx) {
    if (dfg.modulep()) {
        DfgToAstVisitor</* T_Scoped: */ false>::apply(dfg, ctx.m_dfg2AstContext);
    } else {
        DfgToAstVisitor</* T_Scoped: */ true>::apply(dfg, ctx.m_dfg2AstContext);
    }
}
