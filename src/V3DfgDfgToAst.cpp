// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
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
    using Variable = std::conditional_t<T_Scoped, AstVarScope, AstVar>;
    using Container = std::conditional_t<T_Scoped, AstActive, AstNodeModule>;

    // STATE
    AstModule* const m_modp;  // The parent/result module - This is nullptr when T_Scoped
    V3DfgDfgToAstContext& m_ctx;  // The context for stats
    AstNodeExpr* m_resultp = nullptr;  // The result node of the current traversal
    AstAlways* m_alwaysp = nullptr;  // Process to add assignments to, if have a default driver
    Container* m_containerp = nullptr;  // The AstNodeModule or AstActive to insert assigns into

    // METHODS

    static Variable* getNode(const DfgVertexVar* vtxp) {
        if VL_CONSTEXPR_CXX17 (T_Scoped) {
            return reinterpret_cast<Variable*>(vtxp->varScopep());
        } else {
            return reinterpret_cast<Variable*>(vtxp->varp());
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
        UASSERT_OBJ(vtxp->is<DfgVertexVar>() || vtxp->is<DfgConst>()  //
                        || !vtxp->hasMultipleSinks() || vtxp->isCheaperThanLoad(),  //
                    vtxp, "Intermediate DFG value with multiple uses");
        iterate(vtxp);
        UASSERT_OBJ(m_resultp, vtxp, "Missing result");
        AstNodeExpr* const resultp = m_resultp;
        m_resultp = nullptr;
        return resultp;
    }

    void createAssignment(FileLine* flp, AstNodeExpr* lhsp, DfgVertex* driverp) {
        // Keep track of statisticss
        ++m_ctx.m_resultEquations;
        // Render the driver
        AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(driverp);
        // Update LHS locations to reflect the location of the original driver
        lhsp->foreach([&](AstNode* nodep) { nodep->fileline(flp); });

        // If using a process, add Assign there
        if (m_alwaysp) {
            m_alwaysp->addStmtsp(new AstAssign{flp, lhsp, rhsp});
            return;
        }

        // Otherwise create an AssignW
        AstAssignW* const ap = new AstAssignW{flp, lhsp, rhsp};
        m_containerp->addStmtsp(new AstAlways{ap});
    }

    void convertDriver(FileLine* flp, AstNodeExpr* lhsp, DfgVertex* driverp) {
        if (DfgSplicePacked* const sPackedp = driverp->cast<DfgSplicePacked>()) {
            // Partial assignment of packed value
            sPackedp->foreachDriver([&](DfgVertex& src, uint32_t lo, FileLine* dflp) {
                // Create Sel
                AstConst* const lsbp = new AstConst{dflp, lo};
                const int width = static_cast<int>(src.width());
                AstSel* const nLhsp = new AstSel{dflp, lhsp->cloneTreePure(false), lsbp, width};
                // Convert source
                convertDriver(dflp, nLhsp, &src);
                // Delete Sel - was cloned
                VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
                return false;
            });
            return;
        }

        if (DfgSpliceArray* const sArrayp = driverp->cast<DfgSpliceArray>()) {
            // Partial assignment of array variable
            sArrayp->foreachDriver([&](DfgVertex& src, uint32_t lo, FileLine* dflp) {
                UASSERT_OBJ(src.size() == 1, &src, "We only handle single elements");
                // Create ArraySel
                AstConst* const idxp = new AstConst{dflp, lo};
                AstArraySel* const nLhsp = new AstArraySel{dflp, lhsp->cloneTreePure(false), idxp};
                // Convert source
                if (const DfgUnitArray* const uap = src.cast<DfgUnitArray>()) {
                    convertDriver(dflp, nLhsp, uap->srcp());
                } else {
                    convertDriver(dflp, nLhsp, &src);
                }
                // Delete ArraySel - was cloned
                VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
                return false;
            });
            return;
        }

        if (const DfgUnitArray* const uap = driverp->cast<DfgUnitArray>()) {
            // Single element array being assigned a unit array. Needs an ArraySel.
            AstConst* const idxp = new AstConst{flp, 0};
            AstArraySel* const nLhsp = new AstArraySel{flp, lhsp->cloneTreePure(false), idxp};
            // Convert source
            convertDriver(flp, nLhsp, uap->srcp());
            // Delete ArraySel - was cloned
            VL_DO_DANGLING(nLhsp->deleteTree(), nLhsp);
            return;
        }

        // Base case: assign vertex to current lhs
        createAssignment(flp, lhsp->cloneTreePure(false), driverp);
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
    DfgToAstVisitor(DfgGraph& dfg, V3DfgDfgToAstContext& ctx)
        : m_modp{dfg.modulep()}
        , m_ctx{ctx} {
        if (v3Global.opt.debugCheck()) V3DfgPasses::typeCheck(dfg);

        // Convert the graph back to combinational assignments
        // The graph must have been regularized, so we only need to render assignments
        for (DfgVertexVar& vtx : dfg.varVertices()) {
            // If there is no driver (this vertex is an input to the graph), then nothing to do.
            if (!vtx.srcp()) {
                UASSERT_OBJ(!vtx.defaultp(), &vtx, "Only default driver on variable");
                continue;
            }

            ++m_ctx.m_outputVariables;

            // Render variable assignments
            FileLine* const flp = vtx.driverFileLine() ? vtx.driverFileLine() : vtx.fileline();
            AstVarRef* const lhsp = new AstVarRef{flp, getNode(&vtx), VAccess::WRITE};

            VL_RESTORER(m_containerp);
            if VL_CONSTEXPR_CXX17 (T_Scoped) {
                // Add it to the scope holding the target variable
                AstActive* const activep = getCombActive(vtx.varScopep()->scopep());
                m_containerp = reinterpret_cast<Container*>(activep);
            } else {
                // Add it to the parent module of the DfgGraph
                m_containerp = reinterpret_cast<Container*>(m_modp);
            }

            // If there is a default value, render all drivers under an AstAlways
            VL_RESTORER(m_alwaysp);
            if (DfgVertex* const defaultp = vtx.defaultp()) {
                ++m_ctx.m_outputVariablesWithDefault;
                m_alwaysp = new AstAlways{vtx.fileline(), VAlwaysKwd::ALWAYS_COMB, nullptr};
                m_containerp->addStmtsp(m_alwaysp);
                // The default assignment needs to go first
                createAssignment(vtx.fileline(), lhsp->cloneTreePure(false), defaultp);
            }

            // Render the drivers
            convertDriver(flp, lhsp, vtx.srcp());

            // convetDriver always clones lhsp
            VL_DO_DANGLING(lhsp->deleteTree(), lhsp);
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
