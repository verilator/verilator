// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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
    // NODE STATE
    // AstVar::user1()  bool: this is a temporary we are introducing

    const VNUser1InUse m_inuser1;

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

    // Given a DfgVarPacked, return the canonical AstVar that can be used for this DfgVarPacked.
    // Also builds the m_canonVars map as a side effect.
    AstVar* getCanonicalVar(const DfgVarPacked* vtxp) {
        // If variable driven (at least partially) outside the DFG, then we have no choice
        if (!vtxp->isDrivenFullyByDfg()) return vtxp->varp();

        // Look up map
        const auto it = m_canonVars.find(vtxp->varp());
        if (it != m_canonVars.end()) return it->second;

        // Not known yet, compute it (for all vars driven fully from the same driver)
        std::vector<const DfgVarPacked*> varps;
        vtxp->source(0)->forEachSink([&](const DfgVertex& vtx) {
            if (const DfgVarPacked* const varVtxp = vtx.cast<DfgVarPacked>()) {
                if (varVtxp->isDrivenFullyByDfg()) varps.push_back(varVtxp);
            }
        });
        UASSERT_OBJ(!varps.empty(), vtxp, "The input vtxp is always available");
        std::stable_sort(varps.begin(), varps.end(),
                         [](const DfgVarPacked* ap, const DfgVarPacked* bp) {
                             if (ap->hasExtRefs() != bp->hasExtRefs()) return ap->hasExtRefs();
                             const FileLine& aFl = *(ap->fileline());
                             const FileLine& bFl = *(bp->fileline());
                             if (const int cmp = aFl.operatorCompare(bFl)) return cmp < 0;
                             return ap->varp()->name() < bp->varp()->name();
                         });
        AstVar* const canonVarp = varps.front()->varp();

        // Add results to map
        for (const DfgVarPacked* const varp : varps) m_canonVars.emplace(varp->varp(), canonVarp);

        // Return it
        return canonVarp;
    }

    // Given a DfgVertex, return an AstVar that will hold the value of the given DfgVertex once we
    // are done with converting this Dfg into Ast form.
    AstVar* getResultVar(DfgVertex* vtxp) {
        const auto pair = m_resultVars.emplace(vtxp, nullptr);
        AstVar*& varp = pair.first->second;
        if (pair.second) {
            // If this vertex is a DfgVarPacked, then we know the variable. If this node is not a
            // DfgVarPacked, then first we try to find a DfgVarPacked driven by this node, and use
            // that, otherwise we create a temporary
            if (const DfgVarPacked* const thisDfgVarPackedp = vtxp->cast<DfgVarPacked>()) {
                // This is a DfgVarPacked
                varp = getCanonicalVar(thisDfgVarPackedp);
            } else if (const DfgVarArray* const thisDfgVarArrayp = vtxp->cast<DfgVarArray>()) {
                // This is a DfgVarArray
                varp = thisDfgVarArrayp->varp();
            } else if (const DfgVarPacked* const sinkDfgVarPackedp = vtxp->findSink<DfgVarPacked>(
                           [](const DfgVarPacked& var) { return var.isDrivenFullyByDfg(); })) {
                // We found a DfgVarPacked driven fully by this node
                varp = getCanonicalVar(sinkDfgVarPackedp);
            } else {
                // No DfgVarPacked driven fully by this node. Create a temporary.
                // TODO: should we reuse parts when the AstVar is used as an rvalue?
                const string name = m_tmpNames.get(vtxp->hash().toString());
                // Note: It is ok for these temporary variables to be always unsigned. They are
                // read only by other expressions within the graph and all expressions interpret
                // their operands based on the expression type, not the operand type.
                AstNodeDType* const dtypep = v3Global.rootp()->findBitDType(
                    vtxp->width(), vtxp->width(), VSigning::UNSIGNED);
                varp = new AstVar{vtxp->fileline(), VVarType::MODULETEMP, name, dtypep};
                varp->user1(true);  // Mark as temporary
                // Add temporary AstVar to containing module
                m_modp->addStmtsp(varp);
            }
            // Add to map
        }
        return varp;
    }

    AstNodeExpr* convertDfgVertexToAstNodeExpr(DfgVertex* vtxp) {
        UASSERT_OBJ(!m_resultp, vtxp, "Result already computed");
        iterate(vtxp);
        UASSERT_OBJ(m_resultp, vtxp, "Missing result");
        AstNodeExpr* const resultp = m_resultp;
        m_resultp = nullptr;
        return resultp;
    }

    AstNodeExpr* convertSource(DfgVertex* vtxp) {
        if (vtxp->inlined()) {
            // Inlined vertices are simply recursively converted
            UASSERT_OBJ(vtxp->hasSinks(), vtxp, "Must have one sink: " << vtxp->typeName());
            return convertDfgVertexToAstNodeExpr(vtxp);
        } else {
            // Vertices that are not inlined need a variable, just return a reference
            return new AstVarRef{vtxp->fileline(), getResultVar(vtxp), VAccess::READ};
        }
    }

    void convertCanonicalVarDriver(const DfgVarPacked* dfgVarp) {
        const auto wRef = [dfgVarp]() {
            return new AstVarRef{dfgVarp->fileline(), dfgVarp->varp(), VAccess::WRITE};
        };
        if (dfgVarp->isDrivenFullyByDfg()) {
            // Whole variable is driven. Render driver and assign directly to whole variable.
            AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(dfgVarp->source(0));
            addResultEquation(dfgVarp->driverFileLine(0), wRef(), rhsp);
        } else {
            // Variable is driven partially. Render each driver as a separate assignment.
            dfgVarp->forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {
                UASSERT_OBJ(edge.sourcep(), dfgVarp, "Should have removed undriven sources");
                // Render the rhs expression
                AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(edge.sourcep());
                // Create select LValue
                FileLine* const flp = dfgVarp->driverFileLine(idx);
                AstConst* const lsbp = new AstConst{flp, dfgVarp->driverLsb(idx)};
                AstConst* const widthp = new AstConst{flp, edge.sourcep()->width()};
                AstSel* const lhsp = new AstSel{flp, wRef(), lsbp, widthp};
                // Add assignment of the value to the selected bits
                addResultEquation(flp, lhsp, rhsp);
            });
        }
    }

    void convertDuplicateVarDriver(const DfgVarPacked* dfgVarp, AstVar* canonVarp) {
        const auto rRef = [canonVarp]() {
            return new AstVarRef{canonVarp->fileline(), canonVarp, VAccess::READ};
        };
        const auto wRef = [dfgVarp]() {
            return new AstVarRef{dfgVarp->fileline(), dfgVarp->varp(), VAccess::WRITE};
        };
        if (dfgVarp->isDrivenFullyByDfg()) {
            // Whole variable is driven. Just assign from the canonical variable.
            addResultEquation(dfgVarp->driverFileLine(0), wRef(), rRef());
        } else {
            // Variable is driven partially. Assign from parts of the canonical var.
            dfgVarp->forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {
                UASSERT_OBJ(edge.sourcep(), dfgVarp, "Should have removed undriven sources");
                // Create select LValue
                FileLine* const flp = dfgVarp->driverFileLine(idx);
                AstConst* const lsbp = new AstConst{flp, dfgVarp->driverLsb(idx)};
                AstConst* const widthp = new AstConst{flp, edge.sourcep()->width()};
                AstSel* const rhsp = new AstSel{flp, rRef(), lsbp, widthp->cloneTreePure(false)};
                AstSel* const lhsp = new AstSel{flp, wRef(), lsbp->cloneTreePure(false), widthp};
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

    void addResultEquation(FileLine* flp, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        m_modp->addStmtsp(new AstAssignW{flp, lhsp, rhsp});
        ++m_ctx.m_resultEquations;
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatal("Unhandled DfgVertex: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgVarPacked* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), getCanonicalVar(vtxp), VAccess::READ};
    }

    void visit(DfgVarArray* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), vtxp->varp(), VAccess::READ};
    }

    void visit(DfgConst* vtxp) override {  //
        m_resultp = new AstConst{vtxp->fileline(), vtxp->num()};
    }

    void visit(DfgSel* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertSource(vtxp->fromp());
        AstConst* const lsbp = new AstConst{flp, vtxp->lsb()};
        AstConst* const widthp = new AstConst{flp, vtxp->width()};
        m_resultp = new AstSel{flp, fromp, lsbp, widthp};
    }

    void visit(DfgMux* vtxp) override {
        FileLine* const flp = vtxp->fileline();
        AstNodeExpr* const fromp = convertSource(vtxp->fromp());
        AstNodeExpr* const lsbp = convertSource(vtxp->lsbp());
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

        // Used by DfgVertex::hash
        const auto userDataInUse = dfg.userDataInUse();

        // We can eliminate some variables completely
        std::vector<AstVar*> redundantVarps;

        // First render variable assignments
        for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();

            // If there is no driver (this vertex is an input to the graph), then nothing to do.
            if (!vtxp->isDrivenByDfg()) continue;

            // Render packed variable assignments
            if (const DfgVarPacked* const dfgVarp = vtxp->cast<DfgVarPacked>()) {
                // The driver of this DfgVarPacked might drive multiple variables. Only emit one
                // assignment from the driver to an arbitrarily chosen canonical variable, and
                // assign the other variables from that canonical variable
                AstVar* const canonVarp = getCanonicalVar(dfgVarp);
                if (canonVarp == dfgVarp->varp()) {
                    // This is the canonical variable, so render the driver
                    convertCanonicalVarDriver(dfgVarp);
                } else if (dfgVarp->keep()) {
                    // Not the canonical variable but it must be kept
                    convertDuplicateVarDriver(dfgVarp, canonVarp);
                } else {
                    // Not a canonical var, and it can be removed. We will replace all references
                    // to it with the canonical variable, and hence this can be removed.
                    redundantVarps.push_back(dfgVarp->varp());
                    ++m_ctx.m_replacedVars;
                }
                // Done
                continue;
            }

            // Render array variable assignments
            if (const DfgVarArray* dfgVarp = vtxp->cast<DfgVarArray>()) {
                // We don't canonicalize arrays, so just render the drivers
                convertArrayDiver(dfgVarp);
                // Done
                continue;
            }
        }

        // Constants are always inlined, so we only need to iterate proper operations
        for (DfgVertex *vtxp = dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();

            // If the vertex is known to be inlined, then there is nothing to do
            if (vtxp->inlined()) continue;

            // Check if this uses a temporary, vs one of the vars rendered above
            AstVar* const resultVarp = getResultVar(vtxp);
            if (resultVarp->user1()) {
                // We introduced a temporary for this DfgVertex
                ++m_ctx.m_intermediateVars;
                FileLine* const flp = vtxp->fileline();
                // Just render the logic
                AstNodeExpr* const rhsp = convertDfgVertexToAstNodeExpr(vtxp);
                // The lhs is the temporary
                AstNodeExpr* const lhsp = new AstVarRef{flp, resultVarp, VAccess::WRITE};
                // Add assignment of the value to the variable
                addResultEquation(flp, lhsp, rhsp);
            }
        }

        // Remap all references to point to the canonical variables, if one exists
        VNDeleter deleter;
        m_modp->foreach([&](AstVarRef* refp) {
            // Any variable that is written partially outside the DFG will have itself as the
            // canonical var, so need not be replaced, furthermore, if a variable is traced, we
            // don't want to update the write-refs we just created above, so we only replace
            // read-only references to those variables to those variables we know are not written
            // in non-DFG logic.
            if (!refp->access().isReadOnly() || refp->varp()->user3()) return;
            const auto it = m_canonVars.find(refp->varp());
            if (it == m_canonVars.end() || it->second == refp->varp()) return;
            refp->replaceWith(new AstVarRef{refp->fileline(), it->second, refp->access()});
            deleter.pushDeletep(refp);
        });

        // Remove redundant variables
        for (AstVar* const varp : redundantVarps) varp->unlinkFrBack()->deleteTree();
    }

public:
    static AstModule* apply(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
        return DfgToAstVisitor{dfg, ctx}.m_modp;
    }
};

AstModule* V3DfgPasses::dfgToAst(DfgGraph& dfg, V3DfgOptimizationContext& ctx) {
    return DfgToAstVisitor::apply(dfg, ctx);
}
