// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert DfgGraph to AstModule
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
//
// Convert DfgGraph back to AstModule. We recursively construct AstNodeMath expressions for each
// DfgVertex which represents a storage location (e.g.: DfgVar), or has multiple sinks without
// driving a storage location (and hence needs a temporary variable to duplication). The recursion
// stops when we reach a DfgVertex representing a storage location (e.g.: DfgVar), or a vertex that
// that has multiple sinks (as these nodes will have a [potentially new temporary] corresponding
// storage location). Redundant variables (those whose source vertex drives multiple variables) are
// eliminated when possible. Vertices driving multiple variables are rendered once, driving an
// arbitrarily (but deterministically) chosen canonical variable, and the corresponding redundant
// variables are assigned from the canonical variable.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create an AstNodeMath out of a DfgVertex. For most AstNodeMath subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename Node, typename... Ops>
Node* makeNode(const DfgForAst<Node>* vtxp, Ops... ops) {
    Node* const nodep = new Node{vtxp->fileline(), ops...};
    UASSERT_OBJ(nodep->width() == static_cast<int>(vtxp->width()), vtxp,
                "Incorrect width in AstNode created from DfgVertex "
                    << vtxp->typeName() << ": " << nodep->width() << " vs " << vtxp->width());
    return nodep;
}

//======================================================================
// Vertices needing special conversion

template <>
AstExtend* makeNode<AstExtend, AstNodeMath*>(  //
    const DfgExtend* vtxp, AstNodeMath* op1) {
    return new AstExtend{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstExtendS* makeNode<AstExtendS, AstNodeMath*>(  //
    const DfgExtendS* vtxp, AstNodeMath* op1) {
    return new AstExtendS{vtxp->fileline(), op1, static_cast<int>(vtxp->width())};
}

template <>
AstShiftL* makeNode<AstShiftL, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftL* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftL{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftR* makeNode<AstShiftR, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftR* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftR{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

template <>
AstShiftRS* makeNode<AstShiftRS, AstNodeMath*, AstNodeMath*>(  //
    const DfgShiftRS* vtxp, AstNodeMath* op1, AstNodeMath* op2) {
    return new AstShiftRS{vtxp->fileline(), op1, op2, static_cast<int>(vtxp->width())};
}

//======================================================================
// Currently unhandled nodes - see corresponding AstToDfg functions
// LCOV_EXCL_START
template <>
AstCCast* makeNode<AstCCast, AstNodeMath*>(const DfgCCast* vtxp, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}
template <>
AstAtoN* makeNode<AstAtoN, AstNodeMath*>(const DfgAtoN* vtxp, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}
template <>
AstCompareNN* makeNode<AstCompareNN, AstNodeMath*, AstNodeMath*>(const DfgCompareNN* vtxp,
                                                                 AstNodeMath*, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}
template <>
AstSliceSel* makeNode<AstSliceSel, AstNodeMath*, AstNodeMath*, AstNodeMath*>(
    const DfgSliceSel* vtxp, AstNodeMath*, AstNodeMath*, AstNodeMath*) {
    vtxp->v3fatal("not implemented");
}
// LCOV_EXCL_STOP

}  // namespace

class DfgToAstVisitor final : DfgVisitor {
    // STATE

    AstModule* const m_modp;  // The parent/result module
    V3DfgOptimizationContext& m_ctx;  // The optimization context for stats
    AstNodeMath* m_resultp = nullptr;  // The result node of the current traversal
    // Map from DfgVertex to the AstVar holding the value of that DfgVertex after conversion
    std::unordered_map<const DfgVertex*, AstVar*> m_resultVars;
    // Map from an AstVar, to the canonical AstVar that can be substituted for that AstVar
    std::unordered_map<AstVar*, AstVar*> m_canonVars;
    V3UniqueNames m_tmpNames{"_VdfgTmp"};  // For generating temporary names
    DfgVertex::HashCache m_hashCache;  // For caching hashes

    // METHODS

    // Given a DfgVar, return the canonical AstVar that can be used for this DfgVar.
    // Also builds the m_canonVars map as a side effect.
    AstVar* getCanonicalVar(const DfgVar* vtxp) {
        // Variable only read by DFG
        if (!vtxp->driverp()) return vtxp->varp();

        // Look up map
        const auto it = m_canonVars.find(vtxp->varp());
        if (it != m_canonVars.end()) return it->second;

        // Not known yet, compute it (for all vars from the same driver)
        std::vector<const DfgVar*> varps;
        vtxp->driverp()->forEachSink([&](const DfgVertex& vtx) {
            if (const DfgVar* const varVtxp = vtx.cast<DfgVar>()) varps.push_back(varVtxp);
        });
        UASSERT_OBJ(!varps.empty(), vtxp, "The input vtxp->varp() is always available");
        std::stable_sort(varps.begin(), varps.end(), [](const DfgVar* ap, const DfgVar* bp) {
            if (ap->hasExtRefs() != bp->hasExtRefs()) return ap->hasExtRefs();
            const FileLine& aFl = *(ap->fileline());
            const FileLine& bFl = *(bp->fileline());
            if (const int cmp = aFl.operatorCompare(bFl)) return cmp < 0;
            return ap->varp()->name() < bp->varp()->name();
        });
        AstVar* const canonVarp = varps.front()->varp();

        // Add results to map
        for (const DfgVar* const varp : varps) m_canonVars.emplace(varp->varp(), canonVarp);

        // Return it
        return canonVarp;
    }

    // Given a DfgVertex, return an AstVar that will hold the value of the given DfgVertex once we
    // are done with converting this Dfg into Ast form.
    AstVar* getResultVar(const DfgVertex* vtxp) {
        const auto pair = m_resultVars.emplace(vtxp, nullptr);
        AstVar*& varp = pair.first->second;
        if (pair.second) {
            // If this vertex is a DfgVar, then we know the variable. If this node is not a DfgVar,
            // then first we try to find a DfgVar driven by this node, and use that, otherwise we
            // create a temporary
            if (const DfgVar* const thisDfgVarp = vtxp->cast<DfgVar>()) {
                // This is a DfgVar
                varp = getCanonicalVar(thisDfgVarp);
            } else if (const DfgVar* const sinkDfgVarp = vtxp->findSink<DfgVar>()) {
                // We found a DfgVar driven by this node
                varp = getCanonicalVar(sinkDfgVarp);
            } else {
                // No DfgVar driven by this node. Create a temporary.
                const string name = m_tmpNames.get(vtxp->hash(m_hashCache).toString());
                // Note: It is ok for these temporary variables to be always unsigned. They are
                // read only by other expressions within the graph and all expressions interpret
                // their operands based on the expression type, not the operand type.
                AstNodeDType* const dtypep = v3Global.rootp()->findBitDType(
                    vtxp->width(), vtxp->width(), VSigning::UNSIGNED);
                varp = new AstVar{vtxp->fileline(), VVarType::MODULETEMP, name, dtypep};
                // Add temporary AstVar to containing module
                m_modp->addStmtsp(varp);
            }
            // Add to map
        }
        return varp;
    }

    AstNodeMath* convertDfgVertexToAstNodeMath(DfgVertex* vtxp) {
        UASSERT_OBJ(!m_resultp, vtxp, "Result already computed");
        iterate(vtxp);
        UASSERT_OBJ(m_resultp, vtxp, "Missing result");
        AstNodeMath* const resultp = m_resultp;
        m_resultp = nullptr;
        return resultp;
    }

    AstNodeMath* convertSource(DfgVertex* vtxp) {
        if (vtxp->hasMultipleSinks()) {
            // Vertices with multiple sinks need a temporary variable, just return a reference
            return new AstVarRef{vtxp->fileline(), getResultVar(vtxp), VAccess::READ};
        } else {
            // Vertex with single sink is simply recursively converted
            UASSERT_OBJ(vtxp->hasSinks(), vtxp, "Must have one sink: " << vtxp->typeName());
            return convertDfgVertexToAstNodeMath(vtxp);
        }
    }

    // VISITORS
    void visit(DfgVertex* vtxp) override {  // LCOV_EXCL_START
        vtxp->v3fatal("Unhandled DfgVertex: " << vtxp->typeName());
    }  // LCOV_EXCL_STOP

    void visit(DfgVar* vtxp) override {
        m_resultp = new AstVarRef{vtxp->fileline(), getCanonicalVar(vtxp), VAccess::READ};
    }

    void visit(DfgConst* vtxp) override {  //
        m_resultp = vtxp->constp()->cloneTree(false);
    }

    // The rest of the 'visit' methods are generated by 'astgen'
#include "V3Dfg__gen_dfg_to_ast.h"

    // Constructor
    explicit DfgToAstVisitor(DfgGraph& dfg, V3DfgOptimizationContext& ctx)
        : m_modp{dfg.modulep()}
        , m_ctx{ctx} {
        // We can eliminate some variables completely
        std::vector<AstVar*> redundantVarps;

        // Render the logic
        dfg.forEachVertex([&](DfgVertex& vtx) {
            // Compute the AstNodeMath expression representing this DfgVertex
            AstNodeMath* rhsp = nullptr;
            AstNodeMath* lhsp = nullptr;
            FileLine* assignmentFlp = nullptr;
            if (const DfgVar* const dfgVarp = vtx.cast<DfgVar>()) {
                // DfgVar instances (these might be driving the given AstVar variable)
                // If there is no driver (i.e.: this DfgVar is an input to the Dfg), then nothing
                // to do
                if (!dfgVarp->driverp()) return;
                // The driver of this DfgVar might drive multiple variables. Only emit one
                // assignment from the driver to an arbitrarily chosen canonical variable, and
                // assign the other variables from that canonical variable
                AstVar* const canonVarp = getCanonicalVar(dfgVarp);
                if (canonVarp == dfgVarp->varp()) {
                    // This is the canonical variable, so render the driver
                    rhsp = convertDfgVertexToAstNodeMath(dfgVarp->driverp());
                } else if (dfgVarp->keep()) {
                    // Not the canonical variable but it must be kept, just assign from the
                    // canonical variable.
                    rhsp = new AstVarRef{canonVarp->fileline(), canonVarp, VAccess::READ};
                } else {
                    // Not a canonical var, and it can be removed. We will replace all references
                    // to it with the canonical variable, and hence this can be removed.
                    redundantVarps.push_back(dfgVarp->varp());
                    ++m_ctx.m_replacedVars;
                    return;
                }
                // The Lhs is the variable driven by this DfgVar
                lhsp = new AstVarRef{vtx.fileline(), dfgVarp->varp(), VAccess::WRITE};
                // Set location to the location of the original assignment to this variable
                assignmentFlp = dfgVarp->assignmentFileline();
            } else if (vtx.hasMultipleSinks() && !vtx.findSink<DfgVar>()) {
                // DfgVertex that has multiple sinks, but does not drive a DfgVar (needs temporary)
                // Just render the logic
                rhsp = convertDfgVertexToAstNodeMath(&vtx);
                // The lhs is a temporary
                lhsp = new AstVarRef{vtx.fileline(), getResultVar(&vtx), VAccess::WRITE};
                // Render vertex
                assignmentFlp = vtx.fileline();
                // Stats
                ++m_ctx.m_intermediateVars;
            } else {
                // Every other DfgVertex will be inlined by 'convertDfgVertexToAstNodeMath' as an
                // AstNodeMath at use, and hence need not be converted.
                return;
            }
            // Add assignment of the value to the variable
            m_modp->addStmtsp(new AstAssignW{assignmentFlp, lhsp, rhsp});
            ++m_ctx.m_resultEquations;
        });

        // Remap all references to point to the canonical variables, if one exists
        VNDeleter deleter;
        m_modp->foreach<AstVarRef>([&](AstVarRef* refp) {
            // Any variable that is written outside the DFG will have itself as the canonical
            // var, so need not be replaced, furthermore, if a variable is traced, we don't
            // want to update the write ref we just created above, so we only replace read only
            // references.
            if (!refp->access().isReadOnly()) return;
            const auto it = m_canonVars.find(refp->varp());
            if (it == m_canonVars.end()) return;
            if (it->second == refp->varp()) return;
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
