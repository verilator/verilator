// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert AstModule to DfgGraph
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
// Convert and AstModule to a DfgGraph. We proceed by visiting convertable logic blocks (e.g.:
// AstAssignW of appropriate type and with no delays), recursively constructing DfgVertex instances
// for the expressions that compose the subject logic block. If all expressions in the current
// logic block can be converted, then we delete the logic block (now represented in the DfgGraph),
// and connect the corresponding DfgVertex instances appropriately. If some of the expressions were
// not convertible in the current logic block, we revert (delete) the DfgVertex instances created
// for the logic block, and leave the logic block in the AstModule. Any variable reference from
// non-converted logic blocks (or other constructs under the AstModule) are marked as being
// referenced in the AstModule, which is relevant for later optimization.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"
#include "V3Global.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

// Create a DfgVertex out of a AstNodeMath. For most AstNodeMath subtypes, this can be done
// automatically. For the few special cases, we provide specializations below
template <typename Vertex>
Vertex* makeVertex(const AstForDfg<Vertex>* nodep, DfgGraph& dfg) {
    return new Vertex{dfg, nodep->fileline(), DfgVertex::dtypeFor(nodep)};
}

//======================================================================
// Currently unhandled nodes
// LCOV_EXCL_START
// AstCCast changes width, but should not exists where DFG optimization is currently invoked
template <>
DfgCCast* makeVertex<DfgCCast>(const AstCCast*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgAtoN* makeVertex<DfgAtoN>(const AstAtoN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgCompareNN* makeVertex<DfgCompareNN>(const AstCompareNN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on unpacked arrays which we don't optimize anyway
template <>
DfgSliceSel* makeVertex<DfgSliceSel>(const AstSliceSel*, DfgGraph&) {
    return nullptr;
}
// LCOV_EXCL_STOP

}  // namespace

class AstToDfgVisitor final : public VNVisitor {
    // NODE STATE

    // AstNode::user1p   // DfgVertex for this AstNode
    const VNUser1InUse m_user1InUse;

    // STATE

    DfgGraph* const m_dfgp;  // The graph being built
    V3DfgOptimizationContext& m_ctx;  // The optimization context for stats
    bool m_foundUnhandled = false;  // Found node not implemented as DFG or not implemented 'visit'
    std::vector<DfgVertex*> m_uncommittedVertices;  // Vertices that we might decide to revert

    // METHODS
    void markReferenced(AstNode* nodep) {
        nodep->foreach<AstVarRef>([this](const AstVarRef* refp) {
            // No need to (and in fact cannot) mark variables with unsupported dtypes
            if (!DfgVertex::isSupportedDType(refp->varp()->dtypep())) return;
            getNet(refp->varp())->setHasModRefs();
        });
    }

    void commitVertices() { m_uncommittedVertices.clear(); }

    void revertUncommittedVertices() {
        for (DfgVertex* const vtxp : m_uncommittedVertices) vtxp->unlinkDelete(*m_dfgp);
        m_uncommittedVertices.clear();
    }

    DfgVar* getNet(AstVar* varp) {
        if (!varp->user1p()) {
            // Note DfgVar vertices are not added to m_uncommittedVertices, because we want to
            // hold onto them via AstVar::user1p, and the AstVar which might be referenced via
            // multiple AstVarRef instances, so we will never revert a DfgVar once created. This
            // means we can end up with DfgVar vertices in the graph which have no connections at
            // all (which is fine for later processing).
            varp->user1p(new DfgVar{*m_dfgp, varp});
        }
        return varp->user1u().to<DfgVar*>();
    }

    DfgVertex* getVertex(AstNode* nodep) {
        DfgVertex* vtxp = nodep->user1u().to<DfgVertex*>();
        UASSERT_OBJ(vtxp, nodep, "Missing Dfg vertex");
        return vtxp;
    }

    // Returns true if the expression cannot (or should not) be represented by DFG
    bool unhandled(AstNodeMath* nodep) {
        // Short-circuiting if something was already unhandled
        if (!m_foundUnhandled) {
            // Impure nodes cannot be represented
            if (!nodep->isPure()) {
                m_foundUnhandled = true;
                ++m_ctx.m_nonRepImpure;
            }
            // Check node has supported dtype
            if (!DfgVertex::isSupportedDType(nodep->dtypep())) {
                m_foundUnhandled = true;
                ++m_ctx.m_nonRepDType;
            }
        }
        return m_foundUnhandled;
    }

    // VISITORS
    void visit(AstNode* nodep) override {
        // Conservatively treat this node as unhandled
        m_foundUnhandled = true;
        ++m_ctx.m_nonRepUnknown;
        markReferenced(nodep);
    }
    void visit(AstCell* nodep) override { markReferenced(nodep); }
    void visit(AstNodeProcedure* nodep) override { markReferenced(nodep); }
    void visit(AstVar* nodep) override {
        // No need to (and in fact cannot) handle variables with unsupported dtypes
        if (!DfgVertex::isSupportedDType(nodep->dtypep())) return;
        // Mark ports as having external references
        if (nodep->isIO()) getNet(nodep)->setHasExtRefs();
        // Mark variables that are the target of a hierarchical reference
        // (these flags were set up in DataflowPrepVisitor)
        if (nodep->user2()) getNet(nodep)->setHasExtRefs();
    }

    void visit(AstAssignW* nodep) override {
        // Cannot handle assignment with timing control yet
        if (nodep->timingControlp()) {
            markReferenced(nodep);
            ++m_ctx.m_nonRepTiming;
            return;
        }

        // Cannot handle mismatched widths. Mismatched assignments should have been fixed up in
        // earlier passes anyway, so this should never be hit, but being paranoid just in case.
        if (nodep->lhsp()->width() != nodep->rhsp()->width()) {  // LCOV_EXCL_START
            markReferenced(nodep);
            ++m_ctx.m_nonRepWidth;
            return;
        }  // LCOV_EXCL_START

        // Simple assignment with whole variable on left-hand side
        if (AstVarRef* const vrefp = VN_CAST(nodep->lhsp(), VarRef)) {
            UASSERT_OBJ(m_uncommittedVertices.empty(), nodep, "Should not nest");

            // Build DFG vertices representing the two sides
            {
                m_foundUnhandled = false;
                iterate(vrefp);
                iterate(nodep->rhsp());
                // If this assignment contains an AstNode not representable by a DfgVertex,
                // then revert the graph.
                if (m_foundUnhandled) {
                    revertUncommittedVertices();
                    markReferenced(nodep);
                    return;
                }
            }

            // Connect the vertices representing the 2 sides
            DfgVar* const lVtxp = getVertex(vrefp)->as<DfgVar>();
            DfgVertex* const rVtxp = getVertex(nodep->rhsp());
            lVtxp->driverp(rVtxp);
            lVtxp->assignmentFileline(nodep->fileline());
            commitVertices();

            // Remove assignment from Ast. Now represented by the Dfg.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);

            //
            ++m_ctx.m_representable;
            return;
        }

        // TODO: handle complex left-hand sides
        markReferenced(nodep);
        ++m_ctx.m_nonRepLhs;
    }

    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(!nodep->user1p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;

        if (nodep->access().isRW()  // Cannot represent read-write references
            || nodep->varp()->isIfaceRef()  // Cannot handle interface references
            || nodep->varp()->delayp()  // Cannot handle delayed variables
            || nodep->classOrPackagep()  // Cannot represent cross module references
        ) {
            markReferenced(nodep);
            m_foundUnhandled = true;
            ++m_ctx.m_nonRepVarRef;
            return;
        }

        // Sadly sometimes AstVarRef does not have the same dtype as the referenced variable
        if (!DfgVertex::isSupportedDType(nodep->varp()->dtypep())) {
            m_foundUnhandled = true;
            ++m_ctx.m_nonRepVarRef;
            return;
        }

        nodep->user1p(getNet(nodep->varp()));
    }

    void visit(AstConst* nodep) override {
        UASSERT_OBJ(!nodep->user1p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        DfgVertex* const vtxp = new DfgConst{*m_dfgp, nodep->cloneTree(false)};
        m_uncommittedVertices.push_back(vtxp);
        nodep->user1p(vtxp);
    }

    // The rest of the 'visit' methods are generated by 'astgen'
#include "V3Dfg__gen_ast_to_dfg.h"

    // CONSTRUCTOR
    explicit AstToDfgVisitor(AstModule& module, V3DfgOptimizationContext& ctx)
        : m_dfgp{new DfgGraph{module, module.name()}}
        , m_ctx{ctx} {
        // Build the DFG
        iterateChildren(&module);
        UASSERT_OBJ(m_uncommittedVertices.empty(), &module, "Uncommitted vertices remain");
    }

public:
    static DfgGraph* apply(AstModule& module, V3DfgOptimizationContext& ctx) {
        return AstToDfgVisitor{module, ctx}.m_dfgp;
    }
};

DfgGraph* V3DfgPasses::astToDfg(AstModule& module, V3DfgOptimizationContext& ctx) {
    return AstToDfgVisitor::apply(module, ctx);
}
