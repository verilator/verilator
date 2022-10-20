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
template <typename Vertex, typename Node>
Vertex* makeVertex(const Node* nodep, DfgGraph& dfg) {
    return new Vertex{dfg, nodep->fileline(), DfgVertex::dtypeFor(nodep)};
}

//======================================================================
// Currently unhandled nodes
// LCOV_EXCL_START
// AstCCast changes width, but should not exists where DFG optimization is currently invoked
template <>
DfgCCast* makeVertex<DfgCCast, AstCCast>(const AstCCast*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgAtoN* makeVertex<DfgAtoN, AstAtoN>(const AstAtoN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on strings which we don't optimize anyway
template <>
DfgCompareNN* makeVertex<DfgCompareNN, AstCompareNN>(const AstCompareNN*, DfgGraph&) {
    return nullptr;
}
// Unhandled in DfgToAst, but also operates on unpacked arrays which we don't optimize anyway
template <>
DfgSliceSel* makeVertex<DfgSliceSel, AstSliceSel>(const AstSliceSel*, DfgGraph&) {
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
    bool m_converting = false;  // We are trying to convert some logic at the moment
    std::vector<DfgVarPacked*> m_varPackedps;  // All the DfgVarPacked vertices we created.
    std::vector<DfgVarArray*> m_varArrayps;  // All the DfgVarArray vertices we created.

    // METHODS
    void markReferenced(AstNode* nodep) {
        nodep->foreach([this](const AstVarRef* refp) {
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

    DfgVertexVar* getNet(AstVar* varp) {
        if (!varp->user1p()) {
            // Note DfgVertexVar vertices are not added to m_uncommittedVertices, because we
            // want to hold onto them via AstVar::user1p, and the AstVar might be referenced via
            // multiple AstVarRef instances, so we will never revert a DfgVertexVar once
            // created. We will delete unconnected variable vertices at the end.
            if (VN_IS(varp->dtypep()->skipRefp(), UnpackArrayDType)) {
                DfgVarArray* const vtxp = new DfgVarArray{*m_dfgp, varp};
                varp->user1p();
                m_varArrayps.push_back(vtxp);
                varp->user1p(vtxp);
            } else {
                DfgVarPacked* const vtxp = new DfgVarPacked{*m_dfgp, varp};
                m_varPackedps.push_back(vtxp);
                varp->user1p(vtxp);
            }
        }
        return varp->user1u().to<DfgVertexVar*>();
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

    // Build DfgEdge representing the LValue assignment. Returns false if unsuccessful.
    bool convertAssignment(FileLine* flp, AstNode* nodep, DfgVertex* vtxp) {
        if (AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            m_foundUnhandled = false;
            visit(vrefp);
            if (m_foundUnhandled) return false;
            getVertex(vrefp)->as<DfgVarPacked>()->addDriver(flp, 0, vtxp);
            return true;
        }
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            AstVarRef* const vrefp = VN_CAST(selp->fromp(), VarRef);
            const AstConst* const lsbp = VN_CAST(selp->lsbp(), Const);
            if (!vrefp || !lsbp || !VN_IS(selp->widthp(), Const)) {
                ++m_ctx.m_nonRepLhs;
                return false;
            }
            m_foundUnhandled = false;
            visit(vrefp);
            if (m_foundUnhandled) return false;
            getVertex(vrefp)->as<DfgVarPacked>()->addDriver(flp, lsbp->toUInt(), vtxp);
            return true;
        }
        if (AstArraySel* const selp = VN_CAST(nodep, ArraySel)) {
            AstVarRef* const vrefp = VN_CAST(selp->fromp(), VarRef);
            const AstConst* const idxp = VN_CAST(selp->bitp(), Const);
            if (!vrefp || !idxp) {
                ++m_ctx.m_nonRepLhs;
                return false;
            }
            m_foundUnhandled = false;
            visit(vrefp);
            if (m_foundUnhandled) return false;
            getVertex(vrefp)->as<DfgVarArray>()->addDriver(flp, idxp->toUInt(), vtxp);
            return true;
        }
        if (AstConcat* const concatp = VN_CAST(nodep, Concat)) {
            AstNode* const lhsp = concatp->lhsp();
            AstNode* const rhsp = concatp->rhsp();

            {
                FileLine* const lFlp = lhsp->fileline();
                DfgSel* const lVtxp = new DfgSel{*m_dfgp, lFlp, DfgVertex::dtypeFor(lhsp)};
                lVtxp->fromp(vtxp);
                lVtxp->lsb(rhsp->width());
                if (!convertAssignment(flp, lhsp, lVtxp)) return false;
            }

            {
                FileLine* const rFlp = rhsp->fileline();
                DfgSel* const rVtxp = new DfgSel{*m_dfgp, rFlp, DfgVertex::dtypeFor(rhsp)};
                rVtxp->fromp(vtxp);
                rVtxp->lsb(0);
                return convertAssignment(flp, rhsp, rVtxp);
            }
        }
        ++m_ctx.m_nonRepLhs;
        return false;
    }

    bool convertEquation(AstNode* nodep, FileLine* flp, AstNode* lhsp, AstNode* rhsp) {
        UASSERT_OBJ(m_uncommittedVertices.empty(), nodep, "Should not nest");

        // Currently cannot handle direct assignments between unpacked types. These arise e.g.
        // when passing an unpacked array through a module port.
        if (!DfgVertex::isSupportedPackedDType(lhsp->dtypep())
            || !DfgVertex::isSupportedPackedDType(rhsp->dtypep())) {
            markReferenced(nodep);
            ++m_ctx.m_nonRepDType;
            return false;
        }

        // Cannot handle mismatched widths. Mismatched assignments should have been fixed up in
        // earlier passes anyway, so this should never be hit, but being paranoid just in case.
        if (lhsp->width() != rhsp->width()) {  // LCOV_EXCL_START
            markReferenced(nodep);
            ++m_ctx.m_nonRepWidth;
            return false;
        }  // LCOV_EXCL_STOP

        VL_RESTORER(m_converting);
        m_converting = true;

        m_foundUnhandled = false;
        iterate(rhsp);
        if (m_foundUnhandled) {
            revertUncommittedVertices();
            markReferenced(nodep);
            return false;
        }

        if (!convertAssignment(flp, lhsp, getVertex(rhsp))) {
            revertUncommittedVertices();
            markReferenced(nodep);
            return false;
        }

        // Connect the rhs vertex to the driven edge
        commitVertices();

        // Remove node from Ast. Now represented by the Dfg.
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);

        //
        ++m_ctx.m_representable;
        return true;
    }

    // Canonicalize packed variables
    void canonicalizePacked() {
        for (DfgVarPacked* const varp : m_varPackedps) {
            // Delete variables with no sinks nor sources (this can happen due to reverting
            // uncommitted vertices, which does not remove variables)
            if (!varp->hasSinks() && varp->arity() == 0) {
                VL_DO_DANGLING(varp->unlinkDelete(*m_dfgp), varp);
                continue;
            }

            // Gather (and unlink) all drivers
            struct Driver {
                FileLine* flp;
                uint32_t lsb;
                DfgVertex* vtxp;
                Driver(FileLine* flp, uint32_t lsb, DfgVertex* vtxp)
                    : flp{flp}
                    , lsb{lsb}
                    , vtxp{vtxp} {}
            };
            std::vector<Driver> drivers;
            drivers.reserve(varp->arity());
            varp->forEachSourceEdge([varp, &drivers](DfgEdge& edge, size_t idx) {
                UASSERT(edge.sourcep(), "Should not have created undriven sources");
                drivers.emplace_back(varp->driverFileLine(idx), varp->driverLsb(idx),
                                     edge.sourcep());
                edge.unlinkSource();
            });

            // Sort drivers by LSB
            std::stable_sort(drivers.begin(), drivers.end(),
                             [](const Driver& a, const Driver& b) { return a.lsb < b.lsb; });

            // TODO: bail on multidriver

            // Coalesce adjacent ranges
            for (size_t i = 0, j = 1; j < drivers.size(); ++j) {
                Driver& a = drivers[i];
                Driver& b = drivers[j];

                // Coalesce adjacent range
                const uint32_t aWidth = a.vtxp->width();
                const uint32_t bWidth = b.vtxp->width();
                if (a.lsb + aWidth == b.lsb) {
                    const auto dtypep = DfgVertex::dtypeForWidth(aWidth + bWidth);
                    DfgConcat* const concatp = new DfgConcat{*m_dfgp, a.flp, dtypep};
                    concatp->rhsp(a.vtxp);
                    concatp->lhsp(b.vtxp);
                    a.vtxp = concatp;
                    b.vtxp = nullptr;  // Mark as moved
                    ++m_ctx.m_coalescedAssignments;
                    continue;
                }

                ++i;

                // Compact non-adjacent ranges within the vector
                if (j != i) {
                    Driver& c = drivers[i];
                    UASSERT_OBJ(!c.vtxp, c.flp, "Should have been marked moved");
                    c = b;
                    b.vtxp = nullptr;  // Mark as moved
                }
            }

            // Reinsert sources in order
            varp->resetSources();
            for (const Driver& driver : drivers) {
                if (!driver.vtxp) break;  // Stop at end of cmpacted list
                varp->addDriver(driver.flp, driver.lsb, driver.vtxp);
            }
        }
    }

    // Canonicalize array variables
    void canonicalizeArray() {
        for (DfgVarArray* const varp : m_varArrayps) {
            // Delete variables with no sinks nor sources (this can happen due to reverting
            // uncommitted vertices, which does not remove variables)
            if (!varp->hasSinks() && varp->arity() == 0) {
                VL_DO_DANGLING(varp->unlinkDelete(*m_dfgp), varp);
            }
        }
    }

    // VISITORS
    void visit(AstNode* nodep) override {
        // Conservatively treat this node as unhandled
        if (!m_foundUnhandled && m_converting) ++m_ctx.m_nonRepUnknown;
        m_foundUnhandled = true;
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
        ++m_ctx.m_inputEquations;

        // Cannot handle assignment with timing control yet
        if (nodep->timingControlp()) {
            markReferenced(nodep);
            ++m_ctx.m_nonRepTiming;
            return;
        }

        convertEquation(nodep, nodep->fileline(), nodep->lhsp(), nodep->rhsp());
    }

    void visit(AstAlways* nodep) override {
        // Ignore sequential logic, or if there are multiple statements
        const VAlwaysKwd kwd = nodep->keyword();
        if (nodep->sensesp() || !nodep->isJustOneBodyStmt()
            || (kwd != VAlwaysKwd::ALWAYS && kwd != VAlwaysKwd::ALWAYS_COMB)) {
            markReferenced(nodep);
            return;
        }

        AstNode* const stmtp = nodep->stmtsp();

        if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
            ++m_ctx.m_inputEquations;
            if (assignp->timingControlp()) {
                markReferenced(stmtp);
                ++m_ctx.m_nonRepTiming;
                return;
            }
            convertEquation(nodep, assignp->fileline(), assignp->lhsp(), assignp->rhsp());
        } else if (AstIf* const ifp = VN_CAST(stmtp, If)) {
            // Will only handle single assignments to the same LHS in both branches
            AstAssign* const thenp = VN_CAST(ifp->thensp(), Assign);
            AstAssign* const elsep = VN_CAST(ifp->elsesp(), Assign);
            if (!thenp || !elsep || thenp->nextp() || elsep->nextp()
                || !thenp->lhsp()->sameTree(elsep->lhsp())) {
                markReferenced(stmtp);
                return;
            }

            ++m_ctx.m_inputEquations;
            if (thenp->timingControlp() || elsep->timingControlp()) {
                markReferenced(stmtp);
                ++m_ctx.m_nonRepTiming;
                return;
            }

            // Create a conditional for the rhs by borrowing the components from the AstIf
            AstCond* const rhsp = new AstCond{ifp->fileline(),  //
                                              ifp->condp()->unlinkFrBack(),  //
                                              thenp->rhsp()->unlinkFrBack(),  //
                                              elsep->rhsp()->unlinkFrBack()};

            if (!convertEquation(nodep, ifp->fileline(), thenp->lhsp(), rhsp)) {
                // Failed to convert. Mark 'rhsp', as 'convertEquation' only marks 'nodep'.
                markReferenced(rhsp);
                // Put the AstIf back together
                ifp->condp(rhsp->condp()->unlinkFrBack());
                thenp->rhsp(rhsp->thenp()->unlinkFrBack());
                elsep->rhsp(rhsp->elsep()->unlinkFrBack());
            }
            // Delete the auxiliary conditional
            VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
        } else {
            markReferenced(stmtp);
        }
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
        DfgVertex* const vtxp = new DfgConst{*m_dfgp, nodep->fileline(), nodep->num()};
        m_uncommittedVertices.push_back(vtxp);
        nodep->user1p(vtxp);
    }

    void visit(AstSel* nodep) override {
        UASSERT_OBJ(!nodep->user1p(), nodep, "Already has Dfg vertex");
        if (unhandled(nodep)) return;
        if (!VN_IS(nodep->widthp(), Const)) {  // This should never be taken, but paranoia
            m_foundUnhandled = true;
            ++m_ctx.m_nonRepNode;
            return;
        }
        iterate(nodep->fromp());
        if (m_foundUnhandled) return;

        FileLine* const flp = nodep->fileline();
        DfgVertex* vtxp = nullptr;
        if (AstConst* const constp = VN_CAST(nodep->lsbp(), Const)) {
            DfgSel* const selp = new DfgSel{*m_dfgp, flp, DfgVertex::dtypeFor(nodep)};
            selp->fromp(nodep->fromp()->user1u().to<DfgVertex*>());
            selp->lsb(constp->toUInt());
            vtxp = selp;
        } else {
            iterate(nodep->lsbp());
            if (m_foundUnhandled) return;
            DfgMux* const muxp = new DfgMux{*m_dfgp, flp, DfgVertex::dtypeFor(nodep)};
            muxp->fromp(nodep->fromp()->user1u().to<DfgVertex*>());
            muxp->lsbp(nodep->lsbp()->user1u().to<DfgVertex*>());
            vtxp = muxp;
        }
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

        // Canonicalize variables
        canonicalizePacked();
        canonicalizeArray();
    }

public:
    static DfgGraph* apply(AstModule& module, V3DfgOptimizationContext& ctx) {
        return AstToDfgVisitor{module, ctx}.m_dfgp;
    }
};

DfgGraph* V3DfgPasses::astToDfg(AstModule& module, V3DfgOptimizationContext& ctx) {
    return AstToDfgVisitor::apply(module, ctx);
}
