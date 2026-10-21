// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Removal of SAMPLED
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Sampled's Transformations:
//
// Top Scope:
//   Replace each variable reference under SAMPLED with a new variable.
//   Capture whole-signal force reads by value, before sampling their children.
//   Assign the new variables in the 'sample' eval function.
//   Remove SAMPLED.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Sampled.h"

#include "V3Sched.h"
#include "V3SharedTmps.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Clock state, as a visitor of each AstNode

class SampledVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVarScope::user1()  -> AstVarScope*. The VarScope that stores sampled value
    //  AstVarRef::user1()    -> bool. Whether already converted
    const VNUser1InUse m_user1InUse;

    // STATE - across all visitors
    AstCFunc* const m_sampleFuncp;  // The 'sample' eval function assigning the sampled values
    V3SharedTmps m_sampledTmps{"__Vsampled", VVarType::MODULETEMP};  // Sampled variables
    V3SharedTmps m_forceTmps{"__VsampledForce", VVarType::MODULETEMP};  // Sampled force values
    // Keys remain in the tree as the sampled variables' value expressions.
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_forceSamples;

    // STATE - for current visit position (use VL_RESTORER)
    AstScope* m_scopep = nullptr;  // Current scope
    bool m_inSampled = false;  // True inside a sampled expression

    // METHODS

    // Create a variable in the current scope, assigned 'valuep' at the start of each evaluation
    AstVarScope* createSampledVar(V3SharedTmps& tmps, AstNodeExpr* valuep,
                                  const std::string& name) {
        FileLine* const flp = valuep->fileline();
        AstVarScope* const vscp = tmps.make(flp, m_scopep, valuep->dtypep(), name);
        vscp->varp()->sampled(true);
        AstVarRef* const lhsp = new AstVarRef{flp, vscp, VAccess::WRITE};
        m_sampleFuncp->addStmtsp(new AstAssign{flp, lhsp, valuep});
        UINFO(4, "New Sampled: " << vscp);
        return vscp;
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstSampled* nodep) override {
        VL_RESTORER(m_inSampled);
        m_inSampled = true;
        iterateChildren(nodep);
        nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstCMethodHard* nodep) override {
        if (!m_inSampled || nodep->method() != VCMethod::FORCE_READ) {
            iterateChildren(nodep);
            return;
        }
        // Force vectors hold pointers to live RHS shadows. Copying the vector and base
        // separately would let later writes change the sampled value (IEEE 1800-2023 16.5.1).
        // Whole-signal reads have no user expressions to evaluate at the point of use.
        const auto pair = m_forceSamples.emplace(*nodep, nullptr);
        AstVarScope*& vscp = pair.first->second;
        FileLine* const flp = nodep->fileline();
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        if (pair.second) {
            vscp = createSampledVar(m_forceTmps, nodep, "");
        } else {
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::READ};
        refp->user1SetOnce();
        relinker.relink(refp);
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_inSampled && !nodep->user1SetOnce()) {
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Should have failed in V3Access");
            AstVarScope* const vscp = nodep->varScopep();
            if (!vscp->user1p()) {
                AstVarRef* const valuep = new AstVarRef{vscp->fileline(), vscp, VAccess::READ};
                vscp->user1p(createSampledVar(m_sampledTmps, valuep, vscp->varp()->name()));
            }
            AstVarScope* const sampledp = VN_AS(vscp->user1p(), VarScope);
            AstNode* const newp = new AstVarRef{nodep->fileline(), sampledp, VAccess::READ};
            newp->user1SetOnce();  // Don't sample this one
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SampledVisitor(AstNetlist* netlistp)
        : m_sampleFuncp{netlistp->evalFuncp(VEval::SAMPLE)} {
        iterate(netlistp);
        V3Sched::util::splitCheck(m_sampleFuncp);
    }
    ~SampledVisitor() override = default;
};

//######################################################################
// Sampled class functions

void V3Sampled::sampledAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SampledVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("sampled", 0, dumpTreeEitherLevel() >= 3);
}
