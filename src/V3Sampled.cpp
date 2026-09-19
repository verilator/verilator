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
//   Remove SAMPLED.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Sampled.h"

#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Clock state, as a visitor of each AstNode

class SampledVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVarScope::user1()  -> AstVarScope*. The VarScope that stores sampled value
    //  AstVarRef::user1()    -> bool. Whether already converted
    const VNUser1InUse m_user1InUse;

    // STATE - across all visitors
    // Keys remain in the tree as the sampled variables' value expressions.
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_forceSamples;

    // STATE - for current visit position (use VL_RESTORER)
    AstScope* m_scopep = nullptr;  // Current scope
    bool m_inSampled = false;  // True inside a sampled expression
    V3UniqueNames m_forceNames{"__Vsampled_force"};  // Names for sampled force values

    // METHODS

    AstVarScope* createSampledVar(AstVarScope* vscp) {
        if (vscp->user1p()) return VN_AS(vscp->user1p(), VarScope);
        const AstVar* const varp = vscp->varp();
        const string newvarname
            = "__Vsampled_" + vscp->scopep()->nameDotless() + "__" + varp->name();
        FileLine* const flp = vscp->fileline();
        AstVar* const newvarp = new AstVar{flp, VVarType::MODULETEMP, newvarname, varp->dtypep()};
        m_scopep->modp()->addStmtsp(newvarp);
        AstVarScope* const newvscp = new AstVarScope{flp, m_scopep, newvarp};
        newvarp->sampled(true);
        vscp->user1p(newvscp);
        m_scopep->addVarsp(newvscp);
        // At the top of _eval, assign them (use valuep here as temporary storage during V3Sched)
        newvarp->valuep(new AstVarRef{flp, vscp, VAccess::READ});
        UINFO(4, "New Sampled: " << newvscp);
        return newvscp;
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        VL_RESTORER_COPY(m_forceNames);
        m_scopep = nodep;
        m_forceNames.reset();
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
        if (pair.second) {
            vscp = m_scopep->createTemp(m_forceNames.get(nodep), nodep->dtypep());
            vscp->varp()->sampled(true);
        }
        AstVarRef* const refp = new AstVarRef{nodep->fileline(), vscp, VAccess::READ};
        refp->user1SetOnce();
        nodep->replaceWith(refp);
        if (pair.second) {
            vscp->varp()->valuep(nodep);
        } else {
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_inSampled && !nodep->user1SetOnce()) {
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Should have failed in V3Access");
            AstVarScope* const varscp = nodep->varScopep();
            AstVarScope* const lastscp = createSampledVar(varscp);
            AstNode* const newp = new AstVarRef{nodep->fileline(), lastscp, VAccess::READ};
            newp->user1SetOnce();  // Don't sample this one
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SampledVisitor(AstNetlist* netlistp) { iterate(netlistp); }
    ~SampledVisitor() override = default;
};

//######################################################################
// Sampled class functions

void V3Sampled::sampledAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { SampledVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("sampled", 0, dumpTreeEitherLevel() >= 3);
}
