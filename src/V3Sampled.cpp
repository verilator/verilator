// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Removal of SAMPLED
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
// V3Sampled's Transformations:
//
// Top Scope:
//   Replace each variable reference under SAMPLED with a new variable.
//   Remove SAMPLED.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Sampled.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Clock state, as a visitor of each AstNode

class SampledVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVarScope::user1()  -> AstVarScope*. The VarScope that stores sampled value
    //  AstVarRef::user1()    -> bool. Whether already converted
    const VNUser1InUse m_user1InUse;
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope
    bool m_inSampled = false;  // True inside a sampled expression

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
        newvarp->direction(VDirection::INPUT);  // Inform V3Sched that it will be driven later
        newvarp->primaryIO(true);
        vscp->user1p(newvscp);
        m_scopep->addVarsp(newvscp);
        // At the top of _eval, assign them (use valuep here as temporary storage during V3Sched)
        newvarp->valuep(new AstVarRef{flp, vscp, VAccess::READ});
        UINFO(4, "New Sampled: " << newvscp << endl);
        return newvscp;
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
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SampledVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("sampled", 0, dumpTreeEitherLevel() >= 3);
}
