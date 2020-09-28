// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Assigning statements to regions
//
//*************************************************************************
// V3Region's Transformations:
//
//  Adds region information to nodes
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Region.h"
#include "V3Ast.h"

#include <map>

class RegionVisitor : public AstNVisitor {
    bool m_inReactive = false;

private:
    void markStmt(AstNodeStmt* nodep, bool inactive = false) {
        if (inactive)
            nodep->region(m_inReactive ? VRegion::REINACTIVE : VRegion::INACTIVE);
        else
            nodep->region(m_inReactive ? VRegion::REACTIVE : VRegion::ACTIVE);
    }

    // VISITORS
    virtual void visit(AstModule* nodep) override {
        m_inReactive = nodep->isProgram();
        iterateChildren(nodep);
        m_inReactive = false;
    }

    virtual void visit(AstNodeProcedure* nodep) override {
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeFTask* nodep) override {
        iterateChildren(nodep);
    }

    virtual void visit(AstAssignDly* nodep) override {
        nodep->region(m_inReactive ? VRegion::RENBA : VRegion::NBA);
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeCoverOrAssert* nodep) override {
        if (nodep->immediate()) {
            markStmt(nodep);
            iterateChildren(nodep);
            return;
        }
        nodep->region(VRegion::OBSERVED);
        const AstAssert* assertp = VN_CAST(nodep, Assert);
        VL_RESTORER(m_inReactive);
        if (assertp) m_inReactive = true;
        iterateChildren(nodep);
    }

    virtual void visit(AstNodeStmt* nodep) override {
        markStmt(nodep);
        iterateChildren(nodep);
    }

    virtual void visit(AstDelay* nodep) override {
        const AstConst* constp = VN_CAST(nodep->lhsp(), Const);
        UASSERT_OBJ(constp, nodep, "Delay value isn't a constant!");

        bool inactive = (constp->toUInt() == 0);
        markStmt(nodep, inactive);
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit RegionVisitor(AstNetlist* nodep) {
        iterateChildren(nodep);
        V3Global::dumpCheckGlobalTree("region", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
    virtual ~RegionVisitor() {}
};

//######################################################################
// Region class functions

void V3Region::assignRegions(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    RegionVisitor visitor(nodep);
}
