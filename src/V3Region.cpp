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
    bool m_inProgram;
private:

    // VISITORS
    virtual void visit(AstModule* nodep) VL_OVERRIDE {
        m_inProgram = nodep->isProgram();
        iterateChildren(nodep);
        m_inProgram = false;
    }
    virtual void visit(AstAssignDly* nodep) VL_OVERRIDE {
        nodep->region(m_inProgram ? VRegion::RENBA : VRegion::NBA);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        nodep->region(m_inProgram ? VRegion::REACTIVE : VRegion::ACTIVE);
        UINFO(4, "Region AstNodeStmt " << nodep << endl);
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit RegionVisitor(AstNetlist* nodep) {
        m_inProgram = false;
        iterateChildren(nodep);
        V3Global::dumpCheckGlobalTree("region", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
    virtual ~RegionVisitor() {}
};

//######################################################################
// Region class functions

void V3Region::insertRegions(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    RegionVisitor visitor(nodep);
}
