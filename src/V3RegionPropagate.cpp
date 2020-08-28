// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Propagate region information to CFunc and CCall
//
// Code available from: https://verilator.org
//
//*************************************************************************
// V3RegionPropagate's Transformations:
//
//  Propagates region information to CFunc and CCall nodes
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3RegionPropagate.h"
#include "V3Ast.h"

#include <map>

class RegionPropagateVisitor : public AstNVisitor {
    VRegion m_region;
    bool m_inFunc;
private:
    VRegion updateRegion(VRegion region, AstNode* nodep) {
        bool mixedRegions = false;
        if (region.isActive()) {
            mixedRegions = (m_region == VRegion::REACTIVE);
            region = VRegion::ACTIVE;
        }
        else if (region.isReactive()) {
            mixedRegions = (m_region == VRegion::ACTIVE);
            region = VRegion::REACTIVE;
        }
        UASSERT_OBJ(!mixedRegions, nodep, "Expressions from different regions detected in a single function");
        return region;
    }
    // VISITORS
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        m_inFunc = true;
        m_region = VRegion::NONE;
        iterateChildren(nodep);
        m_inFunc = false;
        nodep->region(m_region);
    }
    virtual void visit(AstCCall* nodep) VL_OVERRIDE {
        nodep->region(nodep->funcp()->region());
    }
    virtual void visit(AstAssign* nodep) VL_OVERRIDE {
        if (m_inFunc) {
            m_region = updateRegion(nodep->region(), nodep);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        if (m_inFunc) {
            m_region = updateRegion(nodep->region(), nodep);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit RegionPropagateVisitor(AstNetlist* nodep) {
        m_inFunc = false;
        iterateChildren(nodep);
        V3Global::dumpCheckGlobalTree("region_prop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
    virtual ~RegionPropagateVisitor() {}
};

//######################################################################
// Region class functions

void V3RegionPropagate::propagateRegions(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    RegionPropagateVisitor visitor(nodep);
}
