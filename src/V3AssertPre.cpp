// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Pre steps:
//      Attach clocks to each assertion
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3AssertPre.h"

#include <cstdarg>
#include <iomanip>

//######################################################################
// Assert class functions

class AssertPreVisitor : public AstNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE/TYPES
    // STATE
    // Reset each module:
    AstNodeSenItem* m_seniDefaultp;  // Default sensitivity (from AstDefClock)
    // Reset each assertion:
    AstNodeSenItem* m_senip;  // Last sensitivity
    // Reset each always:
    AstNodeSenItem* m_seniAlwaysp;  // Last sensitivity in always

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstSenTree* newSenTree(AstNode* nodep) {
        // Create sentree based on clocked or default clock
        // Return NULL for always
        AstSenTree* newp = NULL;
        AstNodeSenItem* senip = m_senip;
        if (!senip) senip = m_seniDefaultp;
        if (!senip) senip = m_seniAlwaysp;
        if (!senip) {
            nodep->v3error("Unsupported: Unclocked assertion");
            newp = new AstSenTree(nodep->fileline(), NULL);
        } else {
            newp = new AstSenTree(nodep->fileline(), senip->cloneTree(true));
        }
        return newp;
    }
    void clearAssertInfo() {
        m_senip = NULL;
    }

    // VISITORS
    //========== Statements
    virtual void visit(AstClocking* nodep) VL_OVERRIDE {
        UINFO(8,"   CLOCKING"<<nodep<<endl);
        // Store the new default clock, reset on new module
        m_seniDefaultp = nodep->sensesp();
        // Trash it, keeping children
        if (nodep->bodysp()) {
            nodep->replaceWith(nodep->bodysp()->unlinkFrBack());
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        iterateAndNextNull(nodep->sensesp());
        if (nodep->sensesp()) {
            m_seniAlwaysp = nodep->sensesp()->sensesp();
        }
        iterateAndNextNull(nodep->bodysp());
        m_seniAlwaysp = NULL;
    }

    virtual void visit(AstNodeCoverOrAssert* nodep) VL_OVERRIDE {
        if (nodep->sentreep()) return;  // Already processed
        clearAssertInfo();
        // Find Clocking's buried under nodep->exprsp
        iterateChildren(nodep);
        if (!nodep->immediate()) {
            nodep->sentreep(newSenTree(nodep));
        }
        clearAssertInfo();
    }
    virtual void visit(AstPast* nodep) VL_OVERRIDE {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        nodep->sentreep(newSenTree(nodep));
    }
    virtual void visit(AstPropClocked* nodep) VL_OVERRIDE {
        // No need to iterate the body, once replace will get iterated
        iterateAndNextNull(nodep->sensesp());
        if (m_senip) {
            nodep->v3error("Unsupported: Only one PSL clock allowed per assertion");
        }
        // Block is the new expression to evaluate
        AstNode* blockp = nodep->propp()->unlinkFrBack();
        if (nodep->disablep()) {
            if (VN_IS(nodep->backp(), Cover)) {
                blockp = new AstAnd(nodep->disablep()->fileline(),
                                    new AstNot(nodep->disablep()->fileline(),
                                               nodep->disablep()->unlinkFrBack()),
                                    blockp);
            } else {
                blockp = new AstOr(nodep->disablep()->fileline(),
                                   nodep->disablep()->unlinkFrBack(),
                                   blockp);
            }
        }
        // Unlink and just keep a pointer to it, convert to sentree as needed
        m_senip = nodep->sensesp();
        nodep->replaceWith(blockp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Reset defaults
        m_seniDefaultp = NULL;
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit AssertPreVisitor(AstNetlist* nodep) {
        m_seniDefaultp = NULL;
        m_seniAlwaysp = NULL;
        clearAssertInfo();
        // Process
        iterate(nodep);
    }
    virtual ~AssertPreVisitor() {}
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        AssertPreVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertpre", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
