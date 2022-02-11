// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generated Clock repairs
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
// GENCLK TRANSFORMATIONS:
//      Follow control-flow graph with assignments and var usages
//          Assignment to variable later used as clock requires change detect
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3GenClk.h"
#include "V3Ast.h"

//######################################################################
// GenClk Read

class GenClkRenameVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user1()    -> AstVarScope*.  Signal replacing activation with
    const VNUser2InUse m_user2InUse;

    // STATE
    bool m_inSensitivityList = false;  // Inside sensitivity list
    AstScope* const m_scopetopp;  // The top level AstScope

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVarScope* genInpClk(AstVarScope* vscp) {
        if (!vscp->user2p()) {
            // In order to create a __VinpClk* for a signal, it needs to be marked circular.
            // The DPI export trigger is never marked circular by V3Order (see comments in
            // OrderVisitor::nodeMarkCircular). The only other place where one might mark
            // a node circular is in this pass (V3GenClk), if the signal is assigned but was
            // previously used as a clock. The DPI export trigger is only ever assigned in
            // a DPI export called from outside eval, or from a DPI import, which are not
            // discovered by GenClkReadVisitor (note that impure tasks - i.e.: those setting
            // non-local variables - cannot be no-inline, see V3Task), hence the DPI export
            // trigger should never be marked circular. Note that ordering should still be
            // correct as there will be a change detect on any signals set from a DPI export
            // that might have dependents scheduled earlier.
            UASSERT_OBJ(vscp != v3Global.rootp()->dpiExportTriggerp(), vscp,
                        "DPI export trigger should not need __VinpClk");
            AstVar* const varp = vscp->varp();
            const string newvarname
                = "__VinpClk__" + vscp->scopep()->nameDotless() + "__" + varp->name();
            // Create:  VARREF(inpclk)
            //          ...
            //          ASSIGN(VARREF(inpclk), VARREF(var))
            AstVar* const newvarp
                = new AstVar(varp->fileline(), VVarType::MODULETEMP, newvarname, varp);
            m_scopetopp->modp()->addStmtp(newvarp);
            AstVarScope* const newvscp = new AstVarScope(vscp->fileline(), m_scopetopp, newvarp);
            m_scopetopp->addVarp(newvscp);
            AstAssign* const asninitp = new AstAssign(
                vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, VAccess::WRITE),
                new AstVarRef(vscp->fileline(), vscp, VAccess::READ));
            m_scopetopp->addFinalClkp(asninitp);
            //
            vscp->user2p(newvscp);
        }
        return VN_AS(vscp->user2p(), VarScope);
    }

    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        if (!m_inSensitivityList) return;

        AstVarScope* const vscp = nodep->varScopep();
        if (vscp->isCircular()) {
            // Replace with the new variable
            AstVarScope* const newvscp = genInpClk(vscp);
            FileLine* const flp = nodep->fileline();
            AstVarRef* const newrefp = new AstVarRef{flp, newvscp, nodep->access()};
            nodep->replaceWith(newrefp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    virtual void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_inSensitivityList, nodep, "Should not nest");
        m_inSensitivityList = true;
        iterate(nodep->sensesp());
        m_inSensitivityList = false;
    }

    //-----
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    GenClkRenameVisitor(AstNetlist* netlistp, AstEval* nodep)
        : m_scopetopp{netlistp->topScopep()->scopep()} {
        iterate(nodep);
    }
    virtual ~GenClkRenameVisitor() override = default;
};

//######################################################################
// GenClk Read

class GenClkReadVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user1()     -> bool.  Set when the var has been used as clock

    // STATE
    bool m_tracingCall = false;  // Iterating into a call to a cfunc
    bool m_inSensitivityList = false;  // Inside sensitivity list

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        m_tracingCall = true;
        iterate(nodep->funcp());
    }
    virtual void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(m_tracingCall, nodep, "???");
        m_tracingCall = false;
        iterateChildrenConst(nodep);
    }
    //----

    virtual void visit(AstVarRef* nodep) override {
        AstVarScope* const vscp = nodep->varScopep();
        if (m_inSensitivityList) {
            // Variable reference in a sensitivity list
            vscp->user1(true);
        } else if (vscp->user1() && nodep->access().isWriteOrRW()) {
            // Variable was previously used in a sensitivity list, and is now being set, thus an
            // unordered generated clock
            vscp->circular(true);
        }
    }
    virtual void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_inSensitivityList, nodep, "Should not nest");
        m_inSensitivityList = true;
        iterate(nodep->sensesp());
        m_inSensitivityList = false;
        iterateChildrenConst(nodep);
    }

    //-----
    virtual void visit(AstVar*) override {}  // Accelerate
    virtual void visit(AstVarScope*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit GenClkReadVisitor(AstNetlist* netlistp) {
        // All AstEval are under the top level AstScope
        AstScope* const scopeTopp = netlistp->topScopep()->scopep();
        for (AstNode* nodep = scopeTopp->blocksp(); nodep; nodep = nodep->nextp()) {
            if (AstEval* const evalp = VN_CAST(nodep, Eval)) {
                {
                    const VNUser1InUse user1InUse;
                    iterate(evalp);
                }
                GenClkRenameVisitor{netlistp, evalp};
            }
        }
    }
    virtual ~GenClkReadVisitor() override = default;
};

//######################################################################
// GenClk class functions

void V3GenClk::genClkAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { GenClkReadVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("genclk", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
