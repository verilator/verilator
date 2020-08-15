// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generated Clock repairs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// GENCLK TRANSFORMATIONS:
//      Follow control-flow graph with assignments and var usages
//          ASSIGNDLY to variable later used as clock requires change detect
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3GenClk.h"
#include "V3Ast.h"

//######################################################################
// GenClk state, as a visitor of each AstNode

class GenClkBaseVisitor : public AstNVisitor {
protected:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// GenClk Read

class GenClkRenameVisitor : public GenClkBaseVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user2()    -> AstVarScope*.  Signal replacing activation with
    //  AstVarRef::user3()      -> bool.  Signal is replaced activation (already done)
    AstUser2InUse m_inuser2;
    AstUser3InUse m_inuser3;

    // STATE
    AstActive* m_activep;  // Inside activate statement
    AstNodeModule* m_topModp;  // Top module
    AstScope* m_scopetopp;  // Scope under TOPSCOPE

    // METHODS
    AstVarScope* genInpClk(AstVarScope* vscp) {
        if (vscp->user2p()) {
            return VN_CAST(vscp->user2p(), VarScope);
        } else {
            AstVar* varp = vscp->varp();
            string newvarname
                = "__VinpClk__" + vscp->scopep()->nameDotless() + "__" + varp->name();
            // Create:  VARREF(inpclk)
            //          ...
            //          ASSIGN(VARREF(inpclk), VARREF(var))
            AstVar* newvarp
                = new AstVar(varp->fileline(), AstVarType::MODULETEMP, newvarname, varp);
            m_topModp->addStmtp(newvarp);
            AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopetopp, newvarp);
            m_scopetopp->addVarp(newvscp);
            AstAssign* asninitp
                = new AstAssign(vscp->fileline(), new AstVarRef(vscp->fileline(), newvscp, true),
                                new AstVarRef(vscp->fileline(), vscp, false));
            m_scopetopp->addFinalClkp(asninitp);
            //
            vscp->user2p(newvscp);
            return newvscp;
        }
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        AstNode::user2ClearTree();  // user2p() used on entire tree

        AstScope* scopep = nodep->scopep();
        UASSERT_OBJ(scopep, nodep, "No scope found on top level");
        m_scopetopp = scopep;

        iterateChildren(nodep);
    }
    //----
    virtual void visit(AstVarRef* nodep) override {
        // Consumption/generation of a variable,
        AstVarScope* vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (m_activep && !nodep->user3()) {
            nodep->user3(true);
            if (vscp->isCircular()) {
                UINFO(8, "  VarActReplace " << nodep << endl);
                // Replace with the new variable
                AstVarScope* newvscp = genInpClk(vscp);
                AstVarRef* newrefp = new AstVarRef(nodep->fileline(), newvscp, nodep->lvalue());
                nodep->replaceWith(newrefp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
        }
    }
    virtual void visit(AstActive* nodep) override {
        m_activep = nodep;
        UASSERT_OBJ(nodep->sensesp(), nodep, "Unlinked");
        iterateChildren(nodep->sensesp());  // iterateAndNext?
        m_activep = nullptr;
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) override { iterateChildren(nodep); }

    //-----
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    GenClkRenameVisitor(AstTopScope* nodep, AstNodeModule* topModp) {
        m_topModp = topModp;
        m_scopetopp = nullptr;
        m_activep = nullptr;
        iterate(nodep);
    }
    virtual ~GenClkRenameVisitor() override {}
};

//######################################################################
// GenClk Read

class GenClkReadVisitor : public GenClkBaseVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user()     -> bool.  Set when the var has been used as clock
    AstUser1InUse m_inuser1;

    // STATE
    AstActive* m_activep;  // Inside activate statement
    bool m_tracingCall;  // Iterating into a call to a cfunc
    AstNodeAssign* m_assignp;  // Inside assigndly statement
    AstNodeModule* m_topModp;  // Top module

    // VISITORS
    virtual void visit(AstTopScope* nodep) override {
        AstNode::user1ClearTree();  // user1p() used on entire tree
        iterateChildren(nodep);
        {
            // Make the new clock signals and replace any activate references
            // See rename, it does some AstNode::userClearTree()'s
            GenClkRenameVisitor visitor(nodep, m_topModp);
        }
    }
    virtual void visit(AstNodeModule* nodep) override {
        // Only track the top scopes, not lower level functions
        if (nodep->isTop()) {
            m_topModp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        if (!nodep->funcp()->entryPoint()) {
            // Enter the function and trace it
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        if (!m_tracingCall && !nodep->entryPoint()) {
            // Only consider logic within a CFunc when looking
            // at the call to it, and not when scanning whatever
            // scope it happens to live beneath.
            return;
        }
        m_tracingCall = false;
        iterateChildren(nodep);
    }
    //----

    virtual void visit(AstVarRef* nodep) override {
        // Consumption/generation of a variable,
        AstVarScope* vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (m_activep) {
            UINFO(8, "  VarAct " << nodep << endl);
            vscp->user1(true);
        }
        if (m_assignp && nodep->lvalue() && vscp->user1()) {
            // Variable was previously used as a clock, and is now being set
            // Thus a unordered generated clock...
            UINFO(8, "  VarSetAct " << nodep << endl);
            vscp->circular(true);
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        // UINFO(8, "ASS " << nodep << endl);
        m_assignp = nodep;
        iterateChildren(nodep);
        m_assignp = nullptr;
    }
    virtual void visit(AstActive* nodep) override {
        UINFO(8, "ACTIVE " << nodep << endl);
        m_activep = nodep;
        UASSERT_OBJ(nodep->sensesp(), nodep, "Unlinked");
        iterateChildren(nodep->sensesp());  // iterateAndNext?
        m_activep = nullptr;
        iterateChildren(nodep);
    }

    //-----
    virtual void visit(AstVar*) override {}  // Don't want varrefs under it
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit GenClkReadVisitor(AstNetlist* nodep)
        : m_activep(nullptr)
        , m_tracingCall(false)
        , m_assignp(nullptr)
        , m_topModp(nullptr) {
        iterate(nodep);
    }
    virtual ~GenClkReadVisitor() override {}
};

//######################################################################
// GenClk class functions

void V3GenClk::genClkAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { GenClkReadVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("genclk", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
