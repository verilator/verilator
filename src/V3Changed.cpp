// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for changed nodes
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
// V3Changed's Transformations:
//
// Each module:
//      Each combo block
//          For each variable that comes from combo block and is generated AFTER a usage
//              Add __Vlast_{var} to local section, init to current value (just use array?)
//              Change = if any var != last.
//          If a signal is used as a clock in this module or any
//          module *below*, and it isn't a input to this module,
//          we need to indicate a new clock has been created.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Ast.h"
#include "V3Changed.h"
#include "V3EmitCBase.h"

#include <algorithm>
#include <cstdarg>
#include <set>

//######################################################################

class ChangedState {
public:
    // STATE
    AstNodeModule*      m_topModp;      // Top module
    AstScope*           m_scopetopp;    // Scope under TOPSCOPE
    AstCFunc*           m_chgFuncp;     // Change function we're building
    AstCFunc*           m_tlChgFuncp;   // Top level change function we're building
    int                 m_numStmts;     // Number of statements added to m_chgFuncp
    int                 m_funcNum;      // Number of change functions emitted

    ChangedState() {
        m_topModp = NULL;
        m_chgFuncp = NULL;
        m_scopetopp = NULL;
        m_tlChgFuncp = NULL;
        m_numStmts = 0;
        m_funcNum = 0;
    }
    ~ChangedState() {}

    void maybeCreateChgFuncp() {
        // Don't create an extra function call if splitting is disabled
        if (!v3Global.opt.outputSplitCFuncs()) {
            m_chgFuncp = m_tlChgFuncp;
            return;
        }
        if (!m_chgFuncp || v3Global.opt.outputSplitCFuncs() < m_numStmts) {
            m_chgFuncp = new AstCFunc(m_scopetopp->fileline(),
                                      "_change_request_" + cvtToStr(++m_funcNum),
                                      m_scopetopp, "QData");
            m_chgFuncp->argTypes(EmitCBaseVisitor::symClassVar());
            m_chgFuncp->symProlog(true);
            m_chgFuncp->declPrivate(true);
            m_scopetopp->addActivep(m_chgFuncp);

            // Add a top call to it
            AstCCall* callp = new AstCCall(m_scopetopp->fileline(), m_chgFuncp);
            callp->argTypes("vlSymsp");

            if (!m_tlChgFuncp->stmtsp()) {
                m_tlChgFuncp->addStmtsp(new AstCReturn(m_scopetopp->fileline(), callp));
            } else {
                AstCReturn* returnp = VN_CAST(m_tlChgFuncp->stmtsp(), CReturn);
                UASSERT_OBJ(returnp, m_scopetopp, "Lost CReturn in top change function");
                // This is currently using AstLogOr which will shortcut the
                // evaluation if any function returns true. This is likely what
                // we want and is similar to the logic already in use inside
                // V3EmitC, however, it also means that verbose logging may
                // miss to print change detect variables.
                AstNode* newp = new AstCReturn(m_scopetopp->fileline(),
                                               new AstLogOr(m_scopetopp->fileline(), callp,
                                                            returnp->lhsp()->unlinkFrBack()));
                returnp->replaceWith(newp);
                VL_DO_DANGLING(returnp->deleteTree(), returnp);
            }
            m_numStmts = 0;
        }
    }
};

//######################################################################
// Utility visitor to find elements to be compared

class ChangedInsertVisitor : public AstNVisitor {
private:
    // STATE
    ChangedState*       m_statep;       // Shared state across visitors
    AstVarScope*        m_vscp;         // Original (non-change) variable we're change-detecting
    AstVarScope*        m_newvscp;      // New (change detect) variable we're change-detecting
    AstNode*            m_varEqnp;      // Original var's equation to get var value
    AstNode*            m_newLvEqnp;    // New var's equation to read value
    AstNode*            m_newRvEqnp;    // New var's equation to set value
    uint32_t            m_detects;      // # detects created

    // CONSTANTS
    enum MiscConsts {
        DETECTARRAY_MAX_INDEXES = 256   // How many indexes before error
        // Ok to increase this, but may result in much slower model
    };

    void newChangeDet() {
        if (++m_detects > DETECTARRAY_MAX_INDEXES) {
            m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect more than "
                           <<cvtToStr(DETECTARRAY_MAX_INDEXES)
                           <<" array indexes (probably with UNOPTFLAT warning suppressed): "
                           <<m_vscp->prettyName()<<endl
                           <<m_vscp->warnMore()
                           <<"... Could recompile with DETECTARRAY_MAX_INDEXES increased"<<endl);
            return;
        }
        m_statep->maybeCreateChgFuncp();

        AstChangeDet* changep = new AstChangeDet(m_vscp->fileline(),
                                                 m_varEqnp->cloneTree(true),
                                                 m_newRvEqnp->cloneTree(true), false);
        m_statep->m_chgFuncp->addStmtsp(changep);
        AstAssign* initp = new AstAssign(m_vscp->fileline(),
                                         m_newLvEqnp->cloneTree(true),
                                         m_varEqnp->cloneTree(true));
        m_statep->m_chgFuncp->addFinalsp(initp);
        EmitCBaseCounterVisitor visitor(initp);
        m_statep->m_numStmts += visitor.count();
    }

    virtual void visit(AstBasicDType* nodep) VL_OVERRIDE {
        newChangeDet();
    }
    virtual void visit(AstPackArrayDType* nodep) VL_OVERRIDE {
        newChangeDet();
    }
    virtual void visit(AstUnpackArrayDType* nodep) VL_OVERRIDE {
        for (int index=0; index < nodep->elementsConst(); ++index) {
            AstNode* origVEp = m_varEqnp;
            AstNode* origNLEp = m_newLvEqnp;
            AstNode* origNREp = m_newRvEqnp;

            m_varEqnp   = new AstArraySel(nodep->fileline(), m_varEqnp->cloneTree(true), index);
            m_newLvEqnp = new AstArraySel(nodep->fileline(), m_newLvEqnp->cloneTree(true), index);
            m_newRvEqnp = new AstArraySel(nodep->fileline(), m_newRvEqnp->cloneTree(true), index);

            iterate(nodep->subDTypep()->skipRefp());

            m_varEqnp->deleteTree();
            m_newLvEqnp->deleteTree();
            m_newRvEqnp->deleteTree();

            m_varEqnp   = origVEp;
            m_newLvEqnp = origNLEp;
            m_newRvEqnp = origNREp;
        }
    }
    virtual void visit(AstNodeUOrStructDType* nodep) VL_OVERRIDE {
        if (nodep->packedUnsup()) {
            newChangeDet();
        } else {
            if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-class-");
            m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                           " (probably with UNOPTFLAT warning suppressed): "
                           <<m_vscp->varp()->prettyNameQ());
        }
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-general-");
        m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                       " (probably with UNOPTFLAT warning suppressed): "
                       <<m_vscp->varp()->prettyNameQ());
    }
public:
    // CONSTRUCTORS
    ChangedInsertVisitor(AstVarScope* vscp, ChangedState* statep) {
        m_statep = statep;
        m_vscp = vscp;
        m_detects = 0;
        {
            AstVar* varp = m_vscp->varp();
            string newvarname = ("__Vchglast__"+m_vscp->scopep()->nameDotless()
                                 +"__"+varp->shortName());
            // Create:  VARREF(_last)
            //          ASSIGN(VARREF(_last), VARREF(var))
            //          ...
            //          CHANGEDET(VARREF(_last), VARREF(var))
            AstVar* newvarp = new AstVar(varp->fileline(), AstVarType::MODULETEMP,
                                         newvarname, varp);
            m_statep->m_topModp->addStmtp(newvarp);
            m_newvscp = new AstVarScope(m_vscp->fileline(), m_statep->m_scopetopp, newvarp);
            m_statep->m_scopetopp->addVarp(m_newvscp);

            m_varEqnp   = new AstVarRef(m_vscp->fileline(), m_vscp, false);
            m_newLvEqnp = new AstVarRef(m_vscp->fileline(), m_newvscp, true);
            m_newRvEqnp = new AstVarRef(m_vscp->fileline(), m_newvscp, false);
        }
        iterate(vscp->dtypep()->skipRefp());
        m_varEqnp->deleteTree();
        m_newLvEqnp->deleteTree();
        m_newRvEqnp->deleteTree();
    }
    virtual ~ChangedInsertVisitor() {}
    VL_UNCOPYABLE(ChangedInsertVisitor);
};

//######################################################################
// Changed state, as a visitor of each AstNode

class ChangedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstVarScope::user1()            -> bool.  True indicates processed
    AstUser1InUse       m_inuser1;

    // STATE
    ChangedState*       m_statep;       // Shared state across visitors

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void genChangeDet(AstVarScope* vscp) {
        vscp->v3warn(IMPERFECTSCH, "Imperfect scheduling of variable: "<<vscp->prettyNameQ());
        ChangedInsertVisitor visitor (vscp, m_statep);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UINFO(4," MOD   "<<nodep<<endl);
        if (nodep->isTop()) {
            m_statep->m_topModp = nodep;
        }
        iterateChildren(nodep);
    }

    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        UINFO(4," TS "<<nodep<<endl);
        // Clearing
        AstNode::user1ClearTree();
        // Create the change detection function
        AstScope* scopep = nodep->scopep();
        UASSERT_OBJ(scopep, nodep,
                    "No scope found on top level, perhaps you have no statements?");
        m_statep->m_scopetopp = scopep;

        // Create a wrapper change detection function that calls each change detection function
        m_statep->m_tlChgFuncp = new AstCFunc(nodep->fileline(),
                                              "_change_request", scopep, "QData");
        m_statep->m_tlChgFuncp->argTypes(EmitCBaseVisitor::symClassVar());
        m_statep->m_tlChgFuncp->symProlog(true);
        m_statep->m_tlChgFuncp->declPrivate(true);
        m_statep->m_scopetopp->addActivep(m_statep->m_tlChgFuncp);
        // Each change detection function needs at least one AstChangeDet
        // to ensure that V3EmitC outputs the necessary code.
        m_statep->maybeCreateChgFuncp();
        m_statep->m_chgFuncp->addStmtsp(new AstChangeDet(nodep->fileline(), NULL, NULL, false));

        iterateChildren(nodep);
    }
    virtual void visit(AstVarScope* nodep) VL_OVERRIDE {
        if (nodep->isCircular()) {
            UINFO(8,"  CIRC "<<nodep<<endl);
            if (!nodep->user1SetOnce()) {
                genChangeDet(nodep);
            }
        }
    }
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {
        // Short-circuit
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    ChangedVisitor(AstNetlist* nodep, ChangedState* statep) {
        m_statep = statep;
        iterate(nodep);
    }
    virtual ~ChangedVisitor() {}
};

//######################################################################
// Changed class functions

void V3Changed::changedAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ChangedState state;
        ChangedVisitor visitor (nodep, &state);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("changed", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
