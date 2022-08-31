// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for changed nodes
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

#include "V3Changed.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>

//######################################################################

class ChangedState final {
public:
    // STATE
    AstNodeModule* m_topModp = nullptr;  // Top module
    AstScope* m_scopetopp = nullptr;  // Scope under TOPSCOPE
    AstCFunc* m_chgFuncp = nullptr;  // Change function we're building
    AstCFunc* m_tlChgFuncp = nullptr;  // Top level change function we're building
    int m_numStmts = 0;  // Number of statements added to m_chgFuncp
    int m_funcNum = 0;  // Number of change functions emitted
    bool m_madeTopChg = false;

    ChangedState() = default;
    ~ChangedState() = default;

    void maybeCreateChgFuncp() {
        maybeCreateTopChg();
        maybeCreateMidChg();
    }
    void maybeCreateTopChg() {
        if (m_madeTopChg) return;
        m_madeTopChg = true;
        v3Global.rootp()->changeRequest(true);

        // Create a wrapper change detection function that calls each change detection function
        m_tlChgFuncp
            = new AstCFunc{m_scopetopp->fileline(), "_change_request", m_scopetopp, "QData"};
        m_tlChgFuncp->isStatic(false);
        m_tlChgFuncp->isLoose(true);
        m_tlChgFuncp->declPrivate(true);
        m_scopetopp->addActivep(m_tlChgFuncp);
        // Each change detection function needs at least one AstChangeDet
        // to ensure that V3EmitC outputs the necessary code.
        maybeCreateMidChg();
        m_chgFuncp->addStmtsp(new AstChangeDet{m_scopetopp->fileline(), nullptr, nullptr});
    }
    void maybeCreateMidChg() {
        // Don't create an extra function call if splitting is disabled
        if (!v3Global.opt.outputSplitCFuncs()) {
            m_chgFuncp = m_tlChgFuncp;
            return;
        }
        if (!m_chgFuncp || v3Global.opt.outputSplitCFuncs() < m_numStmts) {
            m_chgFuncp
                = new AstCFunc{m_scopetopp->fileline(), "_change_request_" + cvtToStr(++m_funcNum),
                               m_scopetopp, "QData"};
            m_chgFuncp->isStatic(false);
            m_chgFuncp->isLoose(true);
            m_chgFuncp->declPrivate(true);
            m_scopetopp->addActivep(m_chgFuncp);

            // Add a top call to it
            AstCCall* const callp = new AstCCall{m_scopetopp->fileline(), m_chgFuncp};

            if (!m_tlChgFuncp->stmtsp()) {
                m_tlChgFuncp->addStmtsp(new AstCReturn{m_scopetopp->fileline(), callp});
            } else {
                AstCReturn* const returnp = VN_AS(m_tlChgFuncp->stmtsp(), CReturn);
                UASSERT_OBJ(returnp, m_scopetopp, "Lost CReturn in top change function");
                // This is currently using AstLogOr which will shortcut the
                // evaluation if any function returns true. This is likely what
                // we want and is similar to the logic already in use inside
                // V3EmitC, however, it also means that verbose logging may
                // miss to print change detect variables.
                AstNode* const newp = new AstCReturn{
                    m_scopetopp->fileline(),
                    new AstLogOr{m_scopetopp->fileline(), callp, returnp->lhsp()->unlinkFrBack()}};
                returnp->replaceWith(newp);
                VL_DO_DANGLING(returnp->deleteTree(), returnp);
            }
            m_numStmts = 0;
        }
    }
};

//######################################################################
// Utility visitor to find elements to be compared

class ChangedInsertVisitor final : public VNVisitor {
private:
    // STATE
    ChangedState& m_state;  // Shared state across visitors
    AstVarScope* const m_vscp;  // Original (non-change) variable we're change-detecting
    AstVarScope* m_newvscp = nullptr;  // New (change detect) variable we're change-detecting
    AstNode* m_varEqnp = nullptr;  // Original var's equation to get var value
    AstNode* m_newLvEqnp = nullptr;  // New var's equation to read value
    AstNode* m_newRvEqnp = nullptr;  // New var's equation to set value
    uint32_t m_detects = 0;  // # detects created

    // CONSTANTS
    // How many indexes before error. Ok to increase this, but may result in much slower model
    static constexpr uint32_t DETECTARRAY_MAX_INDEXES = 256;

    void newChangeDet() {
        if (++m_detects > DETECTARRAY_MAX_INDEXES) {
            m_vscp->v3warn(E_DETECTARRAY,
                           "Unsupported: Can't detect more than "
                               << DETECTARRAY_MAX_INDEXES
                               << " array indexes (probably with UNOPTFLAT warning suppressed): "
                               << m_vscp->prettyName() << '\n'
                               << m_vscp->warnMore()
                               << "... Could recompile with DETECTARRAY_MAX_INDEXES increased");
            return;
        }
        m_state.maybeCreateChgFuncp();

        AstChangeDet* const changep = new AstChangeDet{
            m_vscp->fileline(), m_varEqnp->cloneTree(true), m_newRvEqnp->cloneTree(true)};
        m_state.m_chgFuncp->addStmtsp(changep);
        AstAssign* const initp = new AstAssign{m_vscp->fileline(), m_newLvEqnp->cloneTree(true),
                                               m_varEqnp->cloneTree(true)};
        m_state.m_chgFuncp->addFinalsp(initp);

        // Later code will expand words which adds to GCC compile time,
        // so add penalty based on word width also
        m_state.m_numStmts += initp->nodeCount() + m_varEqnp->widthWords();
    }

    virtual void visit(AstBasicDType*) override {  //
        newChangeDet();
    }
    virtual void visit(AstPackArrayDType*) override {  //
        newChangeDet();
    }
    virtual void visit(AstUnpackArrayDType* nodep) override {
        for (int index = 0; index < nodep->elementsConst(); ++index) {
            VL_RESTORER(m_varEqnp);
            VL_RESTORER(m_newLvEqnp);
            VL_RESTORER(m_newRvEqnp);
            {
                m_varEqnp = new AstArraySel{nodep->fileline(), m_varEqnp->cloneTree(true), index};
                m_newLvEqnp
                    = new AstArraySel{nodep->fileline(), m_newLvEqnp->cloneTree(true), index};
                m_newRvEqnp
                    = new AstArraySel{nodep->fileline(), m_newRvEqnp->cloneTree(true), index};

                iterate(nodep->subDTypep()->skipRefp());

                m_varEqnp->deleteTree();
                m_newLvEqnp->deleteTree();
                m_newRvEqnp->deleteTree();
            }
        }
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->packedUnsup()) {
            newChangeDet();
        } else {
            if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-class-");
            m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                                          " (probably with UNOPTFLAT warning suppressed): "
                                              << m_vscp->varp()->prettyNameQ());
        }
    }
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        if (debug()) nodep->dumpTree(cout, "-DETECTARRAY-general-");
        m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable"
                                      " (probably with UNOPTFLAT warning suppressed): "
                                          << m_vscp->varp()->prettyNameQ());
    }

public:
    // CONSTRUCTORS
    ChangedInsertVisitor(AstVarScope* vscp, ChangedState& state)
        : m_state{state}
        , m_vscp{vscp} {
        // DPI export trigger should never need change detect. See similar assertions in V3Order
        // (OrderVisitor::nodeMarkCircular), and V3GenClk (GenClkRenameVisitor::genInpClk).
        UASSERT_OBJ(vscp != v3Global.rootp()->dpiExportTriggerp(), vscp,
                    "DPI export trigger should not need change detect");
        {
            AstVar* const varp = m_vscp->varp();
            const string newvarname{"__Vchglast__" + m_vscp->scopep()->nameDotless() + "__"
                                    + varp->shortName()};
            // Create:  VARREF(_last)
            //          ASSIGN(VARREF(_last), VARREF(var))
            //          ...
            //          CHANGEDET(VARREF(_last), VARREF(var))
            AstVar* const newvarp
                = new AstVar{varp->fileline(), VVarType::MODULETEMP, newvarname, varp};
            m_state.m_topModp->addStmtp(newvarp);
            m_newvscp = new AstVarScope{m_vscp->fileline(), m_state.m_scopetopp, newvarp};
            m_state.m_scopetopp->addVarp(m_newvscp);

            m_varEqnp = new AstVarRef{m_vscp->fileline(), m_vscp, VAccess::READ};
            m_newLvEqnp = new AstVarRef{m_vscp->fileline(), m_newvscp, VAccess::WRITE};
            m_newRvEqnp = new AstVarRef{m_vscp->fileline(), m_newvscp, VAccess::READ};
        }
        iterate(vscp->dtypep()->skipRefp());
        m_varEqnp->deleteTree();
        m_newLvEqnp->deleteTree();
        m_newRvEqnp->deleteTree();
    }
    virtual ~ChangedInsertVisitor() override = default;
    VL_UNCOPYABLE(ChangedInsertVisitor);
};

//######################################################################
// Changed class functions

void V3Changed::changedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    ChangedState state;
    state.m_scopetopp = nodep->topScopep()->scopep();
    state.m_topModp = nodep->topModulep();
    nodep->foreach<AstVarScope>([&state](AstVarScope* vscp) {
        if (vscp->isCircular()) {
            vscp->v3warn(IMPERFECTSCH,
                         "Imperfect scheduling of variable: " << vscp->prettyNameQ());
            ChangedInsertVisitor{vscp, state};
        }
    });

    V3Global::dumpCheckGlobalTree("changed", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
