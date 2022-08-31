// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Removal of named begin blocks
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
// V3Begin's Transformations:
//
// Each module:
//      Look for BEGINs
//          BEGIN(VAR...) -> VAR ... {renamed}
//      FOR -> WHILEs
//
// There are two scopes; named BEGINs change %m and variable scopes.
// Unnamed BEGINs change only variable, not $display("%m") scope.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Begin.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>

//######################################################################

class BeginState final {
private:
    // NODE STATE
    // Entire netlist:
    // AstNodeFTask::user1      -> bool, 1=processed
    const VNUser1InUse m_inuser1;
    bool m_anyFuncInBegin = false;

public:
    BeginState() = default;
    ~BeginState() = default;
    void userMarkChanged(AstNode* nodep) {
        nodep->user1(true);
        m_anyFuncInBegin = true;
    }
    bool anyFuncInBegin() const { return m_anyFuncInBegin; }
};

//######################################################################

class BeginVisitor final : public VNVisitor {
private:
    // STATE
    BeginState* const m_statep;  // Current global state
    AstNodeModule* m_modp = nullptr;  // Current module
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNode* m_liftedp = nullptr;  // Local  nodes we are lifting into m_ftaskp
    string m_displayScope;  // Name of %m in $display/AstScopeName
    string m_namedScope;  // Name of begin blocks above us
    string m_unnamedScope;  // Name of begin blocks, including unnamed blocks
    int m_ifDepth = 0;  // Current if depth

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    string dot(const string& a, const string& b) {
        if (a == "") return b;
        return a + "__DOT__" + b;
    }

    void dotNames(const AstNodeBlock* const nodep, const char* const blockName) {
        UINFO(8, "nname " << m_namedScope << endl);
        if (nodep->name() != "") {  // Else unneeded unnamed block
            // Create data for dotted variable resolution
            string dottedname = nodep->name() + "__DOT__";  // So always found
            string::size_type pos;
            while ((pos = dottedname.find("__DOT__")) != string::npos) {
                const string ident = dottedname.substr(0, pos);
                dottedname = dottedname.substr(pos + strlen("__DOT__"));
                if (nodep->name() != "") {
                    m_displayScope = dot(m_displayScope, ident);
                    m_namedScope = dot(m_namedScope, ident);
                }
                m_unnamedScope = dot(m_unnamedScope, ident);
                // Create CellInline for dotted var resolution
                if (!m_ftaskp) {
                    AstCellInline* const inlinep = new AstCellInline(
                        nodep->fileline(), m_unnamedScope, blockName, m_modp->timeunit());
                    m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
                }
            }
        }

        // Remap var names and replace lower Begins
        iterateAndNextNull(nodep->stmtsp());
    }

    void liftNode(AstNode* nodep) {
        nodep->unlinkFrBack();
        if (m_ftaskp) {
            // AstBegin under ftask, just move into the ftask
            if (!m_liftedp) {
                m_liftedp = nodep;
            } else {
                m_liftedp->addNext(nodep);
            }
        } else {
            // Move to module
            m_modp->addStmtp(nodep);
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        UINFO(8, "  " << nodep << endl);
        // Rename it
        if (m_unnamedScope != "") {
            nodep->name(dot(m_unnamedScope, nodep->name()));
            UINFO(8, "     rename to " << nodep->name() << endl);
            m_statep->userMarkChanged(nodep);
        }
        // BEGIN wrapping a function rename that function, but don't affect
        // the inside function's variables.  We then restart with empty
        // naming; so that any begin's inside the function will rename
        // inside the function.
        // Process children
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        {
            m_displayScope = dot(m_displayScope, nodep->name());
            m_namedScope = "";
            m_unnamedScope = "";
            m_ftaskp = nodep;
            m_liftedp = nullptr;
            iterateChildren(nodep);
            if (m_liftedp) {
                // Place lifted nodes at beginning of stmtsp, so Var nodes appear before referenced
                if (AstNode* const stmtsp = nodep->stmtsp()) {
                    stmtsp->unlinkFrBackWithNext();
                    m_liftedp->addNext(stmtsp);
                }
                nodep->addStmtsp(m_liftedp);
                m_liftedp = nullptr;
            }
            m_ftaskp = nullptr;
        }
    }
    virtual void visit(AstBegin* nodep) override {
        // Begin blocks were only useful in variable creation, change names and delete
        UINFO(8, "  " << nodep << endl);
        VL_RESTORER(m_displayScope);
        VL_RESTORER(m_namedScope);
        VL_RESTORER(m_unnamedScope);
        {
            dotNames(nodep, "__BEGIN__");

            UASSERT_OBJ(!nodep->genforp(), nodep, "GENFORs should have been expanded earlier");

            // Cleanup
            AstNode* addsp = nullptr;
            if (AstNode* const stmtsp = nodep->stmtsp()) {
                stmtsp->unlinkFrBackWithNext();
                if (addsp) {
                    addsp = addsp->addNextNull(stmtsp);
                } else {
                    addsp = stmtsp;
                }
            }
            if (addsp) {
                nodep->replaceWith(addsp);
            } else {
                nodep->unlinkFrBack();
            }
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    virtual void visit(AstVar* nodep) override {
        if (m_unnamedScope != "") {
            // Rename it
            nodep->name(dot(m_unnamedScope, nodep->name()));
            m_statep->userMarkChanged(nodep);
            // Move it under enclosing tree
            liftNode(nodep);
        }
    }
    virtual void visit(AstTypedef* nodep) override {
        if (m_unnamedScope != "") {
            // Rename it
            nodep->name(dot(m_unnamedScope, nodep->name()));
            m_statep->userMarkChanged(nodep);
            // Move it under enclosing tree
            liftNode(nodep);
        }
    }
    virtual void visit(AstCell* nodep) override {
        UINFO(8, "   CELL " << nodep << endl);
        if (m_namedScope != "") {
            m_statep->userMarkChanged(nodep);
            // Rename it
            nodep->name(dot(m_namedScope, nodep->name()));
            UINFO(8, "     rename to " << nodep->name() << endl);
            // Move to module
            nodep->unlinkFrBack();
            m_modp->addStmtp(nodep);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstVarXRef* nodep) override {
        UINFO(9, "   VARXREF " << nodep << endl);
        if (m_namedScope != "" && nodep->inlinedDots() == "" && !m_ftaskp) {
            nodep->inlinedDots(m_namedScope);
            UINFO(9, "    rescope to " << nodep << endl);
        }
    }
    virtual void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Inline
        if (nodep->user1SetOnce()) return;  // Don't double-add text's
        // DPI svGetScope doesn't include function name, but %m does
        const string scname = nodep->forFormat() ? m_displayScope : m_namedScope;
        if (!scname.empty()) {
            // To keep correct visual order, must add before other Text's
            AstNode* const afterp = nodep->scopeAttrp();
            if (afterp) afterp->unlinkFrBackWithNext();
            nodep->scopeAttrp(new AstText{nodep->fileline(), string("__DOT__") + scname});
            if (afterp) nodep->scopeAttrp(afterp);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) override {
        // Don't need to fix path in coverage statements, they're not under
        // any BEGINs, but V3Coverage adds them all under the module itself.
        iterateChildren(nodep);
    }
    // VISITORS - LINT CHECK
    virtual void visit(AstIf* nodep) override {  // not AstNodeIf; other types not covered
        // Check IFDEPTH warning - could be in other transform files if desire
        VL_RESTORER(m_ifDepth);
        if (m_ifDepth == -1 || v3Global.opt.ifDepth() < 1) {  // Turned off
        } else if (nodep->uniquePragma() || nodep->unique0Pragma() || nodep->priorityPragma()) {
            m_ifDepth = -1;
        } else if (++m_ifDepth > v3Global.opt.ifDepth()) {
            nodep->v3warn(IFDEPTH,
                          "Deep 'if' statement; suggest unique/priority to avoid slow logic");
            nodep->fileline()->modifyWarnOff(V3ErrorCode::IFDEPTH, true);  // Warn only once
            m_ifDepth = -1;
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    BeginVisitor(AstNetlist* nodep, BeginState* statep)
        : m_statep{statep} {
        iterate(nodep);
    }
    virtual ~BeginVisitor() override = default;
};

//######################################################################

class BeginRelinkVisitor final : public VNVisitor {
    // Replace tasks with new pointer
private:
    // NODE STATE
    //  Input:
    //   AstNodeFTask::user1p           // Node replaced, rename it

    // VISITORS
    virtual void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->taskp()->user1()) {  // It was converted
            UINFO(9, "    relinkFTask " << nodep << endl);
            nodep->name(nodep->taskp()->name());
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varp()->user1()) {  // It was converted
            UINFO(9, "    relinVarRef " << nodep << endl);
            nodep->name(nodep->varp()->name());
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstIfaceRefDType* nodep) override {
        // May have changed cell names
        // TypeTable is always after all modules, so names are stable
        UINFO(8, "   IFACEREFDTYPE " << nodep << endl);
        if (nodep->cellp()) nodep->cellName(nodep->cellp()->name());
        UINFO(8, "       rename to " << nodep << endl);
        iterateChildren(nodep);
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    BeginRelinkVisitor(AstNetlist* nodep, BeginState*) { iterate(nodep); }
    virtual ~BeginRelinkVisitor() override = default;
};

//######################################################################
// Task class functions

void V3Begin::debeginAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        BeginState state;
        { BeginVisitor{nodep, &state}; }
        if (state.anyFuncInBegin()) { BeginRelinkVisitor{nodep, &state}; }
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("begin", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
