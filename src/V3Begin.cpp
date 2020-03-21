// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Removal of named begin blocks
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

#include "V3Global.h"
#include "V3Begin.h"
#include "V3Inst.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <vector>

//######################################################################

class BeginState {
private:
    // NODE STATE
    //Entire netlist:
    // AstNodeFTask::user1      -> bool, 1=processed
    AstUser1InUse       m_inuser1;
    bool                m_anyFuncInBegin;
public:
    BeginState() {
        m_anyFuncInBegin = false;
    }
    ~BeginState() {}
    void userMarkChanged(AstNode* nodep) {
        nodep->user1(true);
        m_anyFuncInBegin = true;
    }
    bool anyFuncInBegin() const { return m_anyFuncInBegin; }
};

//######################################################################

class BeginVisitor : public AstNVisitor {
private:
    // STATE
    BeginState*         m_statep;       // Current global state
    AstNodeModule*      m_modp;         // Current module
    AstNodeFTask*       m_ftaskp;       // Current function/task
    string              m_namedScope;   // Name of begin blocks above us
    string              m_unnamedScope; // Name of begin blocks, including unnamed blocks
    int                 m_ifDepth;      // Current if depth

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        UINFO(8,"  "<<nodep<<endl);
        // Rename it
        if (m_unnamedScope != "") {
            nodep->name(m_unnamedScope+"__DOT__"+nodep->name());
            UINFO(8,"     rename to "<<nodep->name()<<endl);
            m_statep->userMarkChanged(nodep);
        }
        // BEGIN wrapping a function rename that function, but don't affect
        // the inside function's variables.  We then restart with empty
        // naming; so that any begin's inside the function will rename
        // inside the function.
        // Process children
        string oldScope = m_namedScope;
        string oldUnnamed = m_unnamedScope;
        {
            m_namedScope = "";
            m_unnamedScope = "";
            m_ftaskp = nodep;
            iterateChildren(nodep);
            m_ftaskp = NULL;
        }
        m_namedScope = oldScope;
        m_unnamedScope = oldUnnamed;
    }
    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        // Begin blocks were only useful in variable creation, change names and delete
        UINFO(8,"  "<<nodep<<endl);
        string oldScope = m_namedScope;
        string oldUnnamed = m_unnamedScope;
        {
            UINFO(8,"nname "<<m_namedScope<<endl);
            if (nodep->name() != "") {  // Else unneeded unnamed block
                // Create data for dotted variable resolution
                string dottedname = nodep->name() + "__DOT__";  // So always found
                string::size_type pos;
                while ((pos=dottedname.find("__DOT__")) != string::npos) {
                    string ident = dottedname.substr(0, pos);
                    dottedname = dottedname.substr(pos+strlen("__DOT__"));
                    if (nodep->name() != "") {
                        if (m_namedScope=="") m_namedScope = ident;
                        else m_namedScope = m_namedScope + "__DOT__"+ident;
                    }
                    if (m_unnamedScope=="") m_unnamedScope = ident;
                    else m_unnamedScope = m_unnamedScope + "__DOT__"+ident;
                    // Create CellInline for dotted var resolution
                    if (!m_ftaskp) {
                        AstCellInline* inlinep = new AstCellInline(nodep->fileline(),
                                                                   m_unnamedScope, "__BEGIN__");
                        m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
                    }
                }
            }

            // Remap var names and replace lower Begins
            iterateAndNextNull(nodep->stmtsp());
            UASSERT_OBJ(!nodep->genforp(), nodep, "GENFORs should have been expanded earlier");
        }
        m_namedScope = oldScope;
        m_unnamedScope = oldUnnamed;

        // Cleanup
        AstNode* addsp = NULL;
        if (AstNode* stmtsp = nodep->stmtsp()) {
            stmtsp->unlinkFrBackWithNext();
            if (addsp) { addsp = addsp->addNextNull(stmtsp); } else { addsp = stmtsp; }
        }
        if (addsp) {
            nodep->replaceWith(addsp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (m_unnamedScope != "") {
            // Rename it
            nodep->name(m_unnamedScope+"__DOT__"+nodep->name());
            m_statep->userMarkChanged(nodep);
            // Move to module
            nodep->unlinkFrBack();
            if (m_ftaskp) m_ftaskp->addStmtsp(nodep);  // Begins under funcs just move into the func
            else m_modp->addStmtp(nodep);
        }
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        UINFO(8,"   CELL "<<nodep<<endl);
        if (m_namedScope != "") {
            m_statep->userMarkChanged(nodep);
            // Rename it
            nodep->name(m_namedScope+"__DOT__"+nodep->name());
            UINFO(8,"     rename to "<<nodep->name()<<endl);
            // Move to module
            nodep->unlinkFrBack();
            m_modp->addStmtp(nodep);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstVarXRef* nodep) VL_OVERRIDE {
        UINFO(9, "   VARXREF "<<nodep<<endl);
        if (m_namedScope != "" && nodep->inlinedDots() == "") {
            nodep->inlinedDots(m_namedScope);
            UINFO(9, "    rescope to "<<nodep<<endl);
        }
    }
    virtual void visit(AstScopeName* nodep) VL_OVERRIDE {
        // If there's a %m in the display text, we add a special node that will contain the name()
        // Similar code in V3Inline
        if (nodep->user1SetOnce()) return;  // Don't double-add text's
        if (m_namedScope != "") {
            // To keep correct visual order, must add before other Text's
            AstNode* afterp = nodep->scopeAttrp();
            if (afterp) afterp->unlinkFrBackWithNext();
            nodep->scopeAttrp(new AstText(nodep->fileline(), string("__DOT__")+m_namedScope));
            if (afterp) nodep->scopeAttrp(afterp);
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstCoverDecl* nodep) VL_OVERRIDE {
        // Don't need to fix path in coverage statements, they're not under
        // any BEGINs, but V3Coverage adds them all under the module itself.
        iterateChildren(nodep);
    }
    // VISITORS - LINT CHECK
    virtual void visit(AstIf* nodep) VL_OVERRIDE {  // Note not AstNodeIf; other types don't get covered
        // Check IFDEPTH warning - could be in other transform files if desire
        int prevIfDepth = m_ifDepth;
        if (m_ifDepth == -1 || v3Global.opt.ifDepth()<1) {  // Turned off
        } else if (nodep->uniquePragma() || nodep->unique0Pragma() || nodep->priorityPragma()) {
            m_ifDepth = -1;
        } else if (++m_ifDepth > v3Global.opt.ifDepth()) {
            nodep->v3warn(IFDEPTH,"Deep 'if' statement; suggest unique/priority to avoid slow logic");
            nodep->fileline()->modifyWarnOff(V3ErrorCode::IFDEPTH, true);  // Warn only once
            m_ifDepth = -1;
        }
        iterateChildren(nodep);
        m_ifDepth = prevIfDepth;
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    BeginVisitor(AstNetlist* nodep, BeginState* statep) {
        m_statep = statep;
        m_modp = NULL;
        m_ftaskp = NULL;
        m_ifDepth = 0;
        iterate(nodep);
    }
    virtual ~BeginVisitor() {}
};

//######################################################################

class BeginRelinkVisitor : public AstNVisitor {
    // Replace tasks with new pointer
private:
    // NODE STATE
    //  Input:
    //   AstNodeFTask::user1p           // Node replaced, rename it

    // VISITORS
    virtual void visit(AstNodeFTaskRef* nodep) VL_OVERRIDE {
        if (nodep->taskp()->user1()) {  // It was converted
            UINFO(9, "    relinkFTask "<<nodep<<endl);
            nodep->name(nodep->taskp()->name());
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (nodep->varp()->user1()) {  // It was converted
            UINFO(9, "    relinVarRef "<<nodep<<endl);
            nodep->name(nodep->varp()->name());
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstIfaceRefDType* nodep) VL_OVERRIDE {
        // May have changed cell names
        // TypeTable is always after all modules, so names are stable
        UINFO(8,"   IFACEREFDTYPE "<<nodep<<endl);
        if (nodep->cellp()) nodep->cellName(nodep->cellp()->name());
        UINFO(8,"       rename to "<<nodep<<endl);
        iterateChildren(nodep);
    }
    //--------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    BeginRelinkVisitor(AstNetlist* nodep, BeginState*) {
        iterate(nodep);
    }
    virtual ~BeginRelinkVisitor() {}
};

//######################################################################
// Task class functions

void V3Begin::debeginAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        BeginState state;
        { BeginVisitor bvisitor (nodep,&state); }
        if (state.anyFuncInBegin()) {
            BeginRelinkVisitor brvisitor (nodep,&state);
        }
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("begin", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
