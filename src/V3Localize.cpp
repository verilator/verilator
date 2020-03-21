// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert BLOCKTEMPs to local variables
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
// LOCALIZE TRANSFORMATIONS:
//      All modules:
//          VAR(BLOCKTEMP...
//             if only referenced in a CFUNC, make it local to that CFUNC
//          VAR(others
//             if non-public, set before used, and in single CFUNC, make it local
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Localize.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <cstdarg>
#include <vector>

//######################################################################
// Localize base class

class LocalizeBaseVisitor : public AstNVisitor {
protected:
    // NODE STATE
    // Cleared on entire tree
    //  AstVar::user1p()        -> CFunc which references the variable
    //  AstVar::user2()         -> VarFlags.  Flag state
    //  AstVar::user4()         -> AstVarRef*.  First place signal set; must be first assignment

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // TYPES
    union VarFlags {
        // Per-variable flags
        // Used in user()'s so initializes to all zeros
        struct {
            int m_notOpt:1;     // NOT optimizable
            int m_notStd:1;     // NOT optimizable if a non-blocktemp signal
            int m_stdFuncAsn:1; // Found simple assignment
            int m_done:1;       // Removed
        };
        // cppcheck-suppress unusedStructMember
        uint32_t m_flags;
        explicit VarFlags(AstNode* nodep) { m_flags = nodep->user2(); }
        void setNodeFlags(AstNode* nodep) { nodep->user2(m_flags); }
    };
};

//######################################################################
// Localize class functions

class LocalizeDehierVisitor : public LocalizeBaseVisitor {
private:
    // NODE STATE/TYPES
    // See above

    // METHODS
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        VarFlags flags (nodep->varp());
        if (flags.m_done) {
            nodep->hiername("");  // Remove this->
            nodep->hierThis(true);
        }
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit LocalizeDehierVisitor(AstNetlist* nodep) {
        iterate(nodep);
    }
    virtual ~LocalizeDehierVisitor() {}
};

//######################################################################
// Localize class functions

class LocalizeVisitor : public LocalizeBaseVisitor {
private:
    // NODE STATE/TYPES
    // See above
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;
    AstUser4InUse       m_inuser4;

    // STATE
    VDouble0 m_statLocVars;  // Statistic tracking
    AstCFunc* m_cfuncp;  // Current active function
    std::vector<AstVar*> m_varps;  // List of variables to consider for deletion

    // METHODS
    void clearOptimizable(AstVar* nodep, const char* reason) {
        UINFO(4,"       NoOpt "<<reason<<" "<<nodep<<endl);
        VarFlags flags (nodep);
        flags.m_notOpt = true;
        flags.setNodeFlags(nodep);
    }
    void clearStdOptimizable(AstVar* nodep, const char* reason) {
        UINFO(4,"       NoStd "<<reason<<" "<<nodep<<endl);
        VarFlags flags (nodep);
        flags.m_notStd = true;
        flags.setNodeFlags(nodep);
    }
    void moveVars() {
        for (std::vector<AstVar*>::iterator it = m_varps.begin(); it != m_varps.end(); ++it) {
            AstVar* nodep = *it;
            if (nodep->valuep()) clearOptimizable(nodep, "HasInitValue");
            if (!VarFlags(nodep).m_stdFuncAsn) clearStdOptimizable(nodep, "NoStdAssign");
            VarFlags flags (nodep);
            if ((nodep->isMovableToBlock()  // Blocktemp
                 || !flags.m_notStd)  // Or used only in block
                && !flags.m_notOpt  // Optimizable
                && nodep->user1p()) {  // Single cfunc
                // We don't need to test for tracing; it would be in the tracefunc if it was needed
                UINFO(4,"  ModVar->BlkVar "<<nodep<<endl);
                ++m_statLocVars;
                AstCFunc* newfuncp = VN_CAST(nodep->user1p(), CFunc);
                nodep->unlinkFrBack();
                newfuncp->addInitsp(nodep);
                // Done
                flags.m_done = true;
                flags.setNodeFlags(nodep);
            } else {
                clearOptimizable(nodep, "NotDone");
            }
        }
        m_varps.clear();
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        moveVars();
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        UINFO(4,"  CFUNC "<<nodep<<endl);
        m_cfuncp = nodep;
        searchFuncStmts(nodep->argsp());
        searchFuncStmts(nodep->initsp());
        searchFuncStmts(nodep->stmtsp());
        searchFuncStmts(nodep->finalsp());
        iterateChildren(nodep);
        m_cfuncp = NULL;
    }
    void searchFuncStmts(AstNode* nodep) {
        // Search for basic assignments to allow moving non-blocktemps
        // For now we only find simple assignments not under any other statement.
        // This could be more complicated; allow always-set under both branches of a IF.
        // If so, check for ArrayRef's and such, as they aren't acceptable.
        for (; nodep; nodep=nodep->nextp()) {
            if (VN_IS(nodep, NodeAssign)) {
                if (AstVarRef* varrefp = VN_CAST(VN_CAST(nodep, NodeAssign)->lhsp(), VarRef)) {
                    UASSERT_OBJ(varrefp->lvalue(), varrefp, "LHS assignment not lvalue");
                    if (!varrefp->varp()->user4p()) {
                        UINFO(4,"      FuncAsn "<<varrefp<<endl);
                        varrefp->varp()->user4p(varrefp);
                        VarFlags flags (varrefp->varp());
                        flags.m_stdFuncAsn = true;
                        flags.setNodeFlags(varrefp->varp());
                    }
                }
            }
        }
    }

    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (!nodep->isSigPublic()
            && !nodep->isPrimaryIO()
            && !m_cfuncp) {  // Not already inside a function
            UINFO(4,"    BLKVAR "<<nodep<<endl);
            m_varps.push_back(nodep);
        }
        // No iterate; Don't want varrefs under it
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (!VarFlags(nodep->varp()).m_notOpt) {
            if (!m_cfuncp) {  // Not in function, can't optimize
                clearOptimizable(nodep->varp(), "BVnofunc");
            }
            else {
                // If we're scoping down to it, it isn't really in the same block
                if (!nodep->hierThis()) clearOptimizable(nodep->varp(), "HierRef");
                // Allow a variable to appear in only a single function
                AstNode* oldfunc = nodep->varp()->user1p();
                if (!oldfunc) {
                    UINFO(4,"      BVnewref "<<nodep<<endl);
                    nodep->varp()->user1p(m_cfuncp);  // Remember where it was used
                } else if (m_cfuncp == oldfunc) {
                    // Same usage
                } else {
                    // Used in multiple functions
                    clearOptimizable(nodep->varp(), "BVmultiF");
                }
                // First varref in function must be assignment found earlier
                AstVarRef* firstasn = static_cast<AstVarRef*>(nodep->varp()->user4p());
                if (firstasn && nodep!=firstasn) {
                    clearStdOptimizable(nodep->varp(), "notFirstAsn");
                    nodep->varp()->user4p(NULL);
                }
            }
        }
        // No iterate; Don't want varrefs under it
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit LocalizeVisitor(AstNetlist* nodep) {
        m_cfuncp = NULL;
        iterate(nodep);
    }
    virtual ~LocalizeVisitor() {
        V3Stats::addStat("Optimizations, Vars localized", m_statLocVars);
    }
};

//######################################################################
// Localize class functions

void V3Localize::localizeAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        LocalizeVisitor visitor (nodep);
        // Fix up hiernames
        LocalizeDehierVisitor dvisitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("localize", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
