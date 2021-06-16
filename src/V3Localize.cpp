// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert BLOCKTEMPs to local variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// LOCALIZE TRANSFORMATIONS:
//      All modules:
//          VARSCOPE(BLOCKTEMP...
//             if only referenced in a CFUNC, make it local to that CFUNC
//          VARSCOPE(others
//             if non-public, set before used, and in single CFUNC, make it local
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Localize.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <vector>

//######################################################################
// LocalizeVisitor

class LocalizeVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  AstVar::user1p()        -> First AstCFunc which references the variable
    //  AstVar::user2()         -> VarFlags.  Flag state
    //  AstVar::user4p()        -> AstVarRef that writes whole variable, if first write ref.
    AstUser1InUse m_inuser1;
    AstUser2InUse m_inuser2;
    AstUser4InUse m_inuser4;

    // TYPES
    union VarFlags {
        // Per-variable flags
        // Used in user()'s so initializes to all zeros
        struct {
            int m_notOpt : 1;  // NOT optimizable
            int m_notStd : 1;  // NOT optimizable if a non-blocktemp signal
            int m_stdFuncAsn : 1;  // Found simple assignment
        };
        // cppcheck-suppress unusedStructMember
        uint32_t m_flags;
        explicit VarFlags(AstVarScope* nodep) { m_flags = nodep->user2(); }
        void setNodeFlags(AstVarScope* nodep) { nodep->user2(m_flags); }
    };

    // STATE
    VDouble0 m_statLocVars;  // Statistic tracking
    AstCFunc* m_cfuncp = nullptr;  // Current active function
    std::vector<AstVarScope*> m_varScopeps;  // List of variables to consider for localization
    std::unordered_multimap<const AstVarScope*, AstVarRef*>
        m_references;  // VarRefs referencing the given VarScope

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void clearOptimizable(AstVarScope* nodep, const char* reason) {
        UINFO(4, "       NoOpt " << reason << " " << nodep << endl);
        VarFlags flags(nodep);
        flags.m_notOpt = true;
        flags.setNodeFlags(nodep);
    }
    void clearStdOptimizable(AstVarScope* nodep, const char* reason) {
        UINFO(4, "       NoStd " << reason << " " << nodep << endl);
        VarFlags flags(nodep);
        flags.m_notStd = true;
        flags.setNodeFlags(nodep);
    }
    void moveVarScopes() {
        for (AstVarScope* const nodep : m_varScopeps) {
            if (nodep->varp()->valuep()) clearOptimizable(nodep, "HasInitValue");
            if (!VarFlags(nodep).m_stdFuncAsn) clearStdOptimizable(nodep, "NoStdAssign");
            VarFlags flags(nodep);

            if ((nodep->varp()->varType() == AstVarType::BLOCKTEMP
                 || !flags.m_notStd)  // Temporary Or used only in block
                && !flags.m_notOpt  // Optimizable
                && !nodep->varp()->isClassMember() &&  // Statically exists in design hierarchy
                nodep->user1p())  // Is under a CFunc
            {
                UINFO(4, "Localizing " << nodep << endl);
                ++m_statLocVars;
                AstCFunc* const funcp = VN_CAST(nodep->user1p(), CFunc);
                // Yank the Var and VarScope from it's parent and schedule them for deletion
                AstVar* const varp = nodep->varp();
                if (varp->backp()) {  // Might have already unlinked this via another AstVarScope
                    pushDeletep(varp->unlinkFrBack());
                }
                pushDeletep(nodep->unlinkFrBack());

                // Create the new local variable.
                const string newName
                    = nodep->scopep() == funcp->scopep()
                          ? varp->name()
                          : nodep->scopep()->nameDotless() + "__DOT__" + varp->name();

                AstVar* const newVarp
                    = new AstVar(varp->fileline(), varp->varType(), newName, varp);
                newVarp->funcLocal(true);

                // Fix up all the references
                const auto er = m_references.equal_range(nodep);
                for (auto it = er.first; it != er.second; ++it) {
                    AstVarRef* const refp = it->second;
                    refp->varScopep(nullptr);
                    refp->varp(newVarp);
                }

                // Add the var to this function, and mark local
                funcp->addInitsp(newVarp);
            } else {
                clearOptimizable(nodep, "NotDone");
            }
        }
        m_varScopeps.clear();
        m_references.clear();
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        iterateChildrenConst(nodep);
        moveVarScopes();
    }
    virtual void visit(AstCFunc* nodep) override {
        UINFO(4, "  CFUNC " << nodep << endl);
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            searchFuncStmts(nodep->argsp());
            searchFuncStmts(nodep->initsp());
            searchFuncStmts(nodep->stmtsp());
            searchFuncStmts(nodep->finalsp());
            iterateChildrenConst(nodep);
        }
    }
    void searchFuncStmts(AstNode* nodep) {
        // Search for basic assignments to allow moving non-blocktemps
        // For now we only find simple assignments not under any other statement.
        // This could be more complicated; allow always-set under both branches of a IF.
        // If so, check for ArrayRef's and such, as they aren't acceptable.
        for (; nodep; nodep = nodep->nextp()) {
            if (AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
                if (AstVarRef* const varrefp = VN_CAST(assignp->lhsp(), VarRef)) {
                    UASSERT_OBJ(varrefp->access().isWriteOrRW(), varrefp,
                                "LHS of assignment is not an lvalue");
                    AstVarScope* const varScopep = varrefp->varScopep();
                    if (!varScopep->user4p()) {
                        UINFO(4, "      FuncAsn " << varrefp << endl);
                        varScopep->user4p(varrefp);
                        VarFlags flags(varScopep);
                        flags.m_stdFuncAsn = true;
                        flags.setNodeFlags(varScopep);
                    }
                }
            }
        }
    }

    virtual void visit(AstVarScope* nodep) override {
        if (!nodep->varp()->isPrimaryIO()  // Not an IO the user wants to interact with
            && !nodep->varp()->isSigPublic()  // Not something the user wants to interact with
            && !nodep->varp()->isFuncLocal()  // Not already a function local (e.g.: argument)
            && !nodep->varp()->isStatic()  // Not a static variable
        ) {
            UINFO(4, "    BLKVAR " << nodep << endl);
            m_varScopeps.push_back(nodep);
        }
        // No iterate; Don't want varrefs under it
    }
    virtual void visit(AstVarRef* nodep) override {
        AstVarScope* const varScopep = nodep->varScopep();
        if (!VarFlags(varScopep).m_notOpt) {
            // Remember the reference
            m_references.emplace(varScopep, nodep);
            if (!m_cfuncp) {  // Not in function, can't optimize
                // Perhaps impossible, but better safe
                clearOptimizable(varScopep, "BVnofunc");  // LCOV_EXCL_LINE
            } else {
                // Allow a variable to appear in only a single function
                AstNode* const oldfunc = varScopep->user1p();
                if (!oldfunc) {
                    // First encounter with this variable
                    UINFO(4, "      BVnewref " << nodep << endl);
                    varScopep->user1p(m_cfuncp);  // Remember where it was used
                } else if (m_cfuncp != oldfunc) {
                    // Used in multiple functions
                    clearOptimizable(varScopep, "BVmultiF");
                }
                // First varref in function must be assignment found earlier
                const AstVarRef* const firstasn = VN_CAST(varScopep->user4p(), VarRef);
                if (firstasn && nodep != firstasn) {
                    clearStdOptimizable(varScopep, "notFirstAsn");
                    varScopep->user4p(nullptr);
                }
            }
        }
        // No iterate; Don't want varrefs under it
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit LocalizeVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~LocalizeVisitor() override {
        V3Stats::addStat("Optimizations, Vars localized", m_statLocVars);
    }
};

//######################################################################
// Localize class functions

void V3Localize::localizeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { LocalizeVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("localize", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
