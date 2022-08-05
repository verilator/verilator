// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Convert BLOCKTEMPs to local variables
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
// LOCALIZE TRANSFORMATIONS:
//      All modules:
//          VARSCOPE(BLOCKTEMP...
//             if only referenced in one CFUNC, make it local
//          VARSCOPE
//             if non-public, always written before used, make it local
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Localize.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <vector>

//######################################################################
// LocalizeVisitor

class LocalizeVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstVarScope::user1()    ->  Bool indicating VarScope is not optimizable.
    //  AstCFunc::user1()       ->  Bool indicating CFunc is not a leaf function.
    //  AstVarScope::user2()    ->  Bool indicating VarScope was fully assigned in the current
    //                              function.
    //  AstVarScope::user3p()   ->  Set of CFuncs referencing this VarScope. (via m_accessors)
    //  AstCFunc::user4p()      ->  Multimap of 'VarScope -> VarRefs that reference that VarScope'
    //                              in this function. (via m_references)
    const VNUser1InUse m_user1InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;

    AstUser3Allocator<AstVarScope, std::unordered_set<AstCFunc*>> m_accessors;
    AstUser4Allocator<AstCFunc, std::unordered_multimap<const AstVarScope*, AstVarRef*>>
        m_references;

    // STATE
    VDouble0 m_statLocVars;  // Statistic tracking
    AstCFunc* m_cfuncp = nullptr;  // Current active function
    uint32_t m_nodeDepth = 0;  // Node depth under m_cfuncp
    std::vector<AstVarScope*> m_varScopeps;  // List of variables to consider for localization

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool isOptimizable(AstVarScope* nodep) {
        return !nodep->user1() ||  // Not marked as not optimizable, or ...
               (nodep->varp()->varType() == VVarType::BLOCKTEMP
                && m_accessors(nodep).size() == 1);  // .. a block temp used in a single CFunc
    }

    static bool existsNonLeaf(const std::unordered_set<AstCFunc*>& funcps) {
        for (const AstCFunc* const funcp : funcps) {
            if (funcp->user1()) return true;
        }
        return false;
    }

    void moveVarScopes() {
        for (AstVarScope* const nodep : m_varScopeps) {
            if (!isOptimizable(nodep)) continue;  // Not optimizable

            const std::unordered_set<AstCFunc*>& funcps = m_accessors(nodep);
            if (funcps.empty()) continue;  // No referencing functions at all

            // If more than one referencing function, but not all are leaf
            // functions, then don't localize, as one of the referencing
            // functions might be calling another, which the current analysis
            // cannot cope with. This should be rare (introduced by V3Depth).
            if (funcps.size() > 1 && existsNonLeaf(funcps)) continue;

            UINFO(4, "Localizing " << nodep << endl);
            ++m_statLocVars;

            // Yank the VarScope from it's parent and schedule them for deletion. Leave the Var
            // for now, as not all VarScopes referencing this Var might be localized.
            pushDeletep(nodep->unlinkFrBack());

            // In each referencing function, create a replacement local variable
            AstVar* const oldVarp = nodep->varp();
            for (AstCFunc* const funcp : funcps) {
                // Create the new local variable.
                const string newName
                    = nodep->scopep() == funcp->scopep()
                          ? oldVarp->name()
                          : nodep->scopep()->nameDotless() + "__DOT__" + oldVarp->name();
                AstVar* const newVarp
                    = new AstVar(oldVarp->fileline(), oldVarp->varType(), newName, oldVarp);
                newVarp->funcLocal(true);
                funcp->addInitsp(newVarp);

                // Fix up all the references within this function
                const auto er = m_references(funcp).equal_range(nodep);
                for (auto it = er.first; it != er.second; ++it) {
                    AstVarRef* const refp = it->second;
                    refp->varScopep(nullptr);
                    refp->varp(newVarp);
                }
            }
        }
        m_varScopeps.clear();
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        iterateChildrenConst(nodep);
        moveVarScopes();
    }

    virtual void visit(AstCFunc* nodep) override {
        UINFO(4, "  CFUNC " << nodep << endl);
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_nodeDepth);
        {
            m_cfuncp = nodep;
            m_nodeDepth = 0;
            const VNUser2InUse user2InUse;
            iterateChildrenConst(nodep);
        }
    }

    virtual void visit(AstCCall* nodep) override {
        m_cfuncp->user1(true);  // Mark caller as not a leaf function
        iterateChildrenConst(nodep);
    }

    virtual void visit(AstNodeAssign* nodep) override {
        // Analyze RHS first so "a = a + 1" is detected as a read before write
        iterate(nodep->rhsp());
        // For now we only consider an assignment that is directly under the function, (in
        // particular: not under an AstIf, or other kind of branch). This could be improved with
        // proper data flow analysis.
        if (m_nodeDepth == 0) {
            // Check if simple "VARREF = ..." assignment, i.e.: this assignment sets the whole
            // variable (and in particular, it is not assigned only in part).
            if (const AstVarRef* const refp = VN_CAST(nodep->lhsp(), VarRef)) {
                // Mark this VarScope as assigned in this function
                refp->varScopep()->user2(1);
            }
        }
        // Analyze LHS (in case it's not the above simple case
        iterate(nodep->lhsp());
    }

    virtual void visit(AstVarScope* nodep) override {
        if (!nodep->varp()->isPrimaryIO()  // Not an IO the user wants to interact with
            && !nodep->varp()->isSigPublic()  // Not something the user wants to interact with
            && !nodep->varp()->isFuncLocal()  // Not already a function local (e.g.: argument)
            && !nodep->varp()->isStatic()  // Not a static variable
            && !nodep->varp()->isClassMember()  // Statically exists in design hierarchy
            && !nodep->varp()->valuep()  // Does not have an initializer
        ) {
            UINFO(4, "Consider for localization: " << nodep << endl);
            m_varScopeps.push_back(nodep);
        }
        // No iterate; Don't want varrefs under it (e.g.: in child dtype?)
    }

    virtual void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(m_cfuncp, nodep, "AstVarRef not under function");

        AstVarScope* const varScopep = nodep->varScopep();
        // Remember this function accesses this VarScope (we always need this as we might optimize
        // this VarScope into a local, even if it's not assigned. See 'isOptimizable')
        m_accessors(varScopep).emplace(m_cfuncp);
        // Remember the reference so we can fix it up later (we always need this as well)
        m_references(m_cfuncp).emplace(varScopep, nodep);

        // Check if already marked as not optimizable
        if (!varScopep->user1()) {
            // Note: we only check read variables, as it's ok to localize (and in fact discard)
            // any variables that are only written but never read.
            if (nodep->access().isReadOrRW() && !varScopep->user2()) {
                // Variable is read, but is not known to have been assigned in this function. Mark
                // as not optimizable.
                UINFO(4, "Not optimizable (not written): " << nodep << endl);
                varScopep->user1(1);
            }
        }
        // No iterate; Don't want varrefs under it  (e.g.: in child dtype?)
    }

    virtual void visit(AstNode* nodep) override {
        ++m_nodeDepth;
        iterateChildrenConst(nodep);
        --m_nodeDepth;
    }

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
    { LocalizeVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("localize", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
