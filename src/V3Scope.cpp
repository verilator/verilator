// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Scope's Transformations:
//
//      For every CELL that references this module, create a
//              SCOPE
//                      {all blocked statements}
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Scope.h"

#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Scope class functions

class ScopeVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user1p           -> AstVarScope replacement for this variable
    // AstCell::user2p          -> AstScope*.  The scope created inside the cell
    // AstTask::user2p          -> AstTask*.  Replacement task
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // TYPES
    // These cannot be unordered unless make a specialized hashing pair (gcc-8)
    using VarScopeMap = std::map<std::pair<AstVar*, AstScope*>, AstVarScope*>;

    // STATE, inside processing a single module
    AstNodeModule* m_modp = nullptr;  // Current module
    AstScope* m_scopep = nullptr;  // Current scope we are building
    // STATE, for passing down one level of hierarchy (may need save/restore)
    AstCell* m_aboveCellp = nullptr;  // Cell that instantiates this module
    AstScope* m_aboveScopep = nullptr;  // Scope that instantiates this scope
    AstClocking* m_clockingp = nullptr;  // Current clocking block

    std::unordered_map<AstNodeModule*, AstScope*> m_packageScopes;  // Scopes for each package
    VarScopeMap m_varScopes;  // Varscopes created for each scope and var
    std::set<std::pair<AstVarRef*, AstScope*>>
        m_varRefScopes;  // Varrefs-in-scopes needing fixup when done

    // METHODS

    void cleanupVarRefs() {
        for (const auto& itr : m_varRefScopes) {
            AstVarRef* const nodep = itr.first;
            AstScope* scopep = itr.second;
            if (nodep->classOrPackagep()) {
                const auto it2 = m_packageScopes.find(nodep->classOrPackagep());
                UASSERT_OBJ(it2 != m_packageScopes.end(), nodep, "Can't locate package scope");
                scopep = it2->second;
            }
            const auto it3 = m_varScopes.find(std::make_pair(nodep->varp(), scopep));
            UASSERT_OBJ(it3 != m_varScopes.end(), nodep, "Can't locate varref scope");
            AstVarScope* const varscp = it3->second;
            nodep->varScopep(varscp);
        }
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        AstNodeModule* const modp = nodep->topModulep();
        if (!modp) {
            nodep->v3error("No top level module found");
            return;
        }
        // Operate starting at the top of the hierarchy
        m_aboveCellp = nullptr;
        m_aboveScopep = nullptr;
        iterate(modp);
        cleanupVarRefs();
    }
    void visit(AstNodeModule* nodep) override {
        // Create required blocks and add to module
        string scopename;
        if (!m_aboveScopep) {
            scopename = "TOP";
        } else {
            scopename = m_aboveScopep->name() + "." + m_aboveCellp->name();
        }

        UINFO(4, " MOD AT " << scopename << "  " << nodep << endl);
        AstNode::user1ClearTree();

        m_scopep = new AstScope{
            (m_aboveCellp ? static_cast<AstNode*>(m_aboveCellp) : static_cast<AstNode*>(nodep))
                ->fileline(),
            nodep, scopename, m_aboveScopep, m_aboveCellp};
        if (VN_IS(nodep, Package)) m_packageScopes.emplace(nodep, m_scopep);

        // Now for each child cell, iterate the module this cell points to
        for (AstNode* cellnextp = nodep->stmtsp(); cellnextp; cellnextp = cellnextp->nextp()) {
            if (AstCell* const cellp = VN_CAST(cellnextp, Cell)) {
                VL_RESTORER(m_scopep);  // Protects m_scopep set in called module
                // which is "above" in this code, but later in code execution order
                VL_RESTORER(m_aboveCellp);
                VL_RESTORER(m_aboveScopep);
                {
                    m_aboveCellp = cellp;
                    m_aboveScopep = m_scopep;
                    AstNodeModule* const modp = cellp->modp();
                    UASSERT_OBJ(modp, cellp, "Unlinked mod");
                    iterate(modp);  // Recursive call to visit(AstNodeModule)
                    if (VN_IS(modp, Iface)) {
                        // Remember newly created scope
                        cellp->user2p(m_scopep);
                    }
                }
            }
        }

        // Create scope for the current usage of this module
        UINFO(4, " back AT " << scopename << "  " << nodep << endl);
        AstNode::user1ClearTree();
        m_modp = nodep;
        if (m_modp->isTop()) {
            v3Global.rootp()->createTopScope(m_scopep);
        } else {
            m_modp->addStmtsp(m_scopep);
        }

        // Copy blocks into this scope
        // If this is the first usage of the block ever, we can move the reference
        iterateChildren(nodep);

        // ***Note m_scopep is passed back to the caller of the routine (above)
    }
    void visit(AstClass* nodep) override {
        // Create required blocks and add to module
        VL_RESTORER(m_scopep);
        VL_RESTORER(m_aboveCellp);
        VL_RESTORER(m_aboveScopep);
        VL_RESTORER(m_modp);
        {
            m_aboveScopep = m_scopep;
            m_modp = nodep;

            string scopename;
            if (!m_aboveScopep) {
                scopename = "TOP";
            } else {
                scopename = m_aboveScopep->name() + "." + nodep->name();
            }

            UINFO(4, " CLASS AT " << scopename << "  " << nodep << endl);
            AstNode::user1ClearTree();

            const AstNode* const abovep = (m_aboveCellp ? static_cast<AstNode*>(m_aboveCellp)
                                                        : static_cast<AstNode*>(nodep));
            m_scopep
                = new AstScope{abovep->fileline(), m_modp, scopename, m_aboveScopep, m_aboveCellp};
            m_packageScopes.emplace(nodep, m_scopep);

            // Create scope for the current usage of this cell
            AstNode::user1ClearTree();
            nodep->addMembersp(m_scopep);

            iterateChildren(nodep);
        }
    }
    void visit(AstCellInline* nodep) override {  //
        nodep->scopep(m_scopep);
    }
    void visit(AstActive* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("Actives now made after scoping");
    }
    void visit(AstNodeProcedure* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstAssignAlias* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstAssignVarScope* nodep) override {
        // Copy under the scope but don't recurse
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstAssignW* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstAlwaysPublic* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstCoverToggle* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    Move " << nodep << endl);
        AstNode* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        iterateChildren(clonep);  // We iterate under the *clone*
    }
    void visit(AstCFunc* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    CFUNC " << nodep << endl);
        AstCFunc* const clonep = nodep->cloneTree(false);
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        clonep->scopep(m_scopep);
        // We iterate under the *clone*
        iterateChildren(clonep);
    }
    void visit(AstClocking* nodep) override {
        VL_RESTORER(m_clockingp);
        m_clockingp = nodep;
        UINFO(4, "    CLOCKING " << nodep << endl);
        iterateChildren(nodep);
        if (nodep->varsp()) m_scopep->modp()->addStmtsp(nodep->varsp()->unlinkFrBackWithNext());
        if (nodep->eventp()) m_scopep->modp()->addStmtsp(nodep->eventp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        // Add to list of blocks under this scope
        UINFO(4, "    FTASK " << nodep << endl);
        AstNodeFTask* clonep;
        if (nodep->classMethod()) {
            // Only one scope will be created, so avoid pointless cloning
            nodep->unlinkFrBack();
            clonep = nodep;
        } else {
            clonep = nodep->cloneTree(false);
        }
        nodep->user2p(clonep);
        m_scopep->addBlocksp(clonep);
        // We iterate under the *clone*
        iterateChildren(clonep);
    }
    void visit(AstVar* nodep) override {
        // Make new scope variable
        if (m_clockingp) {
            nodep->name(VString::dot(m_clockingp->name(), "__DOT__", nodep->name()));
        } else if (!nodep->user1p()) {
            AstScope* scopep = m_scopep;
            if (AstIfaceRefDType* const ifacerefp = VN_CAST(nodep->dtypep(), IfaceRefDType)) {
                // Attach every non-virtual interface variable its inner scope
                if (ifacerefp->cellp()) scopep = VN_AS(ifacerefp->cellp()->user2p(), Scope);
            }
            AstVarScope* const varscp = new AstVarScope{nodep->fileline(), scopep, nodep};
            UINFO(6, "   New scope " << varscp << endl);
            if (m_aboveCellp && !m_aboveCellp->isTrace()) varscp->trace(false);
            nodep->user1p(varscp);
            if (v3Global.opt.isClocker(varscp->prettyName())) {
                nodep->attrClocker(VVarAttrClocker::CLOCKER_YES);
            }
            if (v3Global.opt.isNoClocker(varscp->prettyName())) {
                nodep->attrClocker(VVarAttrClocker::CLOCKER_NO);
            }
            UASSERT_OBJ(m_scopep, nodep, "No scope for var");
            m_varScopes.emplace(std::make_pair(nodep, m_scopep), varscp);
            m_scopep->addVarsp(varscp);
        }
    }
    void visit(AstVarRef* nodep) override {
        // VarRef needs to point to VarScope
        // Make sure variable has made user1p.
        UASSERT_OBJ(nodep->varp(), nodep, "Unlinked");
        // We may have not made the variable yet, and we can't make it now as
        // the var's referenced package etc might not be created yet.
        // So push to a list and post-correct.
        // No check here for nodep->classOrPackagep(), will check when walk list.
        m_varRefScopes.emplace(nodep, m_scopep);
    }
    void visit(AstScopeName* nodep) override {
        // If there's a %m in the display text, we add a special node that will contain the name()
        const string prefix = std::string{"__DOT__"} + m_scopep->name();
        // TOP and above will be the user's name().
        // Note 'TOP.' is stripped by scopePrettyName
        // To keep correct visual order, must add before other Text's
        AstText* afterp = nodep->scopeAttrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->addScopeAttrp(new AstText{nodep->fileline(), prefix});
        if (afterp) nodep->addScopeAttrp(afterp);
        afterp = nodep->scopeEntrp();
        if (afterp) afterp->unlinkFrBackWithNext();
        nodep->addScopeEntrp(new AstText{nodep->fileline(), prefix});
        if (afterp) nodep->addScopeEntrp(afterp);
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        // Scope that was made by this module for different cell;
        // Want to ignore blocks under it, so just do nothing
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ScopeVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ScopeVisitor() override = default;
};

//######################################################################
// Scope cleanup -- remove unused activates

class ScopeCleanupVisitor final : public VNVisitor {
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope we are building

    // METHODS

    // VISITORS
    void visit(AstScope* nodep) override {
        // Want to ignore blocks under it
        VL_RESTORER(m_scopep);
        {
            m_scopep = nodep;
            iterateChildren(nodep);
        }
    }

    virtual void movedDeleteOrIterate(AstNode* nodep) {
        if (m_scopep) {
            // The new block; repair varrefs
            iterateChildren(nodep);
        } else {
            // A block that was just moved under a scope, Kill it.
            // Certain nodes can be referenced later in this pass, notably
            // an FTaskRef needs to access the FTask to find the cloned task
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        }
    }

    void visit(AstNodeProcedure* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAssignAlias* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAssignVarScope* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAssignW* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstAlwaysPublic* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstCoverToggle* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstNodeFTask* nodep) override { movedDeleteOrIterate(nodep); }
    void visit(AstCFunc* nodep) override { movedDeleteOrIterate(nodep); }

    void visit(AstVarXRef* nodep) override {
        // The crossrefs are dealt with in V3LinkDot
        nodep->varp(nullptr);
    }
    void visit(AstNodeFTaskRef* nodep) override {
        // The crossrefs are dealt with in V3LinkDot
        UINFO(9, "   Old pkg-taskref " << nodep << endl);
        if (nodep->classOrPackagep()) {
            // Point to the clone
            UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
            AstNodeFTask* const newp = VN_AS(nodep->taskp()->user2p(), NodeFTask);
            UASSERT_OBJ(newp, nodep, "No clone for package function");
            nodep->taskp(newp);
            UINFO(9, "   New pkg-taskref " << nodep << endl);
        } else if (!VN_IS(nodep, MethodCall)) {
            nodep->taskp(nullptr);
            VIsCached::clearCacheTree();
            UINFO(9, "   New pkg-taskref " << nodep << endl);
        }
        iterateChildren(nodep);
    }
    void visit(AstModportFTaskRef* nodep) override {
        // The modport persists only for xml dump
        // The crossrefs are dealt with in V3LinkDot
        nodep->ftaskp(nullptr);
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ScopeCleanupVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ScopeCleanupVisitor() override = default;
};

//######################################################################
// Scope class functions

void V3Scope::scopeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        const ScopeVisitor visitor{nodep};
        ScopeCleanupVisitor{nodep};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("scope", 0, dumpTreeLevel() >= 3);
}
