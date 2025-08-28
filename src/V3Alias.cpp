// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve aliases
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Alias.h"

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class AliasFindVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVar::user1p()        -> AstVar*.  Variable with which the node to be replaced

    // METHODS
public:
    static AstVar* getAliasVarp(AstVar* const varp) {
        if (varp->user1p() && varp != varp->user1p()) {
            AstVar* const aliasp = getAliasVarp(VN_AS(varp->user1p(), Var));
            varp->user1p(aliasp);
            return aliasp;
        } else {
            return varp;
        }
    }

private:
    static void setAliasVar(AstVar* const varp, AstVar* const aliasp) {
        getAliasVarp(varp)->user1p(aliasp);
    }

    // VISITORS
    void visit(AstAlias* nodep) override {
        AstVar* aliasVarp = nullptr;
        for (AstNode* itemp = nodep->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstVarRef* const refp = VN_CAST(itemp, VarRef)) {
                AstVar* const varp = refp->varp();
                if (varp->isIO()) {
                    itemp->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Aliased expression referencing port");
                    break;
                }
                if (!aliasVarp) {
                    aliasVarp = getAliasVarp(varp);
                } else {
                    setAliasVar(varp, aliasVarp);
                }
            } else {
                itemp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Aliased expression is not a simple variable reference");
                break;
            }
        }
        pushDeletep(nodep->unlinkFrBack());
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AliasFindVisitor(AstNetlist* nodep) { iterate(nodep); }
};

class AliasResolveVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVar::user1p()        -> AstVar*.  Variable with which the node to be replaced
    //  AstAssignW::user1()    -> bool.  True if the assignment was added to handle alias

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        if (nodep->varp()->user1p()) nodep->varp(VN_AS(nodep->varp()->user1p(), Var));
    }

    void visit(AstPin* nodep) override {
        if (nodep->modVarp()->user1p()) nodep->modVarp(VN_AS(nodep->modVarp()->user1p(), Var));
    }

    void visit(AstAssignW* nodep) override {
        // Don't replace variables in assignments added in this stage
        if (!nodep->user1()) iterateChildren(nodep);
    }

    void visit(AstVar* nodep) override {
        AstVar* const aliasp = AliasFindVisitor::getAliasVarp(nodep);
        if (nodep != aliasp) {
            AstAssignW* const assignp = new AstAssignW{
                nodep->fileline(), new AstVarRef{nodep->fileline(), nodep, VAccess::WRITE},
                new AstVarRef{nodep->fileline(), aliasp, VAccess::READ}};
            assignp->user1(true);
            nodep->addNextHere(assignp);
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AliasResolveVisitor(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// Alias class functions

void V3Alias::alias(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        // Destruct before checking
        AliasFindVisitor{nodep};
        AliasResolveVisitor{nodep};
    }
    V3Global::dumpCheckGlobalTree("alias", 0, dumpTreeEitherLevel() >= 3);
}
