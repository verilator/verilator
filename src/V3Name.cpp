// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Change names for __PVT__'s
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Name's Transformations:
//
//      Cell/Var's
//              Prepend __PVT__ to variable names
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Name.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3LanguageWords.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Name state, as a visitor of each AstNode

class NameVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstCell::user1()        -> bool.  Set true if already processed
    //  AstScope::user1()       -> bool.  Set true if already processed
    //  AstVar::user1()         -> bool.  Set true if already processed
    const VNUser1InUse m_inuser1;

    // STATE - for current visit position (use VL_RESTORER)
    const AstNodeModule* m_modp = nullptr;  // Current module

    // METHODS
    void rename(AstNode* nodep, bool addPvt) {
        if (!nodep->user1()) {  // Not already done
            if (addPvt) {
                const string newname = std::string{"__PVT__"} + nodep->name();
                nodep->name(newname);
                nodep->editCountInc();
            } else if (VN_IS(nodep, CFunc) && VN_AS(nodep, CFunc)->isConstructor()) {
            } else {
                const string rsvd = V3LanguageWords::isKeyword(nodep->name());
                if (rsvd != "") {
                    nodep->v3warn(SYMRSVDWORD,
                                  "Symbol matches " + rsvd + ": " << nodep->prettyNameQ());
                    const string newname = std::string{"__SYM__"} + nodep->name();
                    nodep->name(newname);
                    nodep->editCountInc();
                }
            }
            nodep->user1(1);
        }
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    // Add __PVT__ to names of local signals
    void visit(AstVar* nodep) override {
        // Don't iterate... Don't need temps for RANGES under the Var.
        rename(nodep,
               ((!m_modp || !m_modp->isTop()) && !nodep->isSigPublic()
                && !nodep->isFuncLocal()  // Isn't exposed, and would mess up dpi import wrappers
                && !nodep->isTemp()));  // Don't bother to rename internal signals
    }
    void visit(AstCFunc* nodep) override {
        if (!nodep->user1()) {
            iterateChildren(nodep);
            rename(nodep, false);
        }
    }
    void visit(AstVarRef* nodep) override { iterate(nodep->varp()); }
    void visit(AstCell* nodep) override {
        if (!nodep->user1()) {
            rename(nodep, (!nodep->modp()->modPublic() && !VN_IS(nodep->modp(), ClassPackage)));
            iterateChildren(nodep);
        }
    }
    void visit(AstMemberDType* nodep) override {
        if (!nodep->user1()) {
            rename(nodep, true);
            iterateChildren(nodep);
        }
    }
    void visit(AstMemberSel* nodep) override {
        if (!nodep->user1()) {
            rename(nodep, true);
            iterateChildren(nodep);
        }
    }
    void visit(AstStructSel* nodep) override {
        if (!nodep->user1()) {
            rename(nodep, true);
            iterateChildren(nodep);
        }
    }
    void visit(AstScope* nodep) override {
        if (!nodep->user1SetOnce()) {
            if (nodep->aboveScopep()) iterate(nodep->aboveScopep());
            if (nodep->aboveCellp()) iterate(nodep->aboveCellp());
            // Always recompute name (as many levels above scope may have changed)
            // Same formula as V3Scope
            nodep->name(nodep->isTop()         ? "TOP"
                        : VN_IS(m_modp, Class) ? ("TOP." + m_modp->name())
                        : VN_IS(m_modp, ClassPackage)
                            ? ("TOP." + m_modp->name())
                            : (nodep->aboveScopep()->name() + "." + nodep->aboveCellp()->name()));
            nodep->editCountInc();
            iterateChildren(nodep);
        }
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit NameVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~NameVisitor() override = default;
};

//######################################################################
// Name class functions

void V3Name::nameAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { NameVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("name", 0, dumpTreeLevel() >= 6);
}
