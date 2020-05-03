// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Change names for __PVT__'s
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
// V3Name's Transformations:
//
//      Cell/Var's
//              Prepend __PVT__ to variable names
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Name.h"
#include "V3Ast.h"
#include "V3File.h"
#include "V3LanguageWords.h"

#include <algorithm>
#include <cstdarg>

//######################################################################
// Name state, as a visitor of each AstNode

class NameVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstCell::user1()        -> bool.  Set true if already processed
    //  AstScope::user1()       -> bool.  Set true if already processed
    //  AstVar::user1()         -> bool.  Set true if already processed
    AstUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp;
    V3LanguageWords m_words;  // Reserved word detector

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void rename(AstNode* nodep, bool addPvt) {
        if (!nodep->user1()) {  // Not already done
            if (addPvt) {
                string newname = string("__PVT__") + nodep->name();
                nodep->name(newname);
                nodep->editCountInc();
            } else if (VN_IS(nodep, CFunc) && VN_CAST(nodep, CFunc)->isConstructor()) {
            } else {
                string rsvd = m_words.isKeyword(nodep->name());
                if (rsvd != "") {
                    nodep->v3warn(SYMRSVDWORD,
                                  "Symbol matches " + rsvd + ": " << nodep->prettyNameQ());
                    string newname = string("__SYM__") + nodep->name();
                    nodep->name(newname);
                    nodep->editCountInc();
                }
            }
            nodep->user1(1);
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    // Add __PVT__ to names of local signals
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        // Don't iterate... Don't need temps for RANGES under the Var.
        rename(nodep,
               ((!m_modp || !m_modp->isTop()) && !nodep->isSigPublic()
                && !nodep->isFuncLocal()  // Isn't exposed, and would mess up dpi import wrappers
                && !nodep->isTemp()));  // Don't bother to rename internal signals
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        if (!nodep->user1()) {
            iterateChildren(nodep);
            rename(nodep, false);
        }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (nodep->varp()) {
            iterate(nodep->varp());
            nodep->name(nodep->varp()->name());
        }
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        if (!nodep->user1()) {
            rename(nodep, (!nodep->modp()->modPublic() && !VN_IS(nodep->modp(), ClassPackage)));
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstMemberDType* nodep) VL_OVERRIDE {
        if (!nodep->user1()) {
            rename(nodep, false);
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstMemberSel* nodep) VL_OVERRIDE {
        if (!nodep->user1()) {
            rename(nodep, false);
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstScope* nodep) VL_OVERRIDE {
        if (!nodep->user1SetOnce()) {
            if (nodep->aboveScopep()) iterate(nodep->aboveScopep());
            if (nodep->aboveCellp()) iterate(nodep->aboveCellp());
            // Always recompute name (as many levels above scope may have changed)
            // Same formula as V3Scope
            nodep->name(nodep->isTop()
                            ? "TOP"
                            : VN_IS(m_modp, Class) ? ("TOP." + m_modp->name())
                                                   : VN_IS(m_modp, ClassPackage)
                                                         ? ("TOP." + m_modp->name())
                                                         : (nodep->aboveScopep()->name() + "."
                                                            + nodep->aboveCellp()->name()));
            nodep->editCountInc();
            iterateChildren(nodep);
        }
    }

    //--------------------
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit NameVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        iterate(nodep);
    }
    virtual ~NameVisitor() {}
};

//######################################################################
// Name class functions

void V3Name::nameAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { NameVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("name", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
