// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Change names for __PVT__'s
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Name's Transformations:
//
//	Cell/Var's
//		Prepend __PVT__ to variable names
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Name.h"
#include "V3Ast.h"
#include "V3LanguageWords.h"

#include <algorithm>
#include <cstdarg>

//######################################################################
// Name state, as a visitor of each AstNode

class NameVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstCell::user1()	-> bool.  Set true if already processed
    //  AstScope::user1()	-> bool.  Set true if already processed
    //  AstVar::user1()		-> bool.  Set true if already processed
    AstUser1InUse	m_inuser1;

    // STATE
    AstNodeModule*	m_modp;
    V3LanguageWords 	m_words;	// Reserved word detector

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void rename(AstNode* nodep, bool addPvt) {
	if (!nodep->user1()) {  // Not already done
	    if (addPvt) {
                string newname = string("__PVT__")+nodep->name();
		nodep->name(newname);
	    } else {
		string rsvd = m_words.isKeyword(nodep->name());
		if (rsvd != "") {
		    nodep->v3warn(SYMRSVDWORD,"Symbol matches "+rsvd+": '"<<nodep->prettyName()<<"'");
                    string newname = string("__SYM__")+nodep->name();
		    nodep->name(newname);
		}
	    }
	    nodep->user1(1);
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) {
	m_modp = nodep;
        iterateChildren(nodep);
	m_modp = NULL;
    }
    // Add __PVT__ to names of local signals
    virtual void visit(AstVar* nodep) {
	// Don't iterate... Don't need temps for RANGES under the Var.
	rename(nodep, (!m_modp->isTop()
		       && !nodep->isSigPublic()
		       && !nodep->isFuncLocal()	// Isn't exposed, and would mess up dpi import wrappers
		       && !nodep->isTemp()));	// Don't bother to rename internal signals
    }
    virtual void visit(AstCFunc* nodep) {
	if (!nodep->user1()) {
            iterateChildren(nodep);
	    rename(nodep, false);
	}
    }
    virtual void visit(AstVarRef* nodep) {
	if (nodep->varp()) {
            iterate(nodep->varp());
	    nodep->name(nodep->varp()->name());
	}
    }
    virtual void visit(AstCell* nodep) {
	if (!nodep->user1()) {
	    rename(nodep, !nodep->modp()->modPublic());
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstMemberDType* nodep) {
	if (!nodep->user1()) {
	    rename(nodep, false);
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstMemberSel* nodep) {
	if (!nodep->user1()) {
	    rename(nodep, false);
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstScope* nodep) {
	if (!nodep->user1SetOnce()) {
            if (nodep->aboveScopep()) iterate(nodep->aboveScopep());
            if (nodep->aboveCellp()) iterate(nodep->aboveCellp());
	    // Always recompute name (as many level above scope may have changed)
	    // Same formula as V3Scope
	    nodep->name(nodep->isTop() ? "TOP"
			: (nodep->aboveScopep()->name()+"."+nodep->aboveCellp()->name()));
            iterateChildren(nodep);
	}
    }

    //--------------------
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTUCTORS
    explicit NameVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        iterate(nodep);
    }
    virtual ~NameVisitor() {}
};

//######################################################################
// Name class functions

void V3Name::nameAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        NameVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("name", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
