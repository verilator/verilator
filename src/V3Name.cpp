// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Change names for __PVT__'s
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Name.h"
#include "V3Ast.h"
#include "V3LanguageWords.h"

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
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void rename(AstNode* nodep, bool addPvt) {
	if (!nodep->user1()) {  // Not already done
	    if (addPvt) {
		string newname = (string)"__PVT__"+nodep->name();
		nodep->name(newname);
	    } else {
		string rsvd = m_words.isKeyword(nodep->name());
		if (rsvd != "") {
		    nodep->v3warn(SYMRSVDWORD,"Symbol matches "+rsvd+": '"<<nodep->prettyName()<<"'");
		    string newname = (string)"__SYM__"+nodep->name();
		    nodep->name(newname);
		}
	    }
	    nodep->user1(1);
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    // Add __PVT__ to names of local signals
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Don't iterate... Don't need temps for RANGES under the Var.
	rename(nodep, (!m_modp->isTop()
		       && !nodep->isSigPublic()
		       && !nodep->isFuncLocal()	// Isn't exposed, and would mess up dpi import wrappers
		       && !nodep->isTemp()));	// Don't bother to rename internal signals
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    nodep->iterateChildren(*this);
	    rename(nodep, false);
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->varp()) {
	    nodep->varp()->iterate(*this);
	    nodep->name(nodep->varp()->name());
	}
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    rename(nodep, !nodep->modp()->modPublic());
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstMemberDType* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    rename(nodep, false);
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstMemberSel* nodep, AstNUser*) {
	if (!nodep->user1()) {
	    rename(nodep, false);
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	if (!nodep->user1SetOnce()) {
	    if (nodep->aboveScopep()) nodep->aboveScopep()->iterate(*this);
	    if (nodep->aboveCellp()) nodep->aboveCellp()->iterate(*this);
	    // Always recompute name (as many level above scope may have changed)
	    // Same formula as V3Scope
	    nodep->name(nodep->isTop() ? "TOP"
			: (nodep->aboveScopep()->name()+"."+nodep->aboveCellp()->name()));
	    nodep->iterateChildren(*this);
	}
    }

    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    NameVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~NameVisitor() {}
};

//######################################################################
// Name class functions

void V3Name::nameAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    NameVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("name.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
