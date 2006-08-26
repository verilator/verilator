// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Removal of named begin blocks
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Begin's Transformations:
//		
// Each module:
//	Look for BEGINs
//	    BEGIN(VAR...) -> VAR ... {renamed}
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Begin.h"
#include "V3Inst.h"
#include "V3Ast.h"

//######################################################################

class BeginVisitor : public AstNVisitor {
private:
    // STATE
    AstModule*		m_modp;		// Current module
    AstNodeFTask* 	m_ftaskp;	// Current function/task
    string		m_beginScope;	// Name of begin blocks above us
    //int debug() { return 9; }

    bool nameMatchesGen(const char* namep, string& numr) {
	numr = "";
	bool needbar = false;
	for (const char* cp=namep; *cp; ) {
	    if (0==strncmp(cp,"genblk",6) || 0==strncmp(cp,"genfor",6)) {
		cp += 6;
	    } else if (isdigit(*cp)) {
		if (needbar) { numr += '_'; needbar = false; }
		numr += *cp++;
	    } else if (*cp=='_') {
		cp++;
		needbar = true;
	    } else {
		return false;  // Not exact match
	    }
	}
	return true;
    }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_ftaskp = nodep;
	nodep->iterateChildren(*this);
	m_ftaskp = NULL;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	// Begin blocks were only useful in variable creation, change names and delete
	UINFO(8,"  "<<nodep<<endl);
	string oldScope = m_beginScope;
	{
	    //string nameNum;
	    //string oldNum;
	    //if (nameMatchesGen(oldScope.c_str(), oldNum/*ref*/)
	    //	&& nameMatchesGen(nodep->name().c_str(), nameNum/*ref*/)
	    //	&& 0) {  // Messes up V3Link
	    //	// Need to leave the dot or we mess up later V3LinkDot
	    //	// gen[blk|for]##_gen[blk|for]##  -> gen[blk|for]##__DOT__##...
	    //	m_beginScope = oldScope + "__DOT__"+nameNum;

	    //UINFO(8,"nname "<<m_beginScope<<endl);
	    // Create data for dotted variable resolution
	    string dottedname = nodep->name() + "__DOT__";  // So always found
	    string::size_type pos;
	    while ((pos=dottedname.find("__DOT__")) != string::npos) {
		string ident = dottedname.substr(0,pos);
		dottedname = dottedname.substr(pos+strlen("__DOT__"));
		if (m_beginScope=="") m_beginScope = nodep->name();
		else m_beginScope = m_beginScope + "__DOT__"+ident;
		// Create CellInline for dotted resolution
		AstCellInline* inlinep = new AstCellInline(nodep->fileline(),
							   m_beginScope, "__BEGIN__");
		m_modp->addInlinesp(inlinep);  // Must be parsed before any AstCells
	    }

	    // Remap var names
	    nodep->iterateChildren(*this);

	    if (AstNode* stmtsp = nodep->stmtsp()) {
		stmtsp->unlinkFrBackWithNext();
		nodep->replaceWith(stmtsp);
	    } else {
		nodep->unlinkFrBack();
	    }
	    pushDeletep(nodep); nodep=NULL;
	}
	m_beginScope = oldScope;
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	if (m_beginScope != "") {
	    // Rename it
	    nodep->name(m_beginScope+"__DOT__"+nodep->name());
	    // Move to module
	    nodep->unlinkFrBack();
	    if (m_ftaskp) m_ftaskp->addStmtsp(nodep);   // Begins under funcs just move into the func
	    else m_modp->addStmtp(nodep);
	}
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	UINFO(8,"   CELL "<<nodep<<endl);
	if (m_beginScope != "") {
	    // Rename it
	    nodep->name(m_beginScope+"__DOT__"+nodep->name());
	    UINFO(8,"     rename to "<<nodep->name()<<endl);
	    // Move to module
	    nodep->unlinkFrBack();
	    m_modp->addStmtp(nodep);
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    BeginVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	m_ftaskp = NULL;
	nodep->accept(*this);
    }
    virtual ~BeginVisitor() {}
};

//######################################################################
// Task class functions

void V3Begin::debeginAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    BeginVisitor bvisitor (nodep);
}
