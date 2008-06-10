//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
//  Pre steps:
//	Attach clocks to each assertion
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3AssertPre.h"
#include "V3Ast.h"

//######################################################################
// Assert class functions

class AssertPreVisitor : public AstNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE/TYPES
    // STATE
    // Reset each module:
    AstSenItem*	m_seniDefaultp;	// Default sensitivity (from AstDefClock)
    // Reset each assertion:
    AstSenItem*	m_senip;	// Last sensitivity

    int debug() { return 0; }

    // METHODS
    AstSenTree* newSenTree(AstNode* nodep) {
	// Create sentree based on clocked or default clock
	// Return NULL for always
	AstSenTree* newp = NULL;
	AstSenItem* senip = m_senip ? m_senip : m_seniDefaultp;
	if (senip) newp = new AstSenTree(nodep->fileline(), senip->cloneTree(true));
	if (!senip) nodep->v3error("Unsupported: Unclocked assertion");
	return newp;
    }

    // VISITORS  //========== Statements
    virtual void visit(AstPslDefClock* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Store the new default clock, reset on new module
	m_seniDefaultp = nodep->sensesp();
	// Trash it
	nodep->unlinkFrBack();
	pushDeletep(nodep); nodep=NULL;
    }

    virtual void visit(AstPslCover* nodep, AstNUser*) {
	// Prep
	m_senip = NULL;
	nodep->iterateChildren(*this);
	nodep->sentreep(newSenTree(nodep));
	m_senip = NULL;
    }
    virtual void visit(AstPslAssert* nodep, AstNUser*) {
	// Prep
	m_senip = NULL;
	nodep->iterateChildren(*this);
	nodep->sentreep(newSenTree(nodep));
	m_senip = NULL;
    }
    virtual void visit(AstPslClocked* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_senip) {
	    nodep->v3error("Unsupported: Only one PSL clock allowed per assertion\n");
	}
	// Unlink and just keep a pointer to it, convert to sentree as needed
	AstNode* blockp = nodep->propp()->unlinkFrBack();
	m_senip = nodep->sensesp();
	nodep->replaceWith(blockp);
	pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Reset defaults
	m_seniDefaultp = NULL;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTRUCTORS
    AssertPreVisitor(AstNetlist* nodep) {
	m_senip = NULL;
	m_seniDefaultp = NULL;
	// Process
	nodep->accept(*this);
    }
    virtual ~AssertPreVisitor() {}
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    AssertPreVisitor visitor (nodep);
}
