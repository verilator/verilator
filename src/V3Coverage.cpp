//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// COVERAGE TRANSFORMATIONS:
//	At each IF/(IF else)/CASEITEM,
//	   If there's no coverage off on the block below it,
//	   or a $stop
//		Insert a COVERDECL node in the module.
//		(V3Emit reencodes into per-module numbers for emitting.)
//		Insert a COVERINC node at the end of the statement list
//		for that if/else/case.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>

#include "V3Global.h"
#include "V3Coverage.h"
#include "V3Ast.h"
#include "V3Const.h"

//######################################################################
// Coverage state, as a visitor of each AstNode

class CoverageVisitor : public AstNVisitor {
private:
    // TYPES
    typedef map<FileLine*,int>	FileMap;

    // STATE
    bool	m_checkBlock;	// Should this block get covered?
    AstModule*	m_modp;		// Current module to add statement to
    FileMap	m_fileps;	// Column counts for each fileline
    string	m_beginHier;	// AstBegin hier name for user coverage points

    //int debug() { return 9; }

    // METHODS
    AstCoverInc* newCoverInc(FileLine* fl, const string& hier,
			     const string& type, const string& comment) {
	int column = 0;
	FileMap::iterator it = m_fileps.find(fl);
	if (it == m_fileps.end()) {
	    m_fileps.insert(make_pair(fl,column+1));
	} else {
	    column = (it->second)++;
	}

	AstCoverDecl* declp = new AstCoverDecl(fl, column, type, comment);
	declp->hier(hier);
	m_modp->addStmtp(declp);

	return new AstCoverInc(fl, declp);
    }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_fileps.clear();
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstIf* nodep, AstNUser*) {
	UINFO(4," IF: "<<nodep<<endl);
	if (m_checkBlock) {
	    nodep->ifsp()->iterateAndNext(*this);
	    if (m_checkBlock && v3Global.opt.coverageLine()) {	// if a "if" branch didn't disable it
		if (!nodep->backp()->castIf()
		    || nodep->backp()->castIf()->elsesp()!=nodep) {  // Ignore if else; did earlier
		    UINFO(4,"   COVER: "<<nodep<<endl);
		    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "block", "if"));
		}
	    }
	    // Don't do empty else's, only empty if/case's
	    if (nodep->elsesp()) {
		m_checkBlock = true;
		nodep->elsesp()->iterateAndNext(*this);
		if (m_checkBlock && v3Global.opt.coverageLine()) {	// if a "else" branch didn't disable it
		    UINFO(4,"   COVER: "<<nodep<<endl);
		    if (nodep->elsesp()->castIf()) {
			nodep->addElsesp(newCoverInc(nodep->elsesp()->fileline(), "", "block", "elsif"));
		    } else {
			nodep->addElsesp(newCoverInc(nodep->elsesp()->fileline(), "", "block", "else"));
		    }
		}
	    }
	    m_checkBlock = true;  // Reset as a child may have cleared it
	}
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	UINFO(4," CASEI: "<<nodep<<endl);
	if (m_checkBlock && v3Global.opt.coverageLine()) {
	    nodep->bodysp()->iterateAndNext(*this);
	    if (m_checkBlock) {	// if the case body didn't disable it
		UINFO(4,"   COVER: "<<nodep<<endl);
		nodep->addBodysp(newCoverInc(nodep->fileline(), "", "block", "case"));
	    }
	    m_checkBlock = true;  // Reset as a child may have cleared it
	}
    }
    virtual void visit(AstPslCover* nodep, AstNUser*) {
	UINFO(4," PSLCOVER: "<<nodep<<endl);
	m_checkBlock = true;  // Always do cover blocks, even if there's a $stop
	nodep->iterateChildren(*this);
	if (!nodep->coverincp()) {
	    // Note the name may be overridden by V3Assert processing
	    nodep->coverincp(newCoverInc(nodep->fileline(), m_beginHier, "psl_cover", "cover"));
	}
	m_checkBlock = true;  // Reset as a child may have cleared it
    }
    virtual void visit(AstStop* nodep, AstNUser*) {
	UINFO(4,"  STOP: "<<nodep<<endl);
	m_checkBlock = false;
    }
    virtual void visit(AstPragma* nodep, AstNUser*) {
	if (nodep->pragType() == AstPragmaType::COVERAGE_BLOCK_OFF) {
	    // Skip all NEXT nodes under this block, and skip this if/case branch
	    UINFO(4,"  OFF: "<<nodep<<endl);
	    m_checkBlock = false;
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	} else {
	    if (m_checkBlock) nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	// Record the hiearchy of any named begins, so we can apply to user
	// coverage points.  This is because there may be cov points inside
	// generate blocks; each point should get separate consideration.
	// (Currently ignored for line coverage, since any generate iteration
	// covers the code in that line.)
	string oldHier = m_beginHier;
	{
	    if (nodep->name()!="") {
		m_beginHier = m_beginHier + (m_beginHier!=""?".":"") + nodep->name();
	    }
	    nodep->iterateChildren(*this);
	}
	m_beginHier = oldHier;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	if (m_checkBlock) {
	    nodep->iterateChildren(*this);
	    m_checkBlock = true;  // Reset as a child may have cleared it
	}
    }

public:
    // CONSTUCTORS
    CoverageVisitor(AstNetlist* rootp) {
	// Operate on all modules
	m_checkBlock = true;
	m_beginHier = "";
	rootp->iterateChildren(*this);
    }
    virtual ~CoverageVisitor() {}
};

//######################################################################
// Coverage class functions

void V3Coverage::coverage(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CoverageVisitor visitor (rootp);
}
