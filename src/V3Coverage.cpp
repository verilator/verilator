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

//######################################################################
// Coverage state, as a visitor of each AstNode

class CoverageVisitor : public AstNVisitor {
private:
    // TYPES
    typedef map<string,int>	FileMap;

    // STATE
    bool	m_checkBlock;	// Should this block get covered?
    AstModule*	m_modp;		// Current module to add statement to
    bool	m_inToggleOff;	// In function/task etc
    FileMap	m_fileps;	// Column counts for each fileline
    string	m_beginHier;	// AstBegin hier name for user coverage points

    //int debug() { return 9; }

    // METHODS
    const char* varIgnoreToggle(AstVar* nodep) {
	// Return true if this shouldn't be traced
	// See also similar rule in V3TraceDecl::varIgnoreTrace
	string prettyName = nodep->prettyName();
	if (!nodep->isToggleCoverable())
	    return "Not relevant signal type";
	if (prettyName.c_str()[0] == '_')
	    return "Leading underscore";
	if (prettyName.find("._") != string::npos)
	    return "Inlined leading underscore";
	if ((nodep->width()*nodep->arrayElements()) > 256) return "Wide bus/array > 256 bits";
	// We allow this, though tracing doesn't
	// if (nodep->arrayp(1)) return "Unsupported: Multi-dimensional array";
	return NULL;
    }

    AstCoverInc* newCoverInc(FileLine* fl, const string& hier,
			     const string& page_prefix, const string& comment) {
	// For line coverage, we may have multiple if's on one line, so disambiguate if
	// everything is otherwise identical
	// (Don't set column otherwise as it may result in making bins not match up with
	// different types of coverage enabled.)
	string key = fl->filename()+"\001"+cvtToStr(fl->lineno())+"\001"+hier+"\001"+page_prefix+"\001"+comment;
	int column = 0;
	FileMap::iterator it = m_fileps.find(key);
	if (it == m_fileps.end()) {
	    m_fileps.insert(make_pair(key,column+1));
	} else {
	    column = (it->second)++;
	}

	// We could use the basename of the filename to the page, but seems better for code
	// from an include file to be listed under the module using it rather than the include file.
	// Note the module name could have parameters appended, thus we use origName.
	// Someday the user might be allowed to specify a different page suffix
	string page = page_prefix + "/" + m_modp->origName();

	AstCoverDecl* declp = new AstCoverDecl(fl, column, page, comment);
	declp->hier(hier);
	m_modp->addStmtp(declp);

	return new AstCoverInc(fl, declp);
    }

    // VISITORS - BOTH
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_fileps.clear();
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }

    // VISITORS - TOGGLE COVERAGE
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	bool oldtog = m_inToggleOff;
	{
	    m_inToggleOff = true;
	    nodep->iterateChildren(*this);
	}
	m_inToggleOff = oldtog;
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_modp && !m_inToggleOff
	    && nodep->fileline()->coverageOn() && v3Global.opt.coverageToggle()) {
	    const char* disablep = varIgnoreToggle(nodep);
	    if (disablep) {
		UINFO(4, "    Disable Toggle: "<<disablep<<" "<<nodep<<endl);
	    } else {
		UINFO(4, "    Toggle: "<<nodep<<endl);
		// There's several overall ways to approach this
		//    Treat like tracing, where a end-of-timestamp action sees all changes
		//	Works ok, but would be quite slow as need to reform vectors before the calls
		//    Convert to "always @ (posedge signal[#]) coverinc"
		//	Would mark many signals as clocks, precluding many later optimizations
		//    Convert to "if (x & !lastx) CoverInc"
		//	OK, but we couldn't later detect them to schedule where the IFs get called
		//    Convert to "AstCoverInc(CoverInc...)"
		//	We'll do this, and make the if(...) coverinc later.

		// Compute size of the problem
		int dimensions = 0;
		for (AstRange* arrayp=nodep->arraysp(); arrayp; arrayp = arrayp->nextp()->castRange()) {
		    dimensions++;
		}

		// Add signal to hold the old value
		string newvarname = (string)"__Vtogcov__"+nodep->shortName();
		AstVar* chgVarp = new AstVar (nodep->fileline(), AstVarType::MODULETEMP, newvarname, nodep);
		m_modp->addStmtp(chgVarp);

		// Create bucket for each dimension * bit.
		// This is necessarily an O(n^2) expansion, which is why
		// we limit coverage to signals with < 256 bits.
		vector<int> selects_docs;  selects_docs.resize(dimensions);
		vector<int> selects_code;  selects_code.resize(dimensions);
		toggleVarRecurse(nodep, chgVarp, nodep->arraysp(),
				 0, selects_docs, selects_code );
	    }
	}
    }

    void toggleVarRecurse(AstVar* nodep, AstVar* chgVarp, AstRange* arrayp,
			  int dimension, vector<int>& selects_docs, vector<int>& selects_code) {
	if (arrayp) {
	    for (int index=arrayp->lsbConst(); index<=arrayp->msbConst()+1; index++) {
		// Handle the next dimension, if any
		selects_docs[dimension] = index;
		selects_code[dimension] = index - arrayp->lsbConst();
		toggleVarRecurse(nodep, chgVarp, arrayp->nextp()->castRange(),
				 dimension+1, selects_docs, selects_code);
	    }
	} else {  // No more arraying - just each bit in the width
	    if (nodep->rangep()) {
		for (int bitindex_docs=nodep->lsb(); bitindex_docs<nodep->msb()+1; bitindex_docs++) {
		    toggleVarBottom(nodep, chgVarp,
				    dimension, selects_docs, selects_code,
				    true, bitindex_docs);
		}
	    } else {
		toggleVarBottom(nodep, chgVarp,
				dimension, selects_docs, selects_code,
				false, 0);
	    }
	}
    }
    void toggleVarBottom(AstVar* nodep, AstVar* chgVarp,
			 int dimension, vector<int>& selects_docs, vector<int>& selects_code,
			 bool bitsel, int bitindex_docs) {
	string comment = nodep->name();
	AstNode* varRefp = new AstVarRef(nodep->fileline(), nodep, false);
	AstNode* chgRefp = new AstVarRef(nodep->fileline(), chgVarp, true);
	// Now determine the name of, and how to get to the bit of this slice
	for (int dim=0; dim<dimension; dim++) {
	    // Comments are strings, not symbols, so we don't need __BRA__ __KET__ 
	    comment += "["+cvtToStr(selects_docs[dim])+"]";
	    varRefp = new AstArraySel(nodep->fileline(), varRefp, selects_code[dim]);
	    chgRefp = new AstArraySel(nodep->fileline(), chgRefp, selects_code[dim]);
	}
	if (bitsel) {
	    comment += "["+cvtToStr(bitindex_docs)+"]";
	    int bitindex_code = bitindex_docs - nodep->lsb();
	    varRefp = new AstSel(nodep->fileline(), varRefp, bitindex_code, 1);
	    chgRefp = new AstSel(nodep->fileline(), chgRefp, bitindex_code, 1);
	}
	AstCoverToggle* newp = new AstCoverToggle (nodep->fileline(),
						   newCoverInc(nodep->fileline(), "", "v_toggle", comment),
						   varRefp, chgRefp);
	m_modp->addStmtp(newp);
    }

    // VISITORS - LINE COVERAGE
    virtual void visit(AstIf* nodep, AstNUser*) {
	UINFO(4," IF: "<<nodep<<endl);
	if (m_checkBlock) {
	    nodep->ifsp()->iterateAndNext(*this);
	    if (m_checkBlock
		&& nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {	// if a "if" branch didn't disable it
		if (!nodep->backp()->castIf()
		    || nodep->backp()->castIf()->elsesp()!=nodep) {  // Ignore if else; did earlier
		    UINFO(4,"   COVER: "<<nodep<<endl);
		    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_line", "if"));
		}
	    }
	    // Don't do empty else's, only empty if/case's
	    if (nodep->elsesp()) {
		m_checkBlock = true;
		nodep->elsesp()->iterateAndNext(*this);
		if (m_checkBlock
		    && nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {	// if a "else" branch didn't disable it
		    UINFO(4,"   COVER: "<<nodep<<endl);
		    if (nodep->elsesp()->castIf()) {
			nodep->addElsesp(newCoverInc(nodep->elsesp()->fileline(), "", "v_line", "elsif"));
		    } else {
			nodep->addElsesp(newCoverInc(nodep->elsesp()->fileline(), "", "v_line", "else"));
		    }
		}
	    }
	    m_checkBlock = true;  // Reset as a child may have cleared it
	}
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	UINFO(4," CASEI: "<<nodep<<endl);
	if (m_checkBlock
	    && nodep->fileline()->coverageOn() && v3Global.opt.coverageLine()) {
	    nodep->bodysp()->iterateAndNext(*this);
	    if (m_checkBlock) {	// if the case body didn't disable it
		UINFO(4,"   COVER: "<<nodep<<endl);
		nodep->addBodysp(newCoverInc(nodep->fileline(), "", "v_line", "case"));
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
	    nodep->coverincp(newCoverInc(nodep->fileline(), m_beginHier, "v_user", "cover"));
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
	bool oldtog = m_inToggleOff;
	{
	    m_inToggleOff = true;
	    if (nodep->name()!="") {
		m_beginHier = m_beginHier + (m_beginHier!=""?".":"") + nodep->name();
	    }
	    nodep->iterateChildren(*this);
	}
	m_beginHier = oldHier;
	m_inToggleOff = oldtog;
    }

    // VISITORS - BOTH
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
	m_inToggleOff = false;
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
