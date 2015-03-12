// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// LinkParse TRANSFORMATIONS:
//	Top-down traversal
//	    Move some attributes around
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <set>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkParse.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkParseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on netlist
    //  AstNode::user1()	-> bool.  True if processed
    //  AstNode::user2()	-> bool.  True if fileline recomputed
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    typedef map <pair<void*,string>,AstTypedef*> ImplTypedefMap;
    typedef set <FileLine*> FileLineSet;

    // STATE
    AstVar*		m_varp;		// Variable we're under
    ImplTypedefMap	m_implTypedef;	// Created typedefs for each <container,name>
    FileLineSet		m_filelines;	// Filelines that have been seen
    bool		m_inAlways;	// Inside an always
    bool		m_inGenerate;	// Inside a generate
    bool		m_needStart;	// Need start marker on lower AstParse
    AstNodeModule*	m_valueModp;	// If set, move AstVar->valuep() initial values to this module
    AstNodeModule*	m_modp;		// Current module
    AstNodeFTask*	m_ftaskp;	// Current task
    AstNodeDType*	m_dtypep;	// Current data type

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void cleanFileline(AstNode* nodep) {
	if (!nodep->user2SetOnce()) {  // Process once
	    // We make all filelines unique per AstNode.  This allows us to
	    // later turn off messages on a fileline when an issue is found
	    // so that messages on replicated blocks occur only once,
	    // without suppressing other token's messages as a side effect.
	    // We could have verilog.l create a new one on every token,
	    // but that's a lot more structures than only doing AST nodes.
	    if (m_filelines.find(nodep->fileline()) != m_filelines.end()) {
		nodep->fileline(new FileLine(nodep->fileline()));
	    }
	    m_filelines.insert(nodep->fileline());
	}
    }

    // VISITs
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	if (!nodep->user1SetOnce()) {  // Process only once.
	    cleanFileline(nodep);
	    m_ftaskp = nodep;
	    nodep->iterateChildren(*this);
	    m_ftaskp = NULL;
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (!nodep->user1SetOnce()) {  // Process only once.
	    cleanFileline(nodep);
	    UINFO(5,"   "<<nodep<<endl);
	    AstNodeModule* upperValueModp = m_valueModp;
	    m_valueModp = NULL;
	    nodep->iterateChildren(*this);
	    m_valueModp = upperValueModp;
	}
    }
    virtual void visit(AstNodeDType* nodep, AstNUser*) {
	if (!nodep->user1SetOnce()) {  // Process only once.
	    cleanFileline(nodep);
	    AstNodeDType* upperDtypep = m_dtypep;
	    m_dtypep = nodep;
	    nodep->iterateChildren(*this);
	    m_dtypep = upperDtypep;
	}
    }
    virtual void visit(AstEnumItem* nodep, AstNUser*) {
	// Expand ranges
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (nodep->rangep()) {
	    if (!nodep->rangep()->msbp()->castConst()
		|| !nodep->rangep()->lsbp()->castConst()) nodep->v3error("Enum ranges must be integral, per spec");
	    int msb = nodep->rangep()->msbConst();
	    int lsb = nodep->rangep()->lsbConst();
	    int increment = (msb > lsb) ? -1 : 1;
	    int offset_from_init = 0;
	    AstNode* addp = NULL;
	    for (int i=msb; i!=(lsb+increment); i+=increment, offset_from_init++) {
		string name = nodep->name() + cvtToStr(i);
		AstNode* valuep = NULL;
		if (nodep->valuep()) valuep = new AstAdd(nodep->fileline(), nodep->valuep()->cloneTree(true),
							 new AstConst(nodep->fileline(), AstConst::Unsized32(), offset_from_init));
		addp = addp->addNextNull(new AstEnumItem(nodep->fileline(), name, NULL, valuep));
	    }
	    nodep->replaceWith(addp);
	    nodep->deleteTree();
	}
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	cleanFileline(nodep);
	// We used modTrace before leveling, and we may now
	// want to turn it off now that we know the levelizations
	if (v3Global.opt.traceDepth()
	    && m_modp
	    && (m_modp->level()-1) > v3Global.opt.traceDepth()) {
	    m_modp->modTrace(false);
	    nodep->trace(false);
	}
	m_varp = nodep;
	nodep->iterateChildren(*this);
	m_varp = NULL;
	// temporaries under an always aren't expected to be blocking
	if (m_inAlways) nodep->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
	if (nodep->valuep()) {
	    // A variable with an = value can be three things:
	    FileLine* fl = nodep->valuep()->fileline();
	    // 1. Parameters and function inputs: It's a default to use if not overridden
	    if (nodep->isParam() || (m_ftaskp && nodep->isInOnly())) {
	    }
	    else if (!m_ftaskp && nodep->isInOnly()) {
		nodep->v3error("Unsupported: Default value on module input: "<<nodep->prettyName());
		nodep->valuep()->unlinkFrBack()->deleteTree();
	    } // 2. Under modules, it's an initial value to be loaded at time 0 via an AstInitial
	    else if (m_valueModp) {
		nodep->addNextHere
		    (new AstInitial
		     (fl, new AstAssign (fl, new AstVarRef(fl, nodep->name(), true),
					 nodep->valuep()->unlinkFrBack())));
	    } // 3. Under blocks, it's an initial value to be under an assign
	    else {
		nodep->addNextHere
		    (new AstAssign (fl, new AstVarRef(fl, nodep->name(), true),
				    nodep->valuep()->unlinkFrBack()));
	    }
	}
	if (nodep->isIfaceRef() && !nodep->isIfaceParent()) {
	    // Only AstIfaceRefDType's at this point correspond to ports;
	    // haven't made additional ones for interconnect yet, so assert is simple
	    // What breaks later is we don't have a Scope/Cell representing the interface to attach to
	    if (m_modp->level()<=2) nodep->v3error("Unsupported: Interfaced port on top level module");
	}
    }

    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (nodep->attrType() == AstAttrType::DT_PUBLIC) {
	    AstTypedef* typep = nodep->backp()->castTypedef();
	    if (!typep) nodep->v3fatalSrc("Attribute not attached to typedef");
	    typep->attrPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_CLOCK) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrScClocked(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_CLOCK_ENABLE) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrClockEn(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true); m_varp->sigModPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RD) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRdPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_PUBLIC_FLAT_RW) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->sigUserRWPublic(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_ISOLATE_ASSIGNMENTS) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrIsolateAssign(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_SFORMAT) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrSFormat(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_SC_BV) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrScBv(true);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_CLOCKER) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrClocker(AstVarAttrClocker::CLOCKER_YES);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	else if (nodep->attrType() == AstAttrType::VAR_NO_CLOCKER) {
	    if (!m_varp) nodep->v3fatalSrc("Attribute not attached to variable");
	    m_varp->attrClocker(AstVarAttrClocker::CLOCKER_NO);
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
    }

    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	// AlwaysPublic was attached under a var, but it's a statement that should be
	// at the same level as the var
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
	if (m_varp) {
	    nodep->unlinkFrBack();
	    m_varp->addNext(nodep);
	    // lvalue is true, because we know we have a verilator public_flat_rw
	    // but someday we may be more general
	    bool lvalue = m_varp->isSigUserRWPublic();
	    nodep->addStmtp(new AstVarRef(nodep->fileline(), m_varp, lvalue));
	}
    }

    virtual void visit(AstDefImplicitDType* nodep, AstNUser*) {
	cleanFileline(nodep);
	UINFO(8,"   DEFIMPLICIT "<<nodep<<endl);
	// Must remember what names we've already created, and combine duplicates
	// so that for "var enum {...} a,b" a & b will share a common typedef
	// Unique name space under each containerp() so that an addition of a new type won't change every verilated module.
	AstTypedef* defp = NULL;
	ImplTypedefMap::iterator it = m_implTypedef.find(make_pair(nodep->containerp(), nodep->name()));
	if (it != m_implTypedef.end()) {
	    defp = it->second;
	} else {
	    // Definition must be inserted right after the variable (etc) that needed it
	    // AstVar, AstTypedef, AstNodeFTask are common containers
	    AstNode* backp = nodep->backp();
	    for (; backp; backp=backp->backp()) {
		if (backp->castVar()) break;
		else if (backp->castTypedef()) break;
		else if (backp->castNodeFTask()) break;
	    }
	    if (!backp) nodep->v3fatalSrc("Implicit enum/struct type created under unexpected node type");
	    AstNodeDType* dtypep = nodep->childDTypep(); dtypep->unlinkFrBack();
	    if (backp->castTypedef()) { // A typedef doesn't need us to make yet another level of typedefing
		// For typedefs just remove the AstRefDType level of abstraction
		nodep->replaceWith(dtypep);
		nodep->deleteTree(); nodep=NULL;
		return;
	    } else {
		defp = new AstTypedef(nodep->fileline(), nodep->name(), NULL, VFlagChildDType(), dtypep);
		m_implTypedef.insert(make_pair(make_pair(nodep->containerp(), defp->name()), defp));
		backp->addNextHere(defp);
	    }
	}
	nodep->replaceWith(new AstRefDType(nodep->fileline(), defp->name()));
	nodep->deleteTree(); nodep=NULL;
    }

    virtual void visit(AstTypedefFwd* nodep, AstNUser*) {
	// We only needed the forward declaration in order to parse correctly.
	// We won't even check it was ever really defined, as it might have been in a header
	// file referring to a module we never needed
	nodep->unlinkFrBack()->deleteTree();
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	cleanFileline(nodep);
	//
	m_modp = nodep;
	m_valueModp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
	m_valueModp = NULL;
    }
    void visitIterateNoValueMod(AstNode* nodep) {
	// Iterate a node which shouldn't have any local variables moved to an Initial
	cleanFileline(nodep);
	//
	AstNodeModule* upperValueModp = m_valueModp;
	m_valueModp = NULL;
	nodep->iterateChildren(*this);
	m_valueModp = upperValueModp;
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	visitIterateNoValueMod(nodep);
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	m_inAlways = true;
	visitIterateNoValueMod(nodep);
	m_inAlways = false;
    }
    virtual void visit(AstPslCover* nodep, AstNUser*) {
	visitIterateNoValueMod(nodep);
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	cleanFileline(nodep);
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkParseVisitor(AstNetlist* rootp) {
	m_varp = NULL;
	m_modp = NULL;
	m_ftaskp = NULL;
	m_dtypep = NULL;
	m_inAlways = false;
	m_inGenerate = false;
	m_needStart = false;
	m_valueModp = NULL;
	rootp->accept(*this);
    }
    virtual ~LinkParseVisitor() {}
};

//######################################################################
// Link class functions

void V3LinkParse::linkParse(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkParseVisitor visitor(rootp);
    V3Global::dumpCheckGlobalTree("linkparse.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
