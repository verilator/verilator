// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dead code elimination
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
// DEAD TRANSFORMATIONS:
//	Remove any unreferenced modules
//	Remove any unreferenced variables
//
// TODO: A graph would make the process of circular and interlinked
// dependencies easier to resolve.
// NOTE: If redo this, consider using maybePointedTo()/broken() ish scheme
// instead of needing as many visitors.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <vector>
#include <map>

#include "V3Global.h"
#include "V3Dead.h"
#include "V3Ast.h"

//######################################################################

class DeadModVisitor : public AstNVisitor {
    // In a module that is dead, cleanup the in-use counts of the modules
private:
    // NODE STATE
    // ** Shared with DeadVisitor **
    // VISITORS
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	nodep->modp()->user1(nodep->modp()->user1() - 1);
    }
    //-----
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}  // Accelerate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    DeadModVisitor(AstNodeModule* nodep) {
	nodep->accept(*this);
    }
    virtual ~DeadModVisitor() {}
};

//######################################################################
// Dead state, as a visitor of each AstNode

class DeadVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire Netlist:
    //  AstNodeModule::user1()	-> int. Count of number of cells referencing this module.
    //  AstVar::user1()		-> int. Count of number of references
    //  AstVarScope::user1()	-> int. Count of number of references
    //  AstNodeDType::user1()	-> int. Count of number of references
    AstUser1InUse	m_inuser1;

    // TYPES
    typedef multimap<AstVarScope*,AstNodeAssign*>	AssignMap;

    // STATE
    AstNodeModule*		m_modp;		// Current module
    vector<AstNode*>		m_varEtcsp;	// List of all encountered to avoid another loop through tree
    vector<AstVarScope*>	m_vscsp;	// List of all encountered to avoid another loop through tree
    AssignMap			m_assignMap;	// List of all simple assignments for each variable
    bool			m_elimUserVars;	// Allow removal of user's vars
    bool			m_elimDTypes;	// Allow removal of DTypes
    bool			m_sideEffect;	// Side effects discovered in assign RHS

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void checkAll(AstNode* nodep) {
	if (nodep != nodep->dtypep()) {  // NodeDTypes reference themselves
	    if (AstNode* subnodep = nodep->dtypep()) subnodep->user1Inc();
	}
	if (AstNode* subnodep = nodep->getChildDTypep()) subnodep->user1Inc();
    }
    void checkDType(AstNodeDType* nodep) {
	if (!nodep->generic()  // Don't remove generic types
	    && m_elimDTypes  // dtypes stick around until post-widthing
	    && !nodep->castMemberDType() // Keep member names iff upper type exists
	    ) {
	    m_varEtcsp.push_back(nodep);
	}
	if (AstNode* subnodep = nodep->virtRefDTypep()) subnodep->user1Inc();
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	checkAll(nodep);
	m_modp = NULL;
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	nodep->modp()->user1Inc();
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	if (nodep->varScopep()) {
	    nodep->varScopep()->user1Inc();
	    nodep->varScopep()->varp()->user1Inc();
	}
	if (nodep->varp()) {
	    nodep->varp()->user1Inc();
	}
	if (nodep->packagep()) {
	    nodep->packagep()->user1Inc();
	}
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	if (nodep->packagep()) {
	    nodep->packagep()->user1Inc();
	}
    }
    virtual void visit(AstRefDType* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkDType(nodep);
	checkAll(nodep);
	if (nodep->packagep()) {
	    nodep->packagep()->user1Inc();
	}
    }
    virtual void visit(AstNodeDType* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkDType(nodep);
	checkAll(nodep);
    }
    virtual void visit(AstEnumItemRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	if (nodep->packagep()) {
	    nodep->packagep()->user1Inc();
	}
    }
    virtual void visit(AstTypedef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	// Don't let packages with only public variables disappear
	// Normal modules may disappear, e.g. if they are parameterized then removed
	if (nodep->attrPublic() && m_modp && m_modp->castPackage()) m_modp->user1Inc();
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	if (mightElim(nodep->varp())) {
	    m_vscsp.push_back(nodep);
	}
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkAll(nodep);
	if (nodep->isSigPublic() && m_modp && m_modp->castPackage()) m_modp->user1Inc();
	if (mightElim(nodep)) {
	    m_varEtcsp.push_back(nodep);
	}
    }

    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// See if simple assignments to variables may be eliminated because that variable is never used.
	// Similar code in V3Life
	m_sideEffect = false;
	nodep->rhsp()->iterateAndNext(*this);
	checkAll(nodep);
	// Has to be direct assignment without any EXTRACTing.
	AstVarRef* varrefp = nodep->lhsp()->castVarRef();
	if (varrefp && !m_sideEffect
	    && varrefp->varScopep()) {	// For simplicity, we only remove post-scoping
	    m_assignMap.insert(make_pair(varrefp->varScopep(), nodep));
	    checkAll(varrefp);  // Must track reference to dtype()
	} else {  // Track like any other statement
	    nodep->lhsp()->iterateAndNext(*this);
	}
	checkAll(nodep);
    }

    //-----
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (nodep->isOutputter()) m_sideEffect=true;
	nodep->iterateChildren(*this);
	checkAll(nodep);
    }

    // METHODS
    void deadCheckMod() {
	// Kill any unused modules
	// V3LinkCells has a graph that is capable of this too, but we need to do it
	// after we've done all the generate blocks
	for (bool retry=true; retry; ) {
	    retry=false;
	    AstNodeModule* nextmodp;
	    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=nextmodp) {
		nextmodp = modp->nextp()->castNodeModule();
		if (modp->level()>2	&& modp->user1()==0 && !modp->internal()) {
		    // > 2 because L1 is the wrapper, L2 is the top user module
		    UINFO(4,"  Dead module "<<modp<<endl);
		    // And its children may now be killable too; correct counts
		    // Recurse, as cells may not be directly under the module but in a generate
		    DeadModVisitor visitor(modp);
		    modp->unlinkFrBack()->deleteTree(); modp=NULL;
		    retry = true;
		}
	    }
	}
    }
    bool mightElim(AstVar* nodep) {
	return (!nodep->isSigPublic()	// Can't elim publics!
		&& !nodep->isIO()
		&& (nodep->isTemp()
		    || (nodep->isParam() && !nodep->isTrace())
		    || m_elimUserVars));  // Post-Trace can kill most anything
    }
    void deadCheckVar() {
	// Delete any unused varscopes
	for (vector<AstVarScope*>::iterator it = m_vscsp.begin(); it!=m_vscsp.end(); ++it) {
	    AstVarScope* vscp = *it;
	    if (vscp->user1() == 0) {
		UINFO(4,"  Dead "<<vscp<<endl);
		pair <AssignMap::iterator,AssignMap::iterator> eqrange = m_assignMap.equal_range(vscp);
		for (AssignMap::iterator it = eqrange.first; it != eqrange.second; ++it) {
		    AstNodeAssign* assp = it->second;
		    UINFO(4,"    Dead assign "<<assp<<endl);
		    assp->unlinkFrBack()->deleteTree(); assp=NULL;
		}
		vscp->unlinkFrBack()->deleteTree(); vscp=NULL;
	    }
	}
	for (vector<AstNode*>::iterator it = m_varEtcsp.begin(); it!=m_varEtcsp.end(); ++it) {
	    if ((*it)->user1() == 0) {
		UINFO(4,"  Dead "<<(*it)<<endl);
		(*it)->unlinkFrBack()->deleteTree(); (*it)=NULL;
	    }
	}
    }

public:
    // CONSTRUCTORS
    DeadVisitor(AstNetlist* nodep, bool elimUserVars, bool elimDTypes) {
	m_modp = NULL;
	m_elimUserVars = elimUserVars;
	m_elimDTypes = elimDTypes;
	m_sideEffect = false;
	// Prepare to remove some datatypes
	nodep->typeTablep()->clearCache();
	// Operate on whole netlist
	nodep->accept(*this);
	deadCheckVar();
	// Modules after vars, because might be vars we delete inside a mod we delete
	deadCheckMod();
	// We may have removed some datatypes, cleanup
	nodep->typeTablep()->repairCache();
    }
    virtual ~DeadVisitor() {}
};

//######################################################################
// Dead class functions

void V3Dead::deadifyModules(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DeadVisitor visitor (nodep, false, false);
    V3Global::dumpCheckGlobalTree("deadModules.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
void V3Dead::deadifyDTypes(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DeadVisitor visitor (nodep, false, true);
    V3Global::dumpCheckGlobalTree("deadDType.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
void V3Dead::deadifyAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DeadVisitor visitor (nodep, true, true);
    V3Global::dumpCheckGlobalTree("deadAll.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
