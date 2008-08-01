//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// Link TRANSFORMATIONS:
//	Top-down traversal
//	    Cells:
//		Connect pins
//	    VarRef's:
//		Link to var they reference
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Link.h"
#include "V3SymTable.h"
#include "V3Ast.h"

//######################################################################
// Link state, as a visitor of each AstNode

class LinkVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist:
    //   AstModule::userp()	// V3SymTable*    Module's Symbol table
    //   AstNodeFTask::userp()	// V3SymTable*    Local Symbol table
    //   AstBegin::userp()	// V3SymTable*    Local Symbol table
    //   AstVar::userp()	// V3SymTable*    Table used to create this variable

    // ENUMS
    enum IdState {		// Which loop through the tree
	ID_FIND,		// Find all identifiers and add to lists
	ID_PARAM,		// Move parameters to cell definitions
	ID_RESOLVE};		// Resolve all identifiers and report errors

    // STATE
    // Below state needs to be preserved between each module call.
    AstModule*	m_modp;		// Current module
    IdState	m_idState;	// Id linking mode (find or resolve)
    int		m_paramNum;	// Parameter number, for position based connection
    V3SymTable* m_curVarsp;	// Symbol table of variables and tasks under table we're inserting into
    V3SymTable* m_cellVarsp;	// Symbol table of variables under cell's module
    int		m_beginNum;	// Begin block number, 0=none seen
    vector<V3SymTable*> m_delSymps;	// Symbol tables to delete

    //int debug() { return 9; }

    // METHODS
    void linkVarName (AstVarRef* nodep) {
	if (!nodep->varp()) {
	    AstVar* varp = m_curVarsp->findIdName(nodep->name())->castVar();
	    nodep->varp(varp);
	}
    }

    const char* varTextType(AstNode* nodep) {
	const char* what = "node";
	if (nodep->castVar()) what = "variable";
	else if (nodep->castCell()) what = "cell";
	else if (nodep->castTask()) what = "task";
	else if (nodep->castFunc()) what = "function";
	return what;
    }

    void createImplicitVar (AstVarRef* forrefp, bool noWarn) {
	// Create implicit after warning
	linkVarName(forrefp);
	if (!forrefp->varp()) {
	    if (!noWarn) forrefp->v3warn(IMPLICIT,"Signal definition not found, creating implicitly: "<<forrefp->prettyName());
	    AstVar* newp = new AstVar (forrefp->fileline(), AstVarType::WIRE,
				       forrefp->name());
	    newp->trace(m_modp->modTrace());
	    m_modp->addStmtp(newp);
	    // Link it to signal list
	    IdState old_id = m_idState;
	    m_idState = ID_FIND;
	    newp->accept(*this);
	    m_idState = old_id;
	}
    }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNode::userClearTree();
	// Look at all modules, and store pointers to all module names
	for (AstModule* modp = v3Global.rootp()->modulesp(); modp; modp=modp->nextp()->castModule()) {
	    V3SymTable* symp = new V3SymTable(NULL);
	    m_delSymps.push_back(symp);
	    modp->userp(symp);
	}
	// And recurse...
	m_idState = ID_FIND;
	nodep->iterateChildren(*this);
	m_idState = ID_PARAM;
	nodep->iterateChildren(*this);
	m_idState = ID_RESOLVE;
	nodep->iterateChildren(*this);
	nodep->checkTree();
    }

    virtual void visit(AstModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	UINFO(2,"Link Module: "<<nodep<<endl);
	m_modp = nodep;
	// This state must be save/restored in the cell visitor function
	m_curVarsp = nodep->userp()->castSymTable();
	if (!m_curVarsp) nodep->v3fatalSrc("NULL");
	m_cellVarsp = NULL;
	m_paramNum = 0;
	m_beginNum = 0;
	nodep->iterateChildren(*this);
	// Prep for next
	m_curVarsp = NULL;
	m_modp = NULL;
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Var: Remember its name for later resolution
	if (!m_curVarsp) nodep->v3fatalSrc("Var not under module??\n");
	nodep->iterateChildren(*this);
	if (m_idState==ID_FIND) {
	    // We used modTrace before leveling, and we may now
	    // want to turn it off now that we know the levelizations
	    if (v3Global.opt.traceDepth()
		&& (m_modp->level()-1) > v3Global.opt.traceDepth()) {
		m_modp->modTrace(false);
		nodep->trace(false);
	    }
	    // Find under either a task or the module's vars
	    AstNode* findidp = m_curVarsp->findIdName(nodep->name());
	    AstVar* findvarp = findidp->castVar();
	    bool ins=false;
	    if (!findidp) {
		ins=true;
	    } else if (!findvarp) {
		nodep->v3error("Unsupported in C: Variable has same name as "
			       <<varTextType(findidp)<<": "<<nodep->prettyName());
	    } else if (findvarp != nodep) {
		UINFO(4,"DupVar: "<<nodep<<" ;; "<<findvarp<<endl);
		if (findvarp->userp() == m_curVarsp) {  // Only when on same level
		    if ((findvarp->isIO() && nodep->isSignal())
			|| (findvarp->isSignal() && nodep->isIO())) {
			findvarp->combineType(nodep);
			findvarp->fileline()->warnStateInherit(nodep->fileline());
			nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    } else {
			nodep->v3error("Duplicate declaration of signal: "<<nodep->prettyName());
			findvarp->v3error("... Location of original declaration");
		    }
		} else {
		    // User can disable the message at either point
		    if (!nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
			&& !findvarp->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
			nodep->v3warn(VARHIDDEN,"Declaration of signal hides declaration in upper scope: "<<nodep->name());
			findvarp->v3warn(VARHIDDEN,"... Location of original declaration");
		    }
		    ins = true;
		}
	    }
	    if (ins) {
		m_curVarsp->insert(nodep->name(), nodep);
		nodep->userp(m_curVarsp);
		if (nodep->isGParam()) {
		    m_paramNum++;
		    m_curVarsp->insert("__paramNumber"+cvtToStr(m_paramNum), nodep);
		}
	    }
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	if (m_idState==ID_RESOLVE && !nodep->varp()) {
	    linkVarName(nodep);
	    if (!nodep->varp()) {
		nodep->v3error("Can't find definition of signal: "<<nodep->prettyName());
		createImplicitVar (nodep, true);  // So only complain once
	    }
	}
	nodep->iterateChildren(*this);
    }
    //virtual void visit(AstVarXRef* nodep, AstNUser*) {
    // See LinkDotVisitor
    //}

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// NodeTask: Remember its name for later resolution
	if (!m_curVarsp) nodep->v3fatalSrc("Function/Task not under module??\n");
	// Remember the existing symbol table scope
	V3SymTable* upperVarsp = m_curVarsp;
	{
	    // Create symbol table for the task's vars
	    if (V3SymTable* localVarsp = nodep->userp()->castSymTable()) {
		m_curVarsp = localVarsp;
	    } else {
		m_curVarsp = new V3SymTable(upperVarsp);
		m_delSymps.push_back(m_curVarsp);
		nodep->userp(m_curVarsp);
	    }
	    // Convert the func's range to the output variable
	    // This should probably be done in the Parser instead, as then we could
	    // just attact normal signal attributes to it.
	    if (AstFunc* funcp = nodep->castFunc()) {
		if (!funcp->fvarp()->castVar()) {
		    AstRange* rangep = funcp->fvarp()->castRange();
		    if (rangep) rangep->unlinkFrBack();
		    AstVar* newvarp = new AstVar(nodep->fileline(), AstVarType::OUTPUT, nodep->name(), rangep);
		    newvarp->isSigned(funcp->isSigned());
		    newvarp->funcReturn(true);
		    newvarp->trace(false);  // Not user visible
		    newvarp->attrIsolateAssign(funcp->attrIsolateAssign());
		    funcp->addFvarp(newvarp);
		    // Explicit insert required, as the var name shadows the upper level's task name
		    m_curVarsp->insert(newvarp->name(), newvarp);
		}
	    }
	    nodep->iterateChildren(*this);
	}
	m_curVarsp = upperVarsp;
	if (m_idState==ID_FIND) {
	    AstNode* findidp = m_curVarsp->findIdName(nodep->name());
	    AstNodeFTask* findtaskp = findidp->castNodeFTask();
	    if (!findidp) {
		m_curVarsp->insert(nodep->name(), nodep);
	    } else if (!findtaskp) {
		nodep->v3error("Unsupported in C: Task/function has same name as "
			       <<varTextType(findidp)<<": "<<nodep->prettyName());
	    } else if (findtaskp!=nodep) {
		nodep->v3error("Duplicate declaration of task/function: "<<nodep->prettyName());
	    }
	}
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	// Link variables underneath blocks
	// Remember the existing symbol table scope
	V3SymTable* upperVarsp = m_curVarsp;
	// Rename "genblk"s to include a number
	// All blocks are numbered in the standard, IE we start with "genblk1" even if only one.
	UINFO(8,"   "<<nodep<<endl);
	if (m_idState==ID_FIND && nodep->name() == "genblk") {
	    ++m_beginNum;
	    nodep->name(nodep->name()+cvtToStr(m_beginNum));
	}
	// Recurse
	int oldNum = m_beginNum;
	m_beginNum = 0;
	{
	    // Create symbol table for the task's vars
	    if (V3SymTable* localVarsp = nodep->userp()->castSymTable()) {
		m_curVarsp = localVarsp;
	    } else {
		m_curVarsp = new V3SymTable(upperVarsp);
		m_delSymps.push_back(m_curVarsp);
		nodep->userp(m_curVarsp);
	    }
	    nodep->iterateChildren(*this);
	}
	m_curVarsp = upperVarsp;
	m_beginNum = oldNum;
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// NodeFTaskRef: Resolve its reference
	if (m_idState==ID_RESOLVE && !nodep->taskp()) {
	    if (nodep->dotted() == "") {
		AstNodeFTask* taskp = m_curVarsp->findIdName(nodep->name())->castNodeFTask();
		if (!taskp) { nodep->v3error("Can't find definition of task/function: "<<nodep->prettyName()); }
		nodep->taskp(taskp);
	    }
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstCell* nodep, AstNUser*) {
	// Cell: Resolve its filename.  If necessary, parse it.
	if (m_idState==ID_FIND) {
	    // Add to list of all cells, for error checking and defparam's
	    AstNode* findidp = m_curVarsp->findIdName(nodep->name());
	    AstCell* findcellp = findidp->castCell();
	    if (!findidp) {
		m_curVarsp->insert(nodep->name(), nodep);
	    } else if (!findcellp) {
		nodep->v3error("Unsupported in C: Cell has same name as "
			       <<varTextType(findidp)<<": "<<nodep->prettyName());
	    } else if (findcellp != nodep) {
		nodep->v3error("Duplicate name of cell: "<<nodep->prettyName());
	    }
	}
	if (!nodep->modp()) {
	    nodep->v3fatalSrc("Cell has unlinked module"); // V3LinkCell should have errored out
	}
	else {
	    // Need to pass the module info to this cell, so we can link up the pin names
	    m_cellVarsp = nodep->modp()->userp()->castSymTable();
	    UINFO(4,"(Backto) Link Cell: "<<nodep<<endl);
	    //if (debug()) { nodep->dumpTree(cout,"linkcell:"); }
	    //if (debug()) { nodep->modp()->dumpTree(cout,"linkcemd:"); }
	    nodep->iterateChildren(*this);
	    m_cellVarsp = NULL;
	}
	// Parent module inherits child's publicity
	// This is done bottom up in the LinkBotupVisitor stage
    }

    virtual void visit(AstPort* nodep, AstNUser*) {
	// Port: Stash the pin number
	if (!m_curVarsp) nodep->v3fatalSrc("Port not under module??\n");
	if (m_idState==ID_PARAM) {
	    // Need to set pin numbers after varnames are created
	    // But before we do the final resolution based on names
	    AstVar* refp = m_curVarsp->findIdName(nodep->name())->castVar();
	    if (!refp) {
		nodep->v3error("Input/output/inout declaration not found for port: "<<nodep->prettyName());
	    } else if (!refp->isIO()) {
		nodep->v3error("Pin is not a in/out/inout: "<<nodep->prettyName());
	    } else {
		m_curVarsp->insert("__pinNumber"+cvtToStr(nodep->pinNum()), refp);
	    }
	    // Ports not needed any more
	    nodep->unlinkFrBack()->deleteTree();  nodep=NULL;
	}
    }

    void pinImplicitExprRecurse(AstNode* nodep) {
	// Under a pin, Check interconnect expression for a pin reference or a concat.
	// Create implicit variable as needed
	if (AstVarRef* varrefp = nodep->castVarRef()) {
	    // To prevent user errors, we should only do single bit
	    // implicit vars, however some netlists (MIPS) expect single
	    // bit implicit wires to get created with range 0:0 etc.
	    //if (!nodep->modVarp()->rangep()) ...
	    createImplicitVar(varrefp, false);
	}
	else if (AstConcat* concp = nodep->castConcat()) {
	    pinImplicitExprRecurse(concp->lhsp());
	    pinImplicitExprRecurse(concp->rhsp());
	}
    }

    virtual void visit(AstPin* nodep, AstNUser*) {
	// Pin: Link to submodule's pin
	if (!m_cellVarsp) nodep->v3fatalSrc("Pin not under cell?\n");
	if (m_idState==ID_RESOLVE && !nodep->modVarp()) {
	    AstVar* refp = m_cellVarsp->findIdName(nodep->name())->castVar();
	    if (!refp) {
		nodep->v3error("Pin not found: "<<nodep->prettyName());
	    } else if (!refp->isIO() && !refp->isParam()) {
		nodep->v3error("Pin is not a in/out/inout/param: "<<nodep->prettyName());
	    } else {
		nodep->modVarp(refp);
	    }
	}
	// Deal with implicit definitions
	if (m_idState==ID_RESOLVE && nodep->modVarp()
	    && !nodep->svImplicit()) {   // SV 19.11.3: .name pins don't allow implicit decls
	    pinImplicitExprRecurse(nodep->exprp());
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Deal with implicit definitions
	// We used to nodep->allowImplicit() here, but it turns out
	// normal "assigns" can also make implicit wires.  Yuk.
	if (AstVarRef* forrefp = nodep->lhsp()->castVarRef()) {
	    createImplicitVar(forrefp, false);
	}
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstDefParam* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_idState==ID_PARAM) {
	    AstNode* findidp = m_curVarsp->findIdName(nodep->path());
	    AstCell* cellp = findidp->castCell();
	    if (!cellp) {
		nodep->v3error("In defparam, cell "<<nodep->path()<<" never declared");
	    } else {
		AstNode* exprp = nodep->rhsp()->unlinkFrBack();
		UINFO(9,"Defparam cell "<<nodep->path()<<"."<<nodep->name()
		      <<" <= "<<exprp<<endl);
		// Don't need to check the name of the defparam exists.  V3Param does.
		AstPin* pinp = new AstPin (nodep->fileline(),
					   -1, // Pin# not relevant
					   nodep->name(),
					   exprp);
		cellp->addParamsp(pinp);
		nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    }
	}
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkVisitor(AstNetlist* rootp) {
	m_curVarsp = NULL;
	m_cellVarsp = NULL;
	m_modp = NULL;
	m_paramNum = 0;
	m_beginNum = 0;
	//
	rootp->accept(*this);
    }
    virtual ~LinkVisitor() {
	for (vector<V3SymTable*>::iterator it = m_delSymps.begin(); it != m_delSymps.end(); ++it) {
	    delete (*it);
	}
    }
};

//######################################################################
// Link class functions

void V3Link::link(AstNetlist* rootp) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    LinkVisitor visitor(rootp);
}
