// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for task nodes
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
// V3Task's Transformations:
//		
// Each module:
//	Look for TASKREF
//	    Insert task's statements into the referrer
//	Look for TASKs
//	    Remove them, they're inlined
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>

#include "V3Global.h"
#include "V3Task.h"
#include "V3Inst.h"
#include "V3Ast.h"

//######################################################################

class TaskStateVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Output:
    //   AstNodeFTask::user3p	// AstScope* this FTask is under

    // TYPES
    typedef std::map<pair<AstScope*,AstVar*>,AstVarScope*> VarToScopeMap;
    // MEMBERS
    VarToScopeMap	m_varToScopeMap;	// Map for Var -> VarScope mappings
public:
    // METHODS
    AstScope* getScope(AstNodeFTask* nodep) {
	AstScope* scopep = nodep->user3p()->castNode()->castScope();
	if (!scopep) nodep->v3fatalSrc("No scope for function");
	return scopep;
    }
    AstVarScope* findVarScope(AstScope* scopep, AstVar* nodep) {
	VarToScopeMap::iterator iter = m_varToScopeMap.find(make_pair(scopep,nodep));
	if (iter == m_varToScopeMap.end()) nodep->v3fatalSrc("No scope for var");
	return iter->second;
    }
private:
    // VISITORS
    virtual void visit(AstScope* nodep, AstNUser*) {
	// Each FTask is unique per-scope, so AstNodeFTaskRefs do not need
	// pointers to what scope the FTask is to be invoked under.
	// However, to create variables, we need to track the scopes involved.
	// Find all var->varscope mappings, for later cleanup
	for (AstNode* stmtp = nodep->varsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVarScope* vscp = stmtp->castVarScope()) {
		if (vscp->varp()->isFuncLocal()) {
		    UINFO(9,"   funcvsc "<<vscp<<endl);
		    m_varToScopeMap.insert(make_pair(make_pair(nodep, vscp->varp()), vscp));
		}
	    }
	}
	// Likewise, all FTask->scope mappings
	for (AstNode* stmtp = nodep->blocksp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstNodeFTask* taskp = stmtp->castNodeFTask()) {
		taskp->user3p(nodep);
	    }
	}
	// No iterateChildren for speed
    }
    //--------------------
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}	// Speedup
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    TaskStateVisitor(AstNode* nodep) {
	AstNode::user3ClearTree();
	nodep->iterateAndNext(*this, NULL);
    }
    virtual ~TaskStateVisitor() {}
};

//######################################################################

class TaskRelinkVisitor : public AstNVisitor {
    // Replace varrefs with new var pointer
private:
    // NODE STATE
    //  Input:
    //   AstVar::user2p		// AstVarScope* to replace varref with

    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Similar code in V3Inline
	if (nodep->varp()->user2p()) { // It's being converted to a alias.
	    UINFO(9, "    relinkVar "<<(void*)nodep->varp()->user2p()<<" "<<nodep<<endl);
	    AstVarScope* newvscp = nodep->varp()->user2p()->castNode()->castVarScope();
	    if (!newvscp) nodep->v3fatalSrc("Null?\n");
	    nodep->varScopep(newvscp);
	    nodep->varp(nodep->varScopep()->varp());
	    nodep->name(nodep->varp()->name());
	}
	nodep->iterateChildren(*this);
    }

    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    TaskRelinkVisitor(AstNode* nodep) {
	nodep->iterateAndNext(*this, NULL);
    }
    virtual ~TaskRelinkVisitor() {}
};

//######################################################################
// Task state, as a visitor of each AstNode

class TaskVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Each module:
    //  AstNodeFTask::user	// True if its been expanded
    // Each funccall
    //  AstVar::user2p		// AstVarScope* to replace varref with
    // STATE
    TaskStateVisitor* m_statep;	// Common state between visitors
    AstModule*	m_modp;		// Current module
    AstScope*	m_scopep;	// Current scope
    AstNode*	m_lastStmtp;	// Proceeding statement
    int		m_modNCalls;	// Incrementing func # for making symbols
    //int debug() { return 9; }

    // METHODS
    AstVarScope* createVarScope(AstVar* invarp, const string& name) {
	// We could create under either the ref's scope or the ftask's scope.
	// It shouldn't matter, as they are only local variables.
	// We choose to do it under whichever called this function, which results
	// in more cache locality.
	AstVar* newvarp = new AstVar (invarp->fileline(), AstVarType::BLOCKTEMP,
				      name, invarp);
	newvarp->funcLocal(false);
	m_modp->addStmtp(newvarp);
	AstVarScope* newvscp = new AstVarScope (newvarp->fileline(), m_scopep, newvarp);
	m_scopep->addVarp(newvscp);
	return newvscp;
    }

    AstNode* createInlinedFTask(AstNodeFTaskRef* refp, string namePrefix, AstVarScope* outvscp) {
	// outvscp is the variable for functions only, if NULL, it's a task
	if (!refp->taskp()) refp->v3fatalSrc("Unlinked?");
	AstNode* newbodysp = refp->taskp()->stmtsp()->cloneTree(true);  // Maybe NULL
	AstNode* beginp = new AstComment(refp->fileline(), (string)("Function: ")+refp->name());
	if (newbodysp) beginp->addNext(newbodysp);
	if (debug()>=9) { beginp->dumpTree(cout,"-newbody:"); }
	//
	// Create input variables
	AstNode::user2ClearTree();
	AstNode* pinp = refp->pinsp();
	AstNode* nextpinp = pinp;
	AstNode* nextstmtp;
	for (AstNode* stmtp = newbodysp; stmtp; pinp=nextpinp, stmtp=nextstmtp) {
	    nextstmtp = stmtp->nextp();
	    if (AstVar* portp = stmtp->castVar()) {
		portp->unlinkFrBack();  // Remove it from the clone (not original)
		pushDeletep(portp);
		if (portp->isIO()) {
		    if (pinp==NULL) {
			refp->v3error("Too few arguments in function call");
			pinp = new AstConst(refp->fileline(), 0);
			m_modp->addStmtp(pinp);  // For below unlink
		    }
		    UINFO(9, "     Port "<<portp<<endl);
		    UINFO(9, "      pin "<<pinp<<endl);
		    //
		    nextpinp = pinp->nextp();
		    pinp->unlinkFrBack();   // Relinked to assignment below
		    //
		    if (portp->isTristate()) {
			refp->v3error("Unsupported: Inouts in functions/tasks");
		    }
		    else if (portp->isOutput() && outvscp) {
			refp->v3error("Outputs not allowed in function declarations");
		    }
		    else if (portp->isOutput()) {
			// Make output variables
			// Correct lvalue; we didn't know when we linked
			if (AstVarRef* varrefp = pinp->castVarRef()) {
			    varrefp->lvalue(true);
			} else {
			    pinp->v3error("Unsupported: Task output pin connected to non-variable");
			}
			// Even if it's referencing a varref, we still make a temporary
			// Else task(x,x,x) might produce incorrect results
			AstVarScope* outvscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
			portp->user2p(outvscp);
			AstAssign* assp = new AstAssign (pinp->fileline(),
							 pinp,
							 new AstVarRef(outvscp->fileline(), outvscp, false));
			// Put assignment BEHIND of all other statements
			beginp->addNext(assp);
		    }
		    else if (portp->isInput()) {
			// Make input variable
			AstVarScope* inVscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
			portp->user2p(inVscp);
			AstAssign* assp = new AstAssign (pinp->fileline(),
							 new AstVarRef(inVscp->fileline(), inVscp, true),
							 pinp);
			// Put assignment in FRONT of all other statements
			if (AstNode* afterp = beginp->nextp()) {
			    afterp->unlinkFrBackWithNext();
			    assp->addNext(afterp);
			}
			beginp->addNext(assp);
		    }
		}
		else { // Var is not I/O
		    // Move it to a new localized variable
		    AstVarScope* localVscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
		    portp->user2p(localVscp);
		}
	    }
	}
	if (pinp!=NULL) refp->v3error("Too many arguments in function call");
	// Create function output variables
	if (outvscp) {
	    //UINFO(0, "setflag on "<<funcp->fvarp()<<" to "<<outvscp<<endl);
	    refp->taskp()->castFunc()->fvarp()->user2p(outvscp);
	}
	// Replace variable refs
	TaskRelinkVisitor visit (beginp);
	//
	if (debug()>=9) { beginp->dumpTree(cout,"-iotask: "); }
	return beginp;
    }


    AstCFunc* makeUserFunc(AstNodeFTask* nodep) {
	// Given a already cloned node, make a public C function.
	// Probably some of this work should be done later, but...
	// should the type of the function be bool/uint32/64 etc (based on lookup) or IData?
	AstNode::user2ClearTree();
	AstVar* rtnvarp = NULL;
	AstVarScope* rtnvscp = NULL;
	if (nodep->castFunc()) {
	    AstVar* portp = NULL;
	    if (NULL!=(portp = nodep->castFunc()->fvarp()->castVar())) {
		if (!portp->isFuncReturn()) nodep->v3error("Not marked as function return var");
		if (portp->isWide()) nodep->v3error("Unsupported: Public functions/tasks with inputs or outputs > 64 bits wide.");
		portp->unlinkFrBack();
		rtnvarp = portp;
		rtnvarp->funcLocal(true);
		rtnvscp = new AstVarScope (rtnvarp->fileline(), m_scopep, rtnvarp);
		m_scopep->addVarp(rtnvscp);
		rtnvarp->user2p(rtnvscp);
	    } else {
		nodep->v3fatalSrc("function without function output variable");
	    }
	}
	AstCFunc* funcp = new AstCFunc(nodep->fileline(), nodep->name(),
				       m_scopep,
				       (rtnvarp?rtnvarp->cType():""));
	if (rtnvarp) funcp->addArgsp(rtnvarp);
	funcp->dontCombine(true);
	funcp->funcPublic(true);

	// We need to get a pointer to all of our variables (may have eval'ed something else earlier)
	funcp->addInitsp(new AstCStmt(nodep->fileline(),
				      string("    ")+v3Global.opt.prefix()+"__Syms::init(__VlSymsp);\n"));

	// Create list of arguments and move to function
	for (AstNode* nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp=nextp) {
	    nextp = stmtp->nextp();
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO()) {
		    // Move it to new function
		    portp->unlinkFrBack();
		    portp->funcLocal(true);
		    funcp->addArgsp(portp);
		    if (portp->isWide()) {
			// As we don't want to export our WData arrays to users,
			// and casting to sc_bv's is ugly, we'll just...
			nodep->v3error("Unsupported: Public functions/tasks with inputs or outputs > 64 bits wide.");
		    }
		} else {
		    // "Normal" variable, mark inside function
		    portp->funcLocal(true);
		}
		AstVarScope* newvscp = new AstVarScope (portp->fileline(), m_scopep, portp);
		m_scopep->addVarp(newvscp);
		portp->user2p(newvscp);
	    }
	}
	// Move body
	AstNode* bodysp = nodep->stmtsp();
	if (bodysp) { bodysp->unlinkFrBackWithNext(); funcp->addStmtsp(bodysp); }
	// Return statement
	if (rtnvscp) { 
	    funcp->addFinalsp(new AstCReturn(rtnvscp->fileline(),
					     new AstVarRef(rtnvscp->fileline(), rtnvscp, false)));
	}
	// Replace variable refs
	TaskRelinkVisitor visit (funcp);
	// Delete rest of cloned task and return new func
	pushDeletep(nodep); nodep=NULL;
	if (debug()>=9) { funcp->dumpTree(cout,"-userFunc: "); }
	return funcp;
    }

    void iterateIntoFTask(AstNodeFTask* nodep) {
	// Iterate into the FTask we are calling.  Note it may be under a different
	// scope then the caller, so we need to restore state.
	AstScope* oldscopep = m_scopep;
	m_scopep = m_statep->getScope(nodep);
	nodep->accept(*this);
	m_scopep = oldscopep;
    }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_lastStmtp = NULL;
	m_modNCalls = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	m_scopep = nodep;
	m_lastStmtp = NULL;
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }
    virtual void visit(AstTaskRef* nodep, AstNUser*) {
	iterateIntoFTask(nodep->taskp());	// First, do hierarchical funcs
	UINFO(4," Task REF   "<<nodep<<endl);
	if (debug()>=9) { nodep->dumpTree(cout,"-inltask:"); }
	// Create cloned statements
	string namePrefix = "__Vtask_"+nodep->taskp()->shortName()+"__"+cvtToStr(m_modNCalls++);
	AstNode* beginp = createInlinedFTask(nodep, namePrefix, NULL);
	// Replace the ref
	nodep->replaceWith(beginp);
	nodep->deleteTree(); nodep=NULL;
    }
    virtual void visit(AstFuncRef* nodep, AstNUser*) {
	UINFO(4," Func REF   "<<nodep<<endl);
	if (debug()>=9) { m_lastStmtp->dumpTree(cout,"-prestmt:"); }
	// First, do hierarchical funcs
	AstFunc* funcp = nodep->taskp()->castFunc();
	if (!funcp) nodep->v3fatalSrc("unlinked");
	AstNode* insertAtp = m_lastStmtp;
	if (AstAssignW* awp = insertAtp->castAssignW()) {
	    // Wire assigns must become always statements to deal with insertion
	    // of multiple statements.  Perhaps someday make all wassigns into always's?
	    AstNode* lhsp = awp->lhsp()->unlinkFrBack();
	    AstNode* rhsp = awp->rhsp()->unlinkFrBack();
	    AstNode* assignp = new AstAssign (awp->fileline(), lhsp, rhsp);
	    AstNode* alwaysp = new AstAlways (awp->fileline(), NULL, assignp);
	    m_lastStmtp = assignp; insertAtp = assignp;
	    awp->replaceWith(alwaysp); pushDeletep(awp); awp=NULL;
	}
	// Inline func refs in the function
	iterateIntoFTask(funcp);
	// Inline this reference
	if (debug()>=9) { m_lastStmtp->dumpTree(cout,"-inlstmt:"); }
	if (!insertAtp) nodep->v3fatalSrc("Function not underneath a statement");
	UINFO(5,"     Under  "<<insertAtp<<endl);
	// Create output variabls
	string namePrefix = "__Vfunc_"+funcp->shortName()+"__"+cvtToStr(m_modNCalls++);
	AstVarScope* outvscp = createVarScope (funcp->fvarp()->castVar(),
					       namePrefix+"__out");
	// Create cloned statements
	if (debug()>=9) { nodep->taskp()->dumpTree(cout,"-oldfunc:"); }
	if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked?");

	AstNode* beginp = createInlinedFTask(nodep, namePrefix, outvscp);
	// Add the whole thing before insertAt
	AstNRelinker handle;
	insertAtp->unlinkFrBackWithNext(&handle);
	if (debug()>=9) { beginp->dumpTree(cout,"-newfunc:"); }
	beginp->addNext(insertAtp);
	handle.relink(beginp);
	// Replace the ref
	AstVarRef* outrefp = new AstVarRef (nodep->fileline(), outvscp, false);
	nodep->replaceWith(outrefp);
	nodep->deleteTree(); nodep=NULL;
	if (debug()>=9) { insertAtp->dumpTree(cout,"-newstmt:"); }
	UINFO(4,"  Done.\n");
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	AstNode* prevLastStmtp = m_lastStmtp;
	m_lastStmtp = nodep->stmtsp();
	if (!nodep->user()) {
	    // Expand functions in it & Mark for later delete
	    nodep->user(true);
	    if (!nodep->taskPublic()) {
		nodep->unlinkFrBack();
	    } else {
		// Clone it first, because we may have later FTaskRef's that still need
		// the original version.
		AstNodeFTask* clonedFuncp = nodep->cloneTree(false)->castNodeFTask();
		AstCFunc* cfuncp = makeUserFunc(clonedFuncp);
		// Replace it
		nodep->replaceWith(cfuncp);
		iterateIntoFTask(clonedFuncp);  // Do the clone too
	    }
	    // Any variables inside the function still have varscopes pointing to them.
	    // We're going to delete the vars, so delete the varscopes.
	    if (nodep->castFunc()) {
		if (AstVar* portp = nodep->castFunc()->fvarp()->castVar()) {
		    AstVarScope* vscp = m_statep->findVarScope(m_scopep, portp);
		    UINFO(9,"   funcremovevsc "<<vscp<<endl);
		    pushDeletep(vscp->unlinkFrBack()); vscp=NULL;
		}
	    }
	    for (AstNode* nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp=nextp) {
		nextp = stmtp->nextp();
		if (AstVar* portp = stmtp->castVar()) {
		    AstVarScope* vscp = m_statep->findVarScope(m_scopep, portp);
		    UINFO(9,"   funcremovevsc "<<vscp<<endl);
		    pushDeletep(vscp->unlinkFrBack()); vscp=NULL;
		}
	    }
	    // Just push, as other references to func may remain until visitor exits
	    pushDeletep(nodep); nodep=NULL;
	}
	m_lastStmtp = prevLastStmtp;
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	m_lastStmtp = nodep;
	nodep->iterateChildren(*this);
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    TaskVisitor(AstNetlist* nodep, TaskStateVisitor* statep)
	: m_statep(statep) {
	m_modp = NULL;
	m_scopep = NULL;
	AstNode::userClearTree();
	nodep->accept(*this);
    }
    virtual ~TaskVisitor() {}
};

//######################################################################
// Task class functions

void V3Task::taskAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TaskStateVisitor visitors (nodep);
    TaskVisitor visitor (nodep, &visitors);
}
