// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for task nodes
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
// V3Task's Transformations:
//
// Each module:
//	Look for TASKREF
//	    Insert task's statements into the referrer
//	Look for TASKs
//	    Remove them, they're inlined
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>

#include "V3Global.h"
#include "V3Task.h"
#include "V3Inst.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Graph.h"
#include "V3LinkLValue.h"

//######################################################################
// Graph subclasses

class TaskBaseVertex : public V3GraphVertex {
    AstNode*	m_impurep;	// Node causing impure function w/ outside references
    bool	m_noInline;	// Marked with pragma
public:
    TaskBaseVertex(V3Graph* graphp)
	: V3GraphVertex(graphp), m_impurep(NULL), m_noInline(false) {}
    virtual ~TaskBaseVertex() {}
    bool pure() const { return m_impurep==NULL; }
    AstNode* impureNode() const { return m_impurep; }
    void impure(AstNode* nodep) { m_impurep = nodep; }
    bool noInline() const { return m_noInline; }
    void noInline(bool flag) { m_noInline = flag; }
};

class TaskFTaskVertex : public TaskBaseVertex {
    // Every task gets a vertex, and we link tasks together based on funcrefs.
    AstNodeFTask* m_nodep;
    AstCFunc* m_cFuncp;
public:
    TaskFTaskVertex(V3Graph* graphp, AstNodeFTask* nodep)
	: TaskBaseVertex(graphp), m_nodep(nodep) {
	m_cFuncp=NULL;
    }
    virtual ~TaskFTaskVertex() {}
    AstNodeFTask* nodep() const { return m_nodep; }
    virtual string name() const { return nodep()->name(); }
    virtual string dotColor() const { return pure() ? "black" : "red"; }
    AstCFunc* cFuncp() const { return m_cFuncp; }
    void cFuncp(AstCFunc* nodep) { m_cFuncp=nodep; }
};

class TaskCodeVertex : public TaskBaseVertex {
    // Top vertex for all calls not under another task
public:
    TaskCodeVertex(V3Graph* graphp)
	: TaskBaseVertex(graphp) {}
    virtual ~TaskCodeVertex() {}
    virtual string name() const { return "*CODE*"; }
    virtual string dotColor() const { return "green"; }
};

class TaskEdge : public V3GraphEdge {
public:
    TaskEdge(V3Graph* graphp, TaskBaseVertex* fromp, TaskBaseVertex* top)
	: V3GraphEdge(graphp, fromp, top, 1, false) {}
    virtual ~TaskEdge() {}
    virtual string dotLabel() const { return "w"+cvtToStr(weight()); }
};

//######################################################################

class TaskStateVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Output:
    //   AstNodeFTask::user3p	// AstScope* this FTask is under
    //   AstNodeFTask::user4p	// GraphFTaskVertex* this FTask is under
    //   AstVar::user4p		// GraphFTaskVertex* this variable is declared in

    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;

    // TYPES
    typedef std::map<pair<AstScope*,AstVar*>,AstVarScope*> VarToScopeMap;
    // MEMBERS
    VarToScopeMap	m_varToScopeMap;	// Map for Var -> VarScope mappings
    AstAssignW*		m_assignwp;		// Current assignment
    V3Graph		m_callGraph;		// Task call graph
    TaskBaseVertex*	m_curVxp;		// Current vertex we're adding to

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
    bool ftaskNoInline(AstNodeFTask* nodep) {
	return (getFTaskVertex(nodep)->noInline());
    }
    AstCFunc* ftaskCFuncp(AstNodeFTask* nodep) {
	return (getFTaskVertex(nodep)->cFuncp());
    }
    void ftaskCFuncp(AstNodeFTask* nodep, AstCFunc* cfuncp) {
	getFTaskVertex(nodep)->cFuncp(cfuncp);
    }

    void checkPurity(AstNodeFTask* nodep) {
	checkPurity(nodep, getFTaskVertex(nodep));
    }
    void checkPurity(AstNodeFTask* nodep, TaskBaseVertex* vxp) {
	if (!vxp->pure()) {
	    nodep->v3warn(IMPURE,"Unsupported: External variable referenced by non-inlined function/task: "<<nodep->prettyName()<<endl
			  <<vxp->impureNode()->warnMore()<<"... Location of the external reference: "<<vxp->impureNode()->prettyName());
	}
	// And, we need to check all tasks this task calls
	for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    checkPurity(nodep, static_cast<TaskBaseVertex*>(edgep->top()));
	}
    }
private:
    TaskFTaskVertex* getFTaskVertex(AstNodeFTask* nodep) {
	if (!nodep->user4p()) {
	    nodep->user4p(new TaskFTaskVertex(&m_callGraph, nodep));
	}
	return static_cast<TaskFTaskVertex*>(nodep->user4p()->castGraphVertex());
    }

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
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	m_assignwp = nodep;
	nodep->iterateChildren(*this); nodep=NULL;  // May delete nodep.
	m_assignwp = NULL;
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (m_assignwp) {
	    // Wire assigns must become always statements to deal with insertion
	    // of multiple statements.  Perhaps someday make all wassigns into always's?
	    UINFO(5,"     IM_WireRep  "<<m_assignwp<<endl);
	    m_assignwp->convertToAlways(); pushDeletep(m_assignwp); m_assignwp=NULL;
	}
	// We make multiple edges if a task is called multiple times from another task.
	if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked task");
	new TaskEdge (&m_callGraph, m_curVxp, getFTaskVertex(nodep->taskp()));
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	UINFO(9,"  TASK "<<nodep<<endl);
	TaskBaseVertex* lastVxp = m_curVxp;
	m_curVxp = getFTaskVertex(nodep);
	if (nodep->dpiImport()) m_curVxp->noInline(true);
	nodep->iterateChildren(*this);
	m_curVxp = lastVxp;
    }
    virtual void visit(AstPragma* nodep, AstNUser*) {
	if (nodep->pragType() == AstPragmaType::NO_INLINE_TASK) {
	    // Just mark for the next steps, and we're done with it.
	    m_curVxp->noInline(true);
	    nodep->unlinkFrBack()->deleteTree();
	}
	else {
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	nodep->user4p(m_curVxp);  // Remember what task it's under
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->varp()->user4p() != m_curVxp) {
	    if (m_curVxp->pure()
		&& !nodep->varp()->isXTemp()) {
		m_curVxp->impure(nodep);
	    }
	}
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    TaskStateVisitor(AstNetlist* nodep) {
	m_assignwp = NULL;
	m_curVxp = new TaskCodeVertex(&m_callGraph);
	AstNode::user3ClearTree();
	AstNode::user4ClearTree();
	//
	nodep->accept(*this);
	//
	m_callGraph.removeRedundantEdgesSum(&TaskEdge::followAlwaysTrue);
	m_callGraph.dumpDotFilePrefixed("task_call");
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
    TaskRelinkVisitor(AstBegin* nodep) {  // Passed temporary tree
	nodep->accept(*this);
    }
    virtual ~TaskRelinkVisitor() {}
};

//######################################################################
// Task state, as a visitor of each AstNode

class TaskVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Each module:
    //    AstNodeFTask::user	// True if its been expanded
    // Each funccall
    //  to TaskRelinkVisitor:
    //    AstVar::user2p	// AstVarScope* to replace varref with

    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    enum  InsertMode {
	IM_BEFORE,		// Pointing at statement ref is in, insert before this
	IM_AFTER,		// Pointing at last inserted stmt, insert after
	IM_WHILE_PRECOND	// Pointing to for loop, add to body end
    };
    typedef map<string,pair<AstCFunc*,string> > DpiNames;

    // STATE
    TaskStateVisitor*	m_statep;	// Common state between visitors
    AstNodeModule*	m_modp;		// Current module
    AstTopScope*	m_topScopep;	// Current top scope
    AstScope*	m_scopep;	// Current scope
    InsertMode	m_insMode;	// How to insert
    AstNode*	m_insStmtp;	// Where to insert statement
    int		m_modNCalls;	// Incrementing func # for making symbols
    DpiNames	m_dpiNames;	// Map of all created DPI functions

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    AstVarScope* createFuncVar(AstCFunc* funcp, const string& name, AstVar* examplep) {
	AstVar* newvarp = new AstVar (funcp->fileline(), AstVarType::BLOCKTEMP, name,
				      examplep);
	newvarp->funcLocal(true);
	funcp->addInitsp(newvarp);
	AstVarScope* newvscp = new AstVarScope(funcp->fileline(), m_scopep, newvarp);
	m_scopep->addVarp(newvscp);
	return newvscp;
    }
    AstVarScope* createInputVar(AstCFunc* funcp, const string& name, AstBasicDTypeKwd kwd) {
	AstVar* newvarp = new AstVar (funcp->fileline(), AstVarType::BLOCKTEMP, name,
				      funcp->findBasicDType(kwd));
	newvarp->funcLocal(true);
	newvarp->combineType(AstVarType::INPUT);
	funcp->addArgsp(newvarp);
	AstVarScope* newvscp = new AstVarScope(funcp->fileline(), m_scopep, newvarp);
	m_scopep->addVarp(newvscp);
	return newvscp;
    }
    AstVarScope* createVarScope(AstVar* invarp, const string& name) {
	// We could create under either the ref's scope or the ftask's scope.
	// It shouldn't matter, as they are only local variables.
	// We choose to do it under whichever called this function, which results
	// in more cache locality.
	AstVar* newvarp = new AstVar (invarp->fileline(), AstVarType::BLOCKTEMP,
				      name, invarp);
	newvarp->funcLocal(false);
	newvarp->propagateAttrFrom(invarp);
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
	if (debug()>=9) { beginp->dumpTreeAndNext(cout,"-newbegi:"); }
	//
	// Create input variables
	AstNode::user2ClearTree();
	V3TaskConnects tconnects = V3Task::taskConnects(refp, beginp);
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstArg* argp = it->second;
	    AstNode* pinp = argp->exprp();
	    portp->unlinkFrBack(); pushDeletep(portp);  // Remove it from the clone (not original)
	    if (pinp==NULL) {
		// Too few arguments in function call
	    } else {
		UINFO(9, "     Port "<<portp<<endl);
		UINFO(9, "      pin "<<pinp<<endl);
		pinp->unlinkFrBack();   // Relinked to assignment below
		argp->unlinkFrBack()->deleteTree(); // Args no longer needed
		//
		if ((portp->isInout()||portp->isOutput()) && pinp->castConst()) {
		    pinp->v3error("Function/task output connected to constant instead of variable: "+portp->prettyName());
		}
		else if (portp->isInout()) {
		    if (AstVarRef* varrefp = pinp->castVarRef()) {
			// Connect to this exact variable
			AstVarScope* localVscp = varrefp->varScopep(); if (!localVscp) varrefp->v3fatalSrc("Null var scope");
			portp->user2p(localVscp);
			pushDeletep(pinp);
		    } else {
			pinp->v3warn(E_TASKNSVAR,"Unsupported: Function/task input argument is not simple variable");
		    }
		}
		else if (portp->isOutput()) {
		    // Make output variables
		    // Correct lvalue; we didn't know when we linked
		    // This is slightly scary; are we sure no decisions were made
		    // before here based on this not being a lvalue?
		    // Doesn't seem so; V3Unknown uses it earlier, but works ok.
		    V3LinkLValue::linkLValueSet(pinp);

		    // Even if it's referencing a varref, we still make a temporary
		    // Else task(x,x,x) might produce incorrect results
		    AstVarScope* outvscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
		    portp->user2p(outvscp);
		    AstAssign* assp = new AstAssign (pinp->fileline(),
						     pinp,
						     new AstVarRef(outvscp->fileline(), outvscp, false));
		    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
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
		    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
		    // Put assignment in FRONT of all other statements
		    if (AstNode* afterp = beginp->nextp()) {
			afterp->unlinkFrBackWithNext();
			assp->addNext(afterp);
		    }
		    beginp->addNext(assp);
		}
	    }
	}
	if (refp->pinsp()) refp->v3fatalSrc("Pin wasn't removed by above loop");
	{
	    AstNode* nextstmtp;
	    for (AstNode* stmtp = beginp; stmtp; stmtp=nextstmtp) {
		nextstmtp = stmtp->nextp();
		if (AstVar* portp = stmtp->castVar()) {
		    // Any I/O variables that fell out of above loop were already linked
		    if (!portp->user2p()) {
			// Move it to a new localized variable
			portp->unlinkFrBack(); pushDeletep(portp);  // Remove it from the clone (not original)
			AstVarScope* localVscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
			portp->user2p(localVscp);
		    }
		}
	    }
	}
	// Create function output variables
	if (outvscp) {
	    //UINFO(0, "setflag on "<<funcp->fvarp()<<" to "<<outvscp<<endl);
	    refp->taskp()->fvarp()->user2p(outvscp);
	}
	// Replace variable refs
	// Iteration requires a back, so put under temporary node
	{
	    AstBegin* tempp = new AstBegin(beginp->fileline(),"[EditWrapper]",beginp);
	    TaskRelinkVisitor visit (tempp);
	    tempp->stmtsp()->unlinkFrBackWithNext(); tempp->deleteTree(); tempp=NULL;
	}
	//
	if (debug()>=9) { beginp->dumpTreeAndNext(cout,"-iotask: "); }
	return beginp;
    }

    AstNode* createNonInlinedFTask(AstNodeFTaskRef* refp, string namePrefix, AstVarScope* outvscp) {
	// outvscp is the variable for functions only, if NULL, it's a task
	if (!refp->taskp()) refp->v3fatalSrc("Unlinked?");
	AstCFunc* cfuncp = m_statep->ftaskCFuncp(refp->taskp());

	if (!cfuncp) refp->v3fatalSrc("No non-inline task associated with this task call?");
	//
	AstNode* beginp = new AstComment(refp->fileline(), (string)("Function: ")+refp->name());
	AstCCall* ccallp = new AstCCall(refp->fileline(), cfuncp, NULL);
	beginp->addNext(ccallp);
	// Convert complicated outputs to temp signals

	V3TaskConnects tconnects = V3Task::taskConnects(refp, refp->taskp()->stmtsp());
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstNode* pinp = it->second->exprp();
	    if (!pinp) {
		// Too few arguments in function call
	    } else {
		UINFO(9, "     Port "<<portp<<endl);
		UINFO(9, "      pin "<<pinp<<endl);
		if ((portp->isInout()||portp->isOutput()) && pinp->castConst()) {
		    pinp->v3error("Function/task output connected to constant instead of variable: "+portp->prettyName());
		}
		else if (portp->isInout()) {
		    if (pinp->castVarRef()) {
			// Connect to this exact variable
		    } else {
			pinp->v3warn(E_TASKNSVAR,"Unsupported: Function/task input argument is not simple variable");
		    }
		}
		else if (portp->isOutput()) {
		    // Make output variables
		    // Correct lvalue; we didn't know when we linked
		    // This is slightly scary; are we sure no decisions were made
		    // before here based on this not being a lvalue?
		    // Doesn't seem so; V3Unknown uses it earlier, but works ok.
		    V3LinkLValue::linkLValueSet(pinp);

		    // Even if it's referencing a varref, we still make a temporary
		    // Else task(x,x,x) might produce incorrect results
		    AstVarScope* outvscp = createVarScope (portp, namePrefix+"__"+portp->shortName());
		    portp->user2p(outvscp);
		    pinp->replaceWith(new AstVarRef(outvscp->fileline(), outvscp, true));
		    AstAssign* assp = new AstAssign (pinp->fileline(),
						     pinp,
						     new AstVarRef(outvscp->fileline(), outvscp, false));
		    assp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);  // Ok if in <= block
		    // Put assignment BEHIND of all other statements
		    beginp->addNext(assp);
		}
	    }
	}
	// First argument is symbol table, then output if a function
	bool needSyms = !refp->taskp()->dpiImport();
	if (needSyms) ccallp->argTypes("vlSymsp");

	if (refp->taskp()->dpiContext()) {
	    // __Vscopep
	    AstNode* snp = refp->scopeNamep()->unlinkFrBack();  if (!snp) refp->v3fatalSrc("Missing scoping context");
	    ccallp->addArgsp(snp);
	    // __Vfilenamep
	    ccallp->addArgsp(new AstCMath(refp->fileline(), "\""+refp->fileline()->filename()+"\"", 64, true));
	    // __Vlineno
	    ccallp->addArgsp(new AstConst(refp->fileline(), refp->fileline()->lineno()));
	}

	// Create connections
	AstNode* nextpinp;
	for (AstNode* pinp = refp->pinsp(); pinp; pinp=nextpinp) {
	    nextpinp = pinp->nextp();
	    // Move pin to the CCall, removing all Arg's
	    AstNode* exprp = pinp->castArg()->exprp();
	    exprp->unlinkFrBack();
	    ccallp->addArgsp(exprp);
	}

	if (outvscp) {
	    ccallp->addArgsp(new AstVarRef(refp->fileline(), outvscp, true));
	}

	if (debug()>=9) { beginp->dumpTreeAndNext(cout,"-nitask: "); }
	return beginp;
    }

    string dpiprotoName(AstNodeFTask* nodep, AstVar* rtnvarp) const {
	// Return fancy export-ish name for DPI function
	// Variable names are NOT included so differences in only IO names won't matter
	string dpiproto;
	if (nodep->pure()) dpiproto += "pure ";
	if (nodep->dpiContext()) dpiproto += "context ";
	dpiproto += rtnvarp ? rtnvarp->dpiArgType(true,true):"void";
	dpiproto += " "+nodep->cname()+" (";
	string args;
	for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO() && !portp->isFuncReturn() && portp!=rtnvarp) {
		    if (args != "") { args+= ", "; dpiproto+= ", "; }
		    args += portp->name();  // Leftover so ,'s look nice
		    if (nodep->dpiImport()) dpiproto += portp->dpiArgType(false,false);
		}
	    }
	}
	dpiproto += ")";
	return dpiproto;
    }

    AstNode* createDpiTemp(AstVar* portp, const string& suffix) {
	bool bitvec = (portp->basicp()->isBitLogic() && portp->width() > 32);
	string stmt;
	if (bitvec) {
	    stmt += "svBitVecVal "+portp->name()+suffix;
	    stmt += " ["+cvtToStr(portp->widthWords())+"]";
	} else {
	    stmt += portp->dpiArgType(true,true);
	    stmt += " "+portp->name()+suffix;
	}
	stmt += ";\n";
	return new AstCStmt(portp->fileline(), stmt);
    }

    AstNode* createAssignInternalToDpi(AstVar* portp, bool isPtr, const string& frSuffix, const string& toSuffix) {
	// Create assignment from internal format into DPI temporary
	bool bitvec = (portp->basicp()->isBitLogic() && portp->width() > 32);
	string stmt;
	string ket;
	// Someday we'll have better type support, and this can make variables and casts.
	// But for now, we'll just text-bash it.
	if (bitvec) {
	    if (portp->isWide()) {
		stmt += ("VL_SET_SVBV_W("+cvtToStr(portp->width())
			 +", "+portp->name()+toSuffix+", "+portp->name()+frSuffix+")");
	    } else {
		stmt += "VL_SET_WQ("+portp->name()+toSuffix+", "+portp->name()+frSuffix+")";
	    }
	} else {
	    if (isPtr) stmt += "*"; // DPI outputs are pointers
	    stmt += portp->name()+toSuffix+" = ";
	    if (portp->basicp() && portp->basicp()->keyword()==AstBasicDTypeKwd::CHANDLE) {
		stmt += "VL_CVT_Q_VP(";
		ket += ")";
	    }
	    stmt += portp->name()+frSuffix;
	    if (portp->basicp() && portp->basicp()->keyword()==AstBasicDTypeKwd::STRING) {
		stmt += ".c_str()";
	    }
	}
	stmt += ket + ";\n";
	return new AstCStmt(portp->fileline(), stmt);
    }

    AstNode* createAssignDpiToInternal(AstVarScope* portvscp, const string& frName, bool cvt) {
	// Create assignment from DPI temporary into internal format
	AstVar* portp = portvscp->varp();
	string stmt;
	string ket;
	if (portp->basicp() && portp->basicp()->keyword()==AstBasicDTypeKwd::CHANDLE) {
	    stmt += "VL_CVT_VP_Q(";
	    ket += ")";
	}
	else if (portp->basicp() && portp->basicp()->isBitLogic() && portp->width() != 1 && portp->isQuad()) {
	    // SV is vector, Verilator isn't
	    stmt += "VL_SET_QW(";
	    ket += ")";
	}
	if (!cvt
	    && portp->basicp() && portp->basicp()->isBitLogic() && portp->width() != 1 && !portp->isWide() && !portp->isQuad())
	    stmt += "*";  // it's a svBitVecVal, which other code won't think is arrayed (as WData aren't), but really is
	stmt += frName;
	stmt += ket;
	// Use a AstCMath, as we want V3Clean to mask off bits that don't make sense.
	int cwidth = VL_WORDSIZE; if (portp->basicp()) cwidth = portp->basicp()->keyword().width();
	if (portp->basicp() && portp->basicp()->isBitLogic()) cwidth = VL_WORDSIZE*portp->widthWords();
	AstNode* newp = new AstAssign(portp->fileline(),
				      new AstVarRef(portp->fileline(), portvscp, true),
				      new AstSel(portp->fileline(),
						 new AstCMath(portp->fileline(), stmt, cwidth, false),
						 0, portp->width()));
	return newp;
    }

    AstCFunc* makeDpiExportWrapper(AstNodeFTask* nodep, AstVar* rtnvarp) {
	AstCFunc* dpip = new AstCFunc(nodep->fileline(),
				      nodep->cname(),
				      m_scopep,
				      (rtnvarp ? rtnvarp->dpiArgType(true,true) : ""));
	dpip->dontCombine(true);
	dpip->entryPoint(true);
	dpip->isStatic(true);
	dpip->dpiExportWrapper(true);
	dpip->cname(nodep->cname());
	// Add DPI reference to top, since it's a global function
	m_topScopep->scopep()->addActivep(dpip);

	{// Create dispatch wrapper
	    // Note this function may dispatch to myfunc on a different class.
	    // Thus we need to be careful not to assume a particular function layout.
	    //
	    // Func numbers must be the same for each function, even when there are
	    // completely different models with the same function name.
	    // Thus we can't just use a constant computed at Verilation time.
	    // We could use 64-bits of a MD5/SHA hash rather than a string here,
	    // but the compare is only done on first call then memoized, so it's not worth optimizing.
	    string stmt;
	    stmt += "static int __Vfuncnum = -1;\n";  // Static doesn't need save-restore as if below will re-fill proper value
	    // First time init (faster than what the compiler does if we did a singleton
	    stmt += "if (VL_UNLIKELY(__Vfuncnum==-1)) { __Vfuncnum = Verilated::exportFuncNum(\""+nodep->cname()+"\"); }\n";
	    // If the find fails, it will throw an error
	    stmt += "const VerilatedScope* __Vscopep = Verilated::dpiScope();\n";
	    // If dpiScope is fails and is null; the exportFind function throws and error
	    string cbtype = v3Global.opt.prefix()+"__Vcb_"+nodep->cname()+"_t";
	    stmt += cbtype+" __Vcb = ("+cbtype+")__Vscopep->exportFind(__Vfuncnum);\n";
	    // If __Vcb is null the exportFind function throws and error
	    dpip->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
	}

	// Convert input/inout DPI arguments to Internal types
	string args;
	args += "("+v3Global.opt.prefix()+"__Syms*)(__Vscopep->symsp())";  // Upcast w/o overhead
	AstNode* argnodesp = NULL;
	for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO() && !portp->isFuncReturn() && portp != rtnvarp) {
		    // No createDpiTemp; we make a real internal variable instead
		    // SAME CODE BELOW
		    args+= ", ";
		    if (args != "") { argnodesp = argnodesp->addNext(new AstText(portp->fileline(), args, true)); args=""; }
		    AstVarScope* outvscp = createFuncVar (dpip, portp->name()+"__Vcvt", portp);
		    AstVarRef* refp = new AstVarRef(portp->fileline(), outvscp, portp->isOutput());
		    argnodesp = argnodesp->addNextNull(refp);

		    if (portp->isInput()) {
			dpip->addStmtsp(createAssignDpiToInternal(outvscp, portp->name(), false));
		    }
		}
	    }
	}

	if (rtnvarp) {
	    AstVar* portp = rtnvarp;
	    // SAME CODE ABOVE
	    args+= ", ";
	    if (args != "") { argnodesp = argnodesp->addNext(new AstText(portp->fileline(), args, true)); args=""; }
	    AstVarScope* outvscp = createFuncVar (dpip, portp->name()+"__Vcvt", portp);
	    AstVarRef* refp = new AstVarRef(portp->fileline(), outvscp, portp->isOutput());
	    argnodesp = argnodesp->addNextNull(refp);
	}

	{// Call the user function
	    // Add the variables referenced as VarRef's so that lifetime analysis
	    // doesn't rip up the variables on us
	    string stmt;
	    stmt += "(*__Vcb)(";
	    args += ");\n";
	    AstCStmt* newp = new AstCStmt(nodep->fileline(), stmt);
	    newp->addBodysp(argnodesp); argnodesp=NULL;
	    newp->addBodysp(new AstText(nodep->fileline(), args, true));
	    dpip->addStmtsp(newp);
	}

	// Convert output/inout arguments back to internal type
	for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO() && portp->isOutput() && !portp->isFuncReturn()) {
		    dpip->addStmtsp(createAssignInternalToDpi(portp,true,"__Vcvt",""));
		}
	    }
	}

	if (rtnvarp) {
	    dpip->addStmtsp(createDpiTemp(rtnvarp,""));
	    dpip->addStmtsp(createAssignInternalToDpi(rtnvarp,false,"__Vcvt",""));
	    string stmt = "return "+rtnvarp->name()+";\n";
	    dpip->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
	}
	return dpip;
    }

    AstCFunc* makeDpiImportWrapper(AstNodeFTask* nodep, AstVar* rtnvarp) {
	if (nodep->cname() != AstNode::prettyName(nodep->cname())) {
	    nodep->v3error("DPI function has illegal characters in C identifier name: "<<AstNode::prettyName(nodep->cname()));
	}
	AstCFunc* dpip = new AstCFunc(nodep->fileline(),
				      nodep->cname(),
				      m_scopep,
				      (rtnvarp ? rtnvarp->dpiArgType(true,true)
				       // Tasks (but not void functions) return bool indicating disabled
				       : nodep->dpiTask() ? "int"
				       : ""));
	dpip->dontCombine(true);
	dpip->entryPoint (false);
	dpip->funcPublic (true);
	dpip->isStatic   (false);
	dpip->pure       (nodep->pure());
	dpip->dpiImport  (true);
	// Add DPI reference to top, since it's a global function
	m_topScopep->scopep()->addActivep(dpip);
	return dpip;
    }

    void bodyDpiImportFunc(AstNodeFTask* nodep, AstVarScope* rtnvscp, AstCFunc* cfuncp) {
	// Convert input/inout arguments to DPI types
	string args;
	for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		AstVarScope* portvscp = portp->user2p()->castNode()->castVarScope();  // Remembered when we created it earlier
		if (portp->isIO() && !portp->isFuncReturn() && portvscp != rtnvscp
		    && portp->name() != "__Vscopep"	// Passed to dpiContext, not callee
		    && portp->name() != "__Vfilenamep"
		    && portp->name() != "__Vlineno") {
		    bool bitvec = (portp->basicp()->isBitLogic() && portp->width() > 32);

		    if (args != "") { args+= ", "; }
		    if (bitvec) {}
		    else if (portp->isOutput()) args += "&";
		    else if (portp->basicp() && portp->basicp()->isBitLogic() && portp->width() != 1) args += "&";  // it's a svBitVecVal

		    args += portp->name()+"__Vcvt";

		    cfuncp->addStmtsp(createDpiTemp(portp,"__Vcvt"));
		    if (portp->isInput()) {
			cfuncp->addStmtsp(createAssignInternalToDpi(portp,false,"","__Vcvt"));
		    }
		}
	    }
	}

	// Store context, if needed
	if (nodep->dpiContext()) {
	    string stmt = "Verilated::dpiContext(__Vscopep, __Vfilenamep, __Vlineno);\n";
	    cfuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
	}

	{// Call the user function
	    string stmt;
	    if (rtnvscp) {  // isFunction will no longer work as we unlinked the return var
		stmt += rtnvscp->varp()->dpiArgType(true,true) + " "+rtnvscp->varp()->name()+"__Vcvt = ";
	    }
	    stmt += nodep->cname()+"("+args+");\n";
	    cfuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
	}

	// Convert output/inout arguments back to internal type
	for (AstNode* stmtp = cfuncp->argsp(); stmtp; stmtp=stmtp->nextp()) {
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO() && (portp->isOutput() || portp->isFuncReturn())) {
		    AstVarScope* portvscp = portp->user2p()->castNode()->castVarScope();  // Remembered when we created it earlier
		    cfuncp->addStmtsp(createAssignDpiToInternal(portvscp,portp->name()+"__Vcvt",true));
		}
	    }
	}
    }

    AstCFunc* makeUserFunc(AstNodeFTask* nodep, bool ftaskNoInline) {
	// Given a already cloned node, make a public C function, or a non-inline C function
	// Probably some of this work should be done later, but...
	// should the type of the function be bool/uint32/64 etc (based on lookup) or IData?
	AstNode::user2ClearTree();
	AstVar* rtnvarp = NULL;
	AstVarScope* rtnvscp = NULL;
	if (nodep->isFunction()) {
	    AstVar* portp = NULL;
	    if (NULL!=(portp = nodep->fvarp()->castVar())) {
		if (!portp->isFuncReturn()) nodep->v3error("Not marked as function return var");
		if (portp->isWide()) nodep->v3error("Unsupported: Public functions with return > 64 bits wide. (Make it a output instead.)");
		if (ftaskNoInline || nodep->dpiExport()) portp->funcReturn(false);  // Converting return to 'outputs'
		portp->unlinkFrBack();
		rtnvarp = portp;
		rtnvarp->funcLocal(true);
		rtnvarp->name(rtnvarp->name()+"__Vfuncrtn");  // Avoid conflict with DPI function name
		rtnvscp = new AstVarScope (rtnvarp->fileline(), m_scopep, rtnvarp);
		m_scopep->addVarp(rtnvscp);
		rtnvarp->user2p(rtnvscp);
	    } else {
		nodep->v3fatalSrc("function without function output variable");
	    }
	}
	string prefix = "";
	if (nodep->dpiImport()) prefix = "__Vdpiimwrap_";
	else if (nodep->dpiExport()) prefix = "__Vdpiexp_";
	else if (ftaskNoInline) prefix = "__VnoInFunc_";
	// Unless public, v3Descope will not uniquify function names even if duplicate per-scope,
	// so make it unique now.
	string suffix = "";  // So, make them unique
	if (!nodep->taskPublic()) suffix = "_"+m_scopep->nameDotless();
	AstCFunc* cfuncp = new AstCFunc(nodep->fileline(),
					prefix + nodep->name() + suffix,
					m_scopep,
					((nodep->taskPublic() && rtnvarp) ? rtnvarp->cPubArgType(true,true)
					 : ""));
	// It's ok to combine imports because this is just a wrapper; duplicate wrappers can get merged.
	cfuncp->dontCombine(!nodep->dpiImport());
	cfuncp->entryPoint (!nodep->dpiImport());
	cfuncp->funcPublic (nodep->taskPublic());
	cfuncp->dpiExport  (nodep->dpiExport());
	cfuncp->isStatic   (!(nodep->dpiImport()||nodep->taskPublic()));
	cfuncp->pure	   (nodep->pure());
	//cfuncp->dpiImport   // Not set in the wrapper - the called function has it set
	if (cfuncp->dpiExport()) cfuncp->cname (nodep->cname());

	bool needSyms = !nodep->dpiImport();
	if (needSyms) {
	    if (nodep->taskPublic()) {
		// We need to get a pointer to all of our variables (may have eval'ed something else earlier)
		cfuncp->addInitsp(
		    new AstCStmt(nodep->fileline(),
				 EmitCBaseVisitor::symClassVar()+" = this->__VlSymsp;\n"));
	    } else {
		// Need symbol table
		cfuncp->argTypes(EmitCBaseVisitor::symClassVar());
	    }
	}
	if (nodep->dpiContext()) {
	    // First three args go to dpiContext call
	    createInputVar (cfuncp, "__Vscopep", AstBasicDTypeKwd::SCOPEPTR);
	    createInputVar (cfuncp, "__Vfilenamep", AstBasicDTypeKwd::CHARPTR);
	    createInputVar (cfuncp, "__Vlineno", AstBasicDTypeKwd::INT);
	}

	if (!nodep->dpiImport()) {
	    cfuncp->addInitsp(new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign()+"\n"));
	}

	if (nodep->dpiExport()) {
	    AstScopeName* snp = nodep->scopeNamep();  if (!snp) nodep->v3fatalSrc("Missing scoping context");
	    snp->dpiExport(true);  // The AstScopeName is really a statement(ish) for tracking, not a function
	    snp->unlinkFrBack();
	    cfuncp->addInitsp(snp);
	}

	AstCFunc* dpip = NULL;
	string dpiproto;
	if (nodep->dpiImport() || nodep->dpiExport()) {
	    dpiproto = dpiprotoName(nodep, rtnvarp);

	    // Only create one DPI extern for each specified cname,
	    // as it's legal for the user to attach multiple tasks to one dpi cname
	    DpiNames::iterator iter = m_dpiNames.find(nodep->cname());
	    if (iter == m_dpiNames.end()) {
		// m_dpiNames insert below
		if (nodep->dpiImport()) {
		    dpip = makeDpiImportWrapper(nodep, rtnvarp);
		} else if (nodep->dpiExport()) {
		    dpip = makeDpiExportWrapper(nodep, rtnvarp);
		    cfuncp->addInitsp(new AstComment(dpip->fileline(), (string)("Function called from: ")+dpip->cname()));
		}

		m_dpiNames.insert(make_pair(nodep->cname(), make_pair(dpip, dpiproto)));
	    }
	    else if (iter->second.second != dpiproto) {
		nodep->v3error("Duplicate declaration of DPI function with different formal arguments: "<<nodep->prettyName()<<endl
			       <<nodep->warnMore()<<"... New prototype:      "<<dpiproto<<endl
			       <<iter->second.first->warnMore()<<"... Original prototype: "<<iter->second.second);
	    }
	}

	// Create list of arguments and move to function
	for (AstNode* nextp, *stmtp = nodep->stmtsp(); stmtp; stmtp=nextp) {
	    nextp = stmtp->nextp();
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO()) {
		    // Move it to new function
		    portp->unlinkFrBack();
		    portp->funcLocal(true);
		    cfuncp->addArgsp(portp);
		    if (dpip) {
			dpip->addArgsp(portp->cloneTree(false));
			if (!portp->basicp() || portp->basicp()->keyword().isDpiUnsupported()) {
			    portp->v3error("Unsupported: DPI argument of type "<<portp->basicp()->prettyTypeName()<<endl
					   <<portp->warnMore()<<"... For best portability, use bit, byte, int, or longint");
			}
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

	// Fake output variable if was a function.  It's more efficient to
	// have it last, rather than first, as the C compiler can sometimes
	// avoid copying variables when calling shells if argument 1
	// remains argument 1 (which it wouldn't if a return got added).
	if (rtnvarp) cfuncp->addArgsp(rtnvarp);

	// Move body
	AstNode* bodysp = nodep->stmtsp();
	if (bodysp) { bodysp->unlinkFrBackWithNext(); cfuncp->addStmtsp(bodysp); }
	if (nodep->dpiImport()) {
	    bodyDpiImportFunc(nodep, rtnvscp, cfuncp);
	}

	// Return statement
	if (rtnvscp && nodep->taskPublic()) {
	    cfuncp->addFinalsp(new AstCReturn(rtnvscp->fileline(),
					      new AstVarRef(rtnvscp->fileline(), rtnvscp, false)));
	}
	// Replace variable refs
	// Iteration requires a back, so put under temporary node
	{
	    AstBegin* tempp = new AstBegin(cfuncp->fileline(),"[EditWrapper]",cfuncp);
	    TaskRelinkVisitor visit (tempp);
	    tempp->stmtsp()->unlinkFrBackWithNext(); tempp->deleteTree(); tempp=NULL;
	}
	// Delete rest of cloned task and return new func
	pushDeletep(nodep); nodep=NULL;
	if (debug()>=9) { cfuncp->dumpTree(cout,"-userFunc: "); }
	return cfuncp;
    }

    void iterateIntoFTask(AstNodeFTask* nodep) {
	// Iterate into the FTask we are calling.  Note it may be under a different
	// scope then the caller, so we need to restore state.
	AstScope* oldscopep = m_scopep;
	InsertMode prevInsMode = m_insMode;
	AstNode* prevInsStmtp = m_insStmtp;
	m_scopep = m_statep->getScope(nodep);
	nodep->accept(*this);
	m_scopep = oldscopep;
	m_insMode = prevInsMode;
	m_insStmtp = prevInsStmtp;
    }
    void insertBeforeStmt(AstNode* nodep, AstNode* newp) {
	// See also AstNode::addBeforeStmt; this predates that function
	if (debug()>=9) { nodep->dumpTree(cout,"-newstmt:"); }
	if (!m_insStmtp) nodep->v3fatalSrc("Function not underneath a statement");
	if (m_insMode == IM_BEFORE) {
	    // Add the whole thing before insertAt
	    UINFO(5,"     IM_Before  "<<m_insStmtp<<endl);
	    if (debug()>=9) { newp->dumpTree(cout,"-newfunc:"); }
	    m_insStmtp->addHereThisAsNext(newp);
	}
	else if (m_insMode == IM_AFTER) {
	    UINFO(5,"     IM_After   "<<m_insStmtp);
	    m_insStmtp->addNextHere(newp);
	}
	else if (m_insMode == IM_WHILE_PRECOND) {
	    UINFO(5,"     IM_While_Precond "<<m_insStmtp);
	    AstWhile* whilep = m_insStmtp->castWhile();
	    if (!whilep) nodep->v3fatalSrc("Insert should be under WHILE");
	    whilep->addPrecondsp(newp);
	}
	else {
	    nodep->v3fatalSrc("Unknown InsertMode");
	}
	m_insMode = IM_AFTER;
	m_insStmtp = newp;
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_insStmtp = NULL;
	m_modNCalls = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	m_topScopep = nodep;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	m_scopep = nodep;
	m_insStmtp = NULL;
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked?");
	iterateIntoFTask(nodep->taskp());	// First, do hierarchical funcs
	UINFO(4," FTask REF   "<<nodep<<endl);
	if (debug()>=9) { nodep->dumpTree(cout,"-inlfunc:"); }
	if (!m_scopep) nodep->v3fatalSrc("func ref not under scope");
	string namePrefix = ((nodep->castFuncRef()?"__Vfunc_":"__Vtask_")
			     +nodep->taskp()->shortName()+"__"+cvtToStr(m_modNCalls++));
	// Create output variable
	AstVarScope* outvscp = NULL;
	if (nodep->taskp()->isFunction()) {
	    // Not that it's a FUNCREF, but that we're calling a function (perhaps as a task)
	    outvscp = createVarScope (nodep->taskp()->fvarp()->castVar(),
				      namePrefix+"__Vfuncout");
	}
	// Create cloned statements
	AstNode* beginp;
	if (m_statep->ftaskNoInline(nodep->taskp())) {
	    // This may share VarScope's with a public task, if any.  Yuk.
	    beginp = createNonInlinedFTask(nodep, namePrefix, outvscp);
	} else {
	    beginp = createInlinedFTask(nodep, namePrefix, outvscp);
	}
	// Replace the ref
	if (nodep->castFuncRef()) {
	    if (!nodep->taskp()->isFunction()) nodep->v3fatalSrc("func reference to non-function");
	    AstVarRef* outrefp = new AstVarRef (nodep->fileline(), outvscp, false);
	    nodep->replaceWith(outrefp);
	    // Insert new statements
	    insertBeforeStmt(nodep, beginp);
	} else {
	    // outvscp maybe non-NULL if calling a function in a taskref,
	    // but if so we want to simply ignore the function result
	    nodep->replaceWith(beginp);
	}
	// Cleanup
	nodep->deleteTree(); nodep=NULL;
	UINFO(4,"  FTask REF Done.\n");
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	UINFO(4," Inline   "<<nodep<<endl);
	InsertMode prevInsMode = m_insMode;
	AstNode* prevInsStmtp = m_insStmtp;
	m_insMode = IM_BEFORE;
	m_insStmtp = nodep->stmtsp();  // Might be null if no statements, but we won't use it
	if (!nodep->user1SetOnce()) {  // Just one creation needed per function
	    // Expand functions in it
	    int modes = 0;
	    if (nodep->dpiImport()) modes++;
	    if (nodep->dpiExport()) modes++;
	    if (nodep->taskPublic()) modes++;
	    if (modes > 1) nodep->v3error("Cannot mix DPI import, DPI export and/or public on same function: "<<nodep->prettyName());

	    if (nodep->dpiImport() || nodep->dpiExport()
		|| nodep->taskPublic() || m_statep->ftaskNoInline(nodep)) {
		// Clone it first, because we may have later FTaskRef's that still need
		// the original version.
		if (m_statep->ftaskNoInline(nodep)) m_statep->checkPurity(nodep);
		AstNodeFTask* clonedFuncp = nodep->cloneTree(false);
		AstCFunc* cfuncp = makeUserFunc(clonedFuncp, m_statep->ftaskNoInline(nodep));
		nodep->addNextHere(cfuncp);
		if (nodep->dpiImport() || m_statep->ftaskNoInline(nodep)) {
		    m_statep->ftaskCFuncp(nodep, cfuncp);
		}
		iterateIntoFTask(clonedFuncp);  // Do the clone too
	    }

	    // Any variables inside the function still have varscopes pointing to them.
	    // We're going to delete the vars, so delete the varscopes.
	    if (nodep->isFunction()) {
		if (AstVar* portp = nodep->fvarp()->castVar()) {
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
	    // Just push for deletion, as other references to func may
	    // remain until visitor exits
	    nodep->unlinkFrBack();
	    pushDeletep(nodep); nodep=NULL;
	}
	m_insMode = prevInsMode;
	m_insStmtp = prevInsStmtp;
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	// Special, as statements need to be put in different places
	// Preconditions insert first just before themselves (the normal rule for other statement types)
	m_insStmtp = NULL;	// First thing should be new statement
	nodep->precondsp()->iterateAndNext(*this);
	// Conditions insert first at end of precondsp.
	m_insMode = IM_WHILE_PRECOND;
	m_insStmtp = nodep;
	nodep->condp()->iterateAndNext(*this);
	// Body insert just before themselves
	m_insStmtp = NULL;	// First thing should be new statement
	nodep->bodysp()->iterateAndNext(*this);
	nodep->incsp()->iterateAndNext(*this);
	// Done the loop
	m_insStmtp = NULL;	// Next thing should be new statement
    }
    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	nodep->v3fatalSrc("For statements should have been converted to while statements in V3Begin.cpp\n");
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	m_insMode = IM_BEFORE;
	m_insStmtp = nodep;
	nodep->iterateChildren(*this);
	m_insStmtp = NULL;	// Next thing should be new statement
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
	m_topScopep = NULL;
	m_scopep = NULL;
	m_insStmtp = NULL;
	AstNode::user1ClearTree();
	nodep->accept(*this);
    }
    virtual ~TaskVisitor() {}
};

//######################################################################
// Task class functions

V3TaskConnects V3Task::taskConnects(AstNodeFTaskRef* nodep, AstNode* taskStmtsp) {
    // Output list will be in order of the port declaration variables (so func calls are made right in C)
    // Missing pin/expr?  We return (pinvar, NULL)
    // Extra   pin/expr?  We clean it up

    typedef map<string,int> NameToIndex;
    NameToIndex nameToIndex;
    V3TaskConnects tconnects;
    if (!nodep->taskp()) nodep->v3fatalSrc("unlinked");

    // Find ports
    //map<string,int> name_to_pinnum;
    int tpinnum = 0;
    AstVar* sformatp = NULL;
    for (AstNode* stmtp = taskStmtsp; stmtp; stmtp=stmtp->nextp()) {
	if (AstVar* portp = stmtp->castVar()) {
	    if (portp->isIO()) {
		tconnects.push_back(make_pair(portp, (AstArg*)NULL));
		nameToIndex.insert(make_pair(portp->name(), tpinnum)); // For name based connections
		tpinnum++;
		if (portp->attrSFormat()) {
		    sformatp = portp;
		} else if (sformatp) {
		    nodep->v3error("/*verilator sformat*/ can only be applied to last argument of a function");
		}
	    }
	}
    }

    // Find pins
    int ppinnum = 0;
    bool reorganize = false;
    for (AstNode* nextp, *pinp = nodep->pinsp(); pinp; pinp=nextp) {
	nextp = pinp->nextp();
	AstArg* argp = pinp->castArg(); if (!argp) pinp->v3fatalSrc("Non-arg under ftask reference");
	if (argp->name() != "") {
	    // By name
	    NameToIndex::iterator it = nameToIndex.find(argp->name());
	    if (it == nameToIndex.end()) {
		pinp->v3error("No such argument '"<<argp->prettyName()
			      <<"' in function call to "<<nodep->taskp()->prettyTypeName());
		// We'll just delete it; seems less error prone than making a false argument
		pinp->unlinkFrBack()->deleteTree(); pinp=NULL;
	    } else {
		if (tconnects[it->second].second) {
		    pinp->v3error("Duplicate argument '"<<argp->prettyName()
				  <<"' in function call to "<<nodep->taskp()->prettyTypeName());
		}
		argp->name("");  // Can forget name as will add back in pin order
		tconnects[it->second].second = argp;
		reorganize = true;
	    }
	} else { // By pin number
	    if (ppinnum >= tpinnum) {
		if (sformatp) {
		    tconnects.push_back(make_pair(sformatp, (AstArg*)NULL));
		    tconnects[ppinnum].second = argp;
		    tpinnum++;
		} else {
		    pinp->v3error("Too many arguments in function call to "<<nodep->taskp()->prettyTypeName());
		    // We'll just delete it; seems less error prone than making a false argument
		    pinp->unlinkFrBack()->deleteTree(); pinp=NULL;
		}
	    } else {
		tconnects[ppinnum].second = argp;
	    }
	}
	ppinnum++;
    }

    // Connect missing ones
    for (int i=0; i<tpinnum; ++i) {
	AstVar* portp = tconnects[i].first;
	if (!tconnects[i].second || !tconnects[i].second->exprp()) {
	    AstNode* newvaluep = NULL;
	    if (!portp->valuep()) {
		nodep->v3error("Missing argument on non-defaulted argument '"<<portp->prettyName()
			       <<"' in function call to "<<nodep->taskp()->prettyTypeName());
		newvaluep = new AstConst(nodep->fileline(), AstConst::Unsized32(), 0);
	    } else if (!portp->valuep()->castConst()) {
		// Problem otherwise is we might have a varref, task call, or something else that only
		// makes sense in the domain of the function, not the callee.
		nodep->v3error("Unsupported: Non-constant default value in missing argument '"<<portp->prettyName()
			       <<"' in function call to "<<nodep->taskp()->prettyTypeName());
		newvaluep = new AstConst(nodep->fileline(), AstConst::Unsized32(), 0);
	    } else {
		newvaluep = portp->valuep()->cloneTree(true);
	    }
	    // To avoid problems with callee needing to know to deleteTree or not, we make this into a pin
	    UINFO(9,"Default pin for "<<portp<<endl);
	    AstArg* newp = new AstArg(nodep->fileline(), portp->name(), newvaluep);
	    if (tconnects[i].second) { // Have a "NULL" pin already defined for it
		tconnects[i].second->unlinkFrBack()->deleteTree(); tconnects[i].second=NULL;
	    }
	    tconnects[i].second = newp;
	    reorganize = true;
	}
	if (tconnects[i].second) { UINFO(9,"Connect "<<portp<<"  ->  "<<tconnects[i].second<<endl); }
	else { UINFO(9,"Connect "<<portp<<"  ->  NONE"<<endl); }
    }

    if (reorganize) {
	// To simplify downstream, put argument list back into pure pinnumber ordering
	while (nodep->pinsp()) nodep->pinsp()->unlinkFrBack();  // Must unlink each pin, not all pins linked together as one list
	for (int i=0; i<tpinnum; ++i) {
	    AstArg* argp = tconnects[i].second; if (!argp) nodep->v3fatalSrc("Lost argument in func conversion");
	    nodep->addPinsp(argp);
	}
    }

    if (debug()>=9) {
	nodep->dumpTree(cout,"-ftref-out: ");
	for (int i=0; i<tpinnum; ++i) UINFO(0,"   pin "<<i<<"  conn="<<(void*)tconnects[i].second<<endl);
    }
    return tconnects;
}

void V3Task::taskAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TaskStateVisitor visitors (nodep);
    TaskVisitor visitor (nodep, &visitors);
    V3Global::dumpCheckGlobalTree("task.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
