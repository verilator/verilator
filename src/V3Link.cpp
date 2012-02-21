//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
#include <cctype>
#include <unistd.h>
#include <map>
#include <set>
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
    //   AstVar/Module/Task::user1() // AstPackage*    Set if inside a package
    //   AstVar::user2p()	// bool		  True if port set for this variable
    //   AstVar/Module::user3p() // V3SymTable*    Table used to create this variable
    //   AstNodeModule::user4p() // V3SymTable*    Module's Symbol table
    //   AstNodeFTask::user4p()	// V3SymTable*    Local Symbol table
    //   AstBegin::user4p()	// V3SymTable*    Local Symbol table
    //   AstVar::user5p()	// AstPin*	  True if port attached to a pin
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;
    AstUser5InUse	m_inuser5;

    // ENUMS
    enum IdState {		// Which loop through the tree
	ID_FIND,		// Find all identifiers and add to lists
	ID_PARAM,		// Move parameters to cell definitions
	ID_RESOLVE};		// Resolve all identifiers and report errors

    // STATE
    // Below state needs to be preserved between each module call.
    AstPackage*		m_packagep;	// Current package
    AstCell*		m_cellp;	// Current cell
    AstNodeModule*	m_modp;		// Current module
    AstNodeFTask* m_ftaskp;	// Current function/task
    IdState	m_idState;	// Id linking mode (find or resolve)
    int		m_paramNum;	// Parameter number, for position based connection
    V3SymTable* m_curVarsp;	// Symbol table of variables and tasks under table we're inserting into
    V3SymTable* m_cellVarsp;	// Symbol table of variables under cell's module
    int		m_beginNum;	// Begin block number, 0=none seen
    int		m_modBeginNum;	// Begin block number in module, 0=none seen
    bool	m_inAlways;	// Inside an always
    bool	m_inGenerate;	// Inside a generate
    AstNodeModule*	m_valueModp;	// If set, move AstVar->valuep() initial values to this module
    vector<V3SymTable*> m_delSymps;	// Symbol tables to delete
    set<string>	m_declfnWarned;	// Files we issued DECLFILENAME on

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // METHODS
    V3SymTable* symsFindNew(AstNode* nodep, V3SymTable* upperVarsp) {
	// Find or create symbol table for this node
	V3SymTable* symsp = nodep->user4p()->castSymTable();
	if (symsp) {
	    return symsp;
	} else {
	    symsp = new V3SymTable(nodep, upperVarsp);
	    m_delSymps.push_back(symsp);
	    nodep->user4p(symsp);
	    return symsp;
	}
    }
    V3SymTable* symsFind(AstNode* nodep) {
	// Find or create symbol table for this node
	if (V3SymTable* symsp = nodep->user4p()->castSymTable()) {
	    return symsp;
	} else {
	    nodep->v3fatalSrc("Symbol table not found looking up symbol");
	    return NULL;
	}
    }

    void symsInsert(const string& name, AstNode* nodep) {
	// Insert into symbol table, and remember what table the node is in
	m_curVarsp->insert(name, nodep);
	nodep->user3p(m_curVarsp);
	nodep->user1p(m_packagep);
    }

    AstPackage* packageFor(AstNode* nodep) {
	if (nodep) return nodep->user1p()->castNode()->castPackage();  // Loaded by symsInsert
	else return NULL;
    }

    bool linkVarName (AstVarRef* nodep) {
	// Return true if changed, and caller should end processing
	if (!nodep->varp()) {
	    AstNode* foundp = m_curVarsp->findIdUpward(nodep->name());
	    if (AstVar* varp = foundp->castVar()) {
		nodep->varp(varp);
		nodep->packagep(packageFor(varp));
	    }
	    else if (AstEnumItem* valuep = foundp->castEnumItem()) {
		AstNode* newp = new AstEnumItemRef(nodep->fileline(), valuep, packageFor(valuep));
		nodep->replaceWith(newp);
		nodep->deleteTree(); nodep=NULL;
		return true; // Edited
	    }
	}
	return false;
    }

    string nodeTextType(AstNode* nodep) {
	if (nodep->castVar()) return "variable";
	else if (nodep->castCell()) return "cell";
	else if (nodep->castTask()) return "task";
	else if (nodep->castFunc()) return "function";
	else if (nodep->castBegin()) return "block";
	else return nodep->prettyTypeName();
    }

    string ucfirst(const string& text) {
	string out = text;
	out[0] = toupper(out[0]);
	return out;
    }

    void findAndInsertAndCheck(AstNode* nodep, const string& name) {
	// Lookup the given name under current symbol table
	// Insert if not found
	// Report error if there's a duplicate
	//
	// Note we only check for conflicts at the same level; it's ok if one block hides another
	// We also wouldn't want to not insert it even though it's lower down
	AstNode* foundp = m_curVarsp->findIdFlat(name);
	if (!foundp) {
	    symsInsert(nodep->name(), nodep);
	    foundp = nodep;
	} else if (nodep==foundp) {  // Already inserted.
	    // Good.
	} else if ((nodep->castBegin() || foundp->castBegin())
		   && m_inGenerate) {
	    // Begin: ... blocks often replicate under genif/genfor, so simply suppress duplicate checks
	    // See t_gen_forif.v for an example.
	} else if (nodep->type() == foundp->type()) {
	    nodep->v3error("Duplicate declaration of "<<nodeTextType(foundp)<<": "<<nodep->prettyName());
	    foundp->v3error("... Location of original declaration");
	} else {
	    nodep->v3error("Unsupported in C: "<<ucfirst(nodeTextType(nodep))<<" has the same name as "
			   <<nodeTextType(foundp)<<": "<<nodep->prettyName());
	    foundp->v3error("... Location of original declaration");
	}
    }

    void createImplicitVar (AstVarRef* forrefp, bool noWarn) {
	// Create implicit after warning
	if (linkVarName(forrefp)) { forrefp=NULL; return; }
	if (!forrefp->varp()) {
	    if (!noWarn) {
		if (forrefp->fileline()->warnIsOff(V3ErrorCode::I_DEF_NETTYPE_WIRE)) {
		    forrefp->v3error("Signal definition not found, and implicit disabled with `default_nettype: "<<forrefp->prettyName());
		} else {
		    forrefp->v3warn(IMPLICIT,"Signal definition not found, creating implicitly: "<<forrefp->prettyName());
		}
	    }
	    AstVar* newp = new AstVar (forrefp->fileline(), AstVarType::WIRE,
				       forrefp->name(), AstLogicPacked(), 1);

	    newp->trace(m_modp->modTrace());
	    m_modp->addStmtp(newp);
	    // Link it to signal list
	    IdState old_id = m_idState;
	    V3SymTable* old_varsp = m_curVarsp;
	    m_idState = ID_FIND;
	    m_curVarsp = symsFind(m_modp);  // Must add the variable under the module; curVarsp might be lower now
	    newp->accept(*this);
	    m_idState = old_id;
	    m_curVarsp = old_varsp;
	}
    }

    // VISITs
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Top scope
	m_curVarsp = symsFindNew(nodep, NULL);
	// And recurse...
	// Recurse...
	m_idState = ID_FIND;
	nodep->iterateChildren(*this);
	if (debug()==9) m_curVarsp->dump(cout,"-curvars: ",true/*user4p_is_table*/);
	m_idState = ID_PARAM;
	nodep->iterateChildren(*this);
	m_idState = ID_RESOLVE;
	nodep->iterateChildren(*this);
	nodep->checkTree();
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Module: Create sim table for entire module and iterate
	UINFO(2,"Link Module: "<<nodep<<endl);
	if (m_idState == ID_FIND) {
	    if (nodep->fileline()->filebasenameNoExt() != nodep->prettyName()
		&& !v3Global.opt.isLibraryFile(nodep->fileline()->filename())) {
		// We only complain once per file, otherwise library-like files have a huge mess of warnings
		if (m_declfnWarned.find(nodep->fileline()->filename()) == m_declfnWarned.end()) {
		    m_declfnWarned.insert(nodep->fileline()->filename());
		    nodep->v3warn(DECLFILENAME, "Filename '"<<nodep->fileline()->filebasenameNoExt()
				  <<"' does not match "<<nodep->typeName()<<" name: "<<nodep->prettyName());
		}
	    }
	}
	AstCell* upperCellp = m_cellp;
	V3SymTable* upperVarsp = m_curVarsp;
	{
	    m_modp = nodep;
	    m_valueModp = nodep;
	    if (!m_curVarsp) nodep->v3fatalSrc("NULL");
	    if (nodep->castPackage()) m_packagep = nodep->castPackage();
	    if (m_packagep && m_packagep->isDollarUnit()) {  // $unit goes on "top"
		nodep->user4p(m_curVarsp);
		// Don't insert dunit itself, or symtable->dump will loop-recurse
	    } else {
		findAndInsertAndCheck(nodep, nodep->name());
		m_curVarsp = symsFindNew(nodep, upperVarsp);
		UINFO(9, "New module scope "<<m_curVarsp<<endl);
	    }
	    // This state must be save/restored in the cell visitor function
	    m_cellp = NULL;
	    m_cellVarsp = NULL;
	    m_paramNum = 0;
	    m_beginNum = 0;
	    m_modBeginNum = 0;
	    nodep->iterateChildren(*this);
	    // Prep for next
	    m_modp = NULL;
	    m_valueModp = NULL;
	    m_packagep = NULL;
	}
	m_curVarsp = upperVarsp;
	m_cellp = upperCellp;
    }

    virtual void visit(AstGenerate* nodep, AstNUser*) {
	// Begin: ... blocks often replicate under genif/genfor, so simply suppress duplicate checks
	// See t_gen_forif.v for an example.
	bool lastInGen = m_inGenerate;
	{
	    m_inGenerate = true;
	    nodep->iterateChildren(*this);
	}
	m_inGenerate = lastInGen;
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
	    AstNode* foundp = m_curVarsp->findIdUpward(nodep->name());
	    AstVar* findvarp = foundp->castVar();
	    bool ins=false;
	    if (!foundp) {
		ins=true;
	    } else if (!findvarp && m_curVarsp->findIdFlat(nodep->name())) {
		nodep->v3error("Unsupported in C: Variable has same name as "
			       <<nodeTextType(foundp)<<": "<<nodep->prettyName());
	    } else if (findvarp != nodep) {
		UINFO(4,"DupVar: "<<nodep<<" ;; "<<foundp<<endl);
		if (findvarp && findvarp->user3p() == m_curVarsp) {  // Only when on same level
		    if ((findvarp->isIO() && nodep->isSignal())
			|| (findvarp->isSignal() && nodep->isIO())) {
			findvarp->combineType(nodep);
			nodep->fileline()->modifyStateInherit(nodep->fileline());
			nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    } else {
			nodep->v3error("Duplicate declaration of signal: "<<nodep->prettyName());
			findvarp->v3error("... Location of original declaration");
		    }
		} else {
		    // User can disable the message at either point
		    if (!(m_ftaskp && m_ftaskp->dpiImport())
			&& !nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
			&& !foundp->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
			nodep->v3warn(VARHIDDEN,"Declaration of signal hides declaration in upper scope: "<<nodep->name());
			foundp->v3warn(VARHIDDEN,"... Location of original declaration");
		    }
		    ins = true;
		}
	    }
	    if (ins) {
		symsInsert(nodep->name(), nodep);
		if (nodep->isGParam()) {
		    m_paramNum++;
		    symsInsert("__paramNumber"+cvtToStr(m_paramNum), nodep);
		}
	    }
	}
	if (m_idState==ID_RESOLVE) {
	    if (nodep->isIO() && !m_ftaskp && !nodep->user2()) {
		nodep->v3error("Input/output/inout does not appear in port list: "<<nodep->prettyName());
	    }
	    // temporaries under an always aren't expected to be blocking
	    if (m_inAlways) nodep->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
	    if (nodep->valuep()) {
		// A variable with a = value can be three things:
		FileLine* fl = nodep->valuep()->fileline();
		// 1. Parameters and function inputs: It's a default to use if not overridden
		if (nodep->isParam() || nodep->isInOnly()) {
		// 2. Under modules, it's an initial value to be loaded at time 0 via an AstInitial
		} else if (m_valueModp) {
		    nodep->addNextHere
			(new AstInitial (fl, new AstAssign (fl,
							    new AstVarRef(fl, nodep, true),
							    nodep->valuep()->unlinkFrBack())));
		// 3. Under blocks, it's an initial value to be under an assign
		} else {
		    nodep->addNextHere
			(new AstAssign (fl, new AstVarRef(fl, nodep, true),
					nodep->valuep()->unlinkFrBack()));
		}
	    }
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// VarRef: Resolve its reference
	nodep->iterateChildren(*this);
	if (m_idState==ID_RESOLVE && !nodep->varp()) {
	    if (linkVarName(nodep)) { nodep=NULL; return; }
	    if (!nodep->varp()) {
		nodep->v3error("Can't find definition of signal: "<<nodep->prettyName());
		createImplicitVar (nodep, true);  // So only complain once
	    }
	}
    }
    //virtual void visit(AstVarXRef* nodep, AstNUser*) {
    // See LinkDotVisitor
    //}

    virtual void visit(AstEnumItem* nodep, AstNUser*) {
	// EnumItem: Remember its name for later resolution
	nodep->iterateChildren(*this);
	if (m_idState==ID_FIND) {
	    // Find under either a task or the module's vars
	    AstNode* foundp = m_curVarsp->findIdUpward(nodep->name());
	    AstEnumItem* findvarp = foundp->castEnumItem();
	    bool ins=false;
	    if (!foundp) {
		ins=true;
	    } else if (findvarp != nodep) {
		UINFO(4,"DupVar: "<<nodep<<" ;; "<<foundp<<endl);
		if (findvarp && findvarp->user3p() == m_curVarsp) {  // Only when on same level
		    nodep->v3error("Duplicate declaration of enum value: "<<nodep->prettyName());
		    findvarp->v3error("... Location of original declaration");
		} else {
		    // User can disable the message at either point
		    if (!nodep->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)
			&& !foundp->fileline()->warnIsOff(V3ErrorCode::VARHIDDEN)) {
			nodep->v3warn(VARHIDDEN,"Declaration of enum value hides declaration in upper scope: "<<nodep->name());
			foundp->v3warn(VARHIDDEN,"... Location of original declaration");
		    }
		    ins = true;
		}
	    }
	    if (ins) {
		symsInsert(nodep->name(), nodep);
	    }
	}
    }

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// NodeTask: Remember its name for later resolution
	if (!m_curVarsp) nodep->v3fatalSrc("Function/Task not under module??\n");
	// Remember the existing symbol table scope
	V3SymTable* upperVarsp = m_curVarsp;
	AstNodeModule* upperValueModp = m_valueModp;
	{
	    m_valueModp = NULL;

	    // Create symbol table for the task's vars
	    m_curVarsp = symsFindNew(nodep, upperVarsp);

	    // Convert the func's range to the output variable
	    // This should probably be done in the Parser instead, as then we could
	    // just attact normal signal attributes to it.
	    if (nodep->fvarp()
		&& !nodep->fvarp()->castVar()) {
		AstNodeDType* dtypep = nodep->fvarp()->castNodeDType();
		// If unspecified, function returns one bit; however when we support NEW() it could
		// also return the class reference.
		if (dtypep) dtypep->unlinkFrBack();
		else dtypep = new AstBasicDType(nodep->fileline(), AstBasicDTypeKwd::LOGIC);
		AstVar* newvarp = new AstVar(nodep->fileline(), AstVarType::OUTPUT, nodep->name(), dtypep);
		if (nodep->isSigned()) newvarp->numeric(AstNumeric::SIGNED);
		newvarp->funcReturn(true);
		newvarp->trace(false);  // Not user visible
		newvarp->attrIsolateAssign(nodep->attrIsolateAssign());
		nodep->addFvarp(newvarp);
		// Explicit insert required, as the var name shadows the upper level's task name
		symsInsert(newvarp->name(), newvarp);
	    }
	    m_ftaskp = nodep;
	    nodep->iterateChildren(*this);
	    m_ftaskp = NULL;
	}
	m_curVarsp = upperVarsp;
	m_valueModp = upperValueModp;
	if (m_idState==ID_FIND) {
	    findAndInsertAndCheck(nodep, nodep->name());
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
	if (m_idState==ID_FIND && nodep->name()=="" && nodep->unnamed()) {
	    // Unnamed blocks are only important when they contain var
	    // decls, so search for them. (Otherwise adding all the
	    // unnamed#'s would just confuse tracing variables in
	    // places such as tasks, where "task ...; begin ... end"
	    // are common.
	    for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp=stmtp->nextp()) {
		if (stmtp->castVar()) {
		    ++m_modBeginNum;
		    nodep->name("unnamedblk"+cvtToStr(m_modBeginNum));
		    break;
		}
	    }
	}

	// Check naming (we don't really care, but some tools do, so better to warn)
	if (m_idState==ID_FIND && nodep->name()!="") {
	    findAndInsertAndCheck(nodep, nodep->name());
	}
	// Recurse
	int oldNum = m_beginNum;
	if (!nodep->hidden()) m_beginNum = 0;
	{
	    // Create symbol table for the task's vars
	    m_curVarsp = symsFindNew(nodep, upperVarsp);
	    nodep->iterateChildren(*this);
	}
	m_curVarsp = upperVarsp;
	m_beginNum = oldNum;
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// NodeFTaskRef: Resolve its reference
	if (m_idState==ID_RESOLVE && !nodep->taskp()) {
	    if (nodep->dotted() == "") {
		AstNodeFTask* taskp;
		if (nodep->packagep()) {
		    taskp = symsFind(nodep->packagep())->findIdUpward(nodep->name())->castNodeFTask();
		} else {
		    taskp = m_curVarsp->findIdUpward(nodep->name())->castNodeFTask();
		}
		if (!taskp) { nodep->v3error("Can't find definition of task/function: "<<nodep->prettyName()); }
		nodep->taskp(taskp);
		nodep->packagep(packageFor(taskp));
		if (taskp->castTask() && nodep->castFuncRef()) nodep->v3error("Illegal call of a task as a function: "<<nodep->prettyName());
	    }
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstDpiExport* nodep, AstNUser*) {
	// AstDpiExport: Make sure the function referenced exists, then dump it
	nodep->iterateChildren(*this);
	if (m_idState==ID_RESOLVE) {
	    AstNodeFTask* taskp;
	    taskp = m_curVarsp->findIdUpward(nodep->name())->castNodeFTask();
	    if (!taskp) { nodep->v3error("Can't find definition of exported task/function: "<<nodep->prettyName()); }
	    else if (taskp->dpiExport()) {
		nodep->v3error("Function was already DPI Exported, duplicate not allowed: "<<nodep->prettyName());
	    } else {
		taskp->dpiExport(true);
		if (nodep->cname()!="") taskp->cname(nodep->cname());
	    }
	    nodep->unlinkFrBack()->deleteTree();
	}
    }

    virtual void visit(AstTypedef* nodep, AstNUser*) {
	// Remember its name for later resolution
	if (!m_curVarsp) nodep->v3fatalSrc("Typedef not under module??\n");
	nodep->iterateChildren(*this);
	if (m_idState==ID_FIND) {
	    findAndInsertAndCheck(nodep, nodep->name());
	}
    }
    virtual void visit(AstTypedefFwd* nodep, AstNUser*) {
	// We only needed the forward declaration in order to parse correctly.
	// We won't even check it was ever really defined, as it might have been in a header
	// file referring to a module we never needed
	nodep->unlinkFrBack()->deleteTree();
    }
    virtual void visit(AstRefDType* nodep, AstNUser*) {
	// Resolve its reference
	if (m_idState==ID_RESOLVE && !nodep->defp()) {
	    AstTypedef* defp;
	    if (nodep->packagep()) {
		defp = symsFind(nodep->packagep())->findIdFlat(nodep->name())->castTypedef();
	    } else {
		defp = m_curVarsp->findIdUpward(nodep->name())->castTypedef();
	    }
	    if (!defp) { nodep->v3error("Can't find typedef: "<<nodep->prettyName()); }
	    nodep->defp(defp->dtypep());
	    nodep->packagep(packageFor(defp));
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	// Cell: Resolve its filename.  If necessary, parse it.
	m_cellp = nodep;
	AstNode::user5ClearTree();
	if (m_idState==ID_FIND) {
	    // Add to list of all cells, for error checking and defparam's
	    findAndInsertAndCheck(nodep, nodep->name());
	}
	if (!nodep->modp()) {
	    nodep->v3fatalSrc("Cell has unlinked module"); // V3LinkCell should have errored out
	}
	else {
	    if (nodep->modp()->castNotFoundModule()) {
		// Prevent warnings about missing pin connects
		if (nodep->pinsp()) nodep->pinsp()->unlinkFrBackWithNext()->deleteTree();
		if (nodep->paramsp()) nodep->paramsp()->unlinkFrBackWithNext()->deleteTree();
	    }
	    // Need to pass the module info to this cell, so we can link up the pin names
	    else if (m_idState==ID_RESOLVE) {
		m_cellVarsp = nodep->modp()->user4p()->castSymTable();
		UINFO(4,"(Backto) Link Cell: "<<nodep<<endl);
		//if (debug()) { nodep->dumpTree(cout,"linkcell:"); }
		//if (debug()) { nodep->modp()->dumpTree(cout,"linkcemd:"); }
		nodep->iterateChildren(*this);
		m_cellVarsp = NULL;
	    }
	    else if (m_idState==ID_PARAM) {
		nodep->iterateChildren(*this);
	    }
	}
	m_cellp = NULL;
	// Parent module inherits child's publicity
	// This is done bottom up in the LinkBotupVisitor stage
    }

    virtual void visit(AstPort* nodep, AstNUser*) {
	// Port: Stash the pin number
	if (!m_curVarsp) nodep->v3fatalSrc("Port not under module??\n");
	if (m_idState==ID_PARAM) {
	    // Need to set pin numbers after varnames are created
	    // But before we do the final resolution based on names
	    AstVar* refp = m_curVarsp->findIdFlat(nodep->name())->castVar();
	    if (!refp) {
		nodep->v3error("Input/output/inout declaration not found for port: "<<nodep->prettyName());
	    } else if (!refp->isIO()) {
		nodep->v3error("Pin is not an in/out/inout: "<<nodep->prettyName());
	    } else {
		symsInsert("__pinNumber"+cvtToStr(nodep->pinNum()), refp);
		refp->user2(true);
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
	// These are perhaps a little too generous, as a SELect of siga[sigb]
	// perhaps shouldn't create an implicit variable.  But, we've warned...
	else {
	    if (nodep->op1p()) pinImplicitExprRecurse(nodep->op1p());
	    if (nodep->op2p()) pinImplicitExprRecurse(nodep->op2p());
	    if (nodep->op3p()) pinImplicitExprRecurse(nodep->op3p());
	    if (nodep->op4p()) pinImplicitExprRecurse(nodep->op4p());
	    if (nodep->nextp()) pinImplicitExprRecurse(nodep->nextp());
	}
    }

    virtual void visit(AstPin* nodep, AstNUser*) {
	// Pin: Link to submodule's port
	// ONLY CALLED by AstCell during ID_RESOLVE and ID_PARAM state
	if (m_idState==ID_RESOLVE && !nodep->modVarp()) {
	    if (!m_cellVarsp) nodep->v3fatalSrc("Pin not under cell?\n");
	    AstVar* refp = m_cellVarsp->findIdFlat(nodep->name())->castVar();
	    if (!refp) {
		if (nodep->name() == "__paramNumber1" && m_cellp->modp()->castPrimitive()) {
		    // Primitive parameter is really a delay we can just ignore
		    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    return;
		}
		nodep->v3error("Pin not found: "<<nodep->prettyName());
	    } else if (!refp->isIO() && !refp->isParam()) {
		nodep->v3error("Pin is not an in/out/inout/param: "<<nodep->prettyName());
	    } else {
		nodep->modVarp(refp);
		if (refp->user5p() && refp->user5p()->castNode()!=nodep) {
		    nodep->v3error("Duplicate pin connection: "<<nodep->prettyName());
		    refp->user5p()->castNode()->v3error("... Location of original pin connection");
		} else {
		    refp->user5p(nodep);
		}
	    }
	    if (!nodep->exprp()) {
		// It's an empty pin connection, done with it.
		// (We used to not create pins for these, but we'd miss
		// warns.  Perhaps they should live even further...)
		pushDeletep(nodep->unlinkFrBack()); nodep=NULL;
		return;
	    }
	    nodep->iterateChildren(*this);
	}
	// Deal with implicit definitions - do before ID_RESOLVE stage as may be referenced above declaration
	if (m_idState==ID_PARAM
	    && nodep->exprp() // Else specifically unconnected pin
	    && !nodep->svImplicit()) {   // SV 19.11.3: .name pins don't allow implicit decls
	    pinImplicitExprRecurse(nodep->exprp());
	}
	// Early return() above when deleted
    }

    virtual void visit(AstAssignW* nodep, AstNUser*) {
	// Deal with implicit definitions
	// We used to nodep->allowImplicit() here, but it turns out
	// normal "assigns" can also make implicit wires.  Yuk.
	pinImplicitExprRecurse(nodep->lhsp());
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	// tran gates need implicit creation
	if (AstVarRef* forrefp = nodep->lhsp()->castVarRef()) {
	    createImplicitVar(forrefp, false);
	}
	if (AstVarRef* forrefp = nodep->rhsp()->castVarRef()) {
	    createImplicitVar(forrefp, false);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstImplicit* nodep, AstNUser*) {
	// Unsupported gates need implicit creation
	pinImplicitExprRecurse(nodep);
	// We're done with implicit gates
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
    }

    virtual void visit(AstDefParam* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_idState==ID_PARAM) {
	    nodep->v3warn(DEFPARAM,"Suggest replace defparam with Verilog 2001 #(."<<nodep->name()<<"(...etc...))");
	    AstNode* foundp = m_curVarsp->findIdUpward(nodep->path());
	    AstCell* cellp = foundp->castCell();
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

    virtual void visit(AstPackageImport* nodep, AstNUser*) {
	UINFO(2,"  Link: "<<nodep<<endl);
	V3SymTable* srcp = symsFind(nodep->packagep());
	if (nodep->name()!="*") {
	    AstNode* impp = srcp->findIdFlat(nodep->name());
	    if (!impp) {
		nodep->v3error("Import object not found: "<<nodep->packagep()->prettyName()<<"::"<<nodep->prettyName());
	    }
	}
	m_curVarsp->import(srcp, nodep->name());
	// No longer needed
	nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
    }

    void visitIterateNoValueMod(AstNode* nodep) {
	// Iterate a node which shouldn't have any local variables moved to an Initial
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
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkVisitor(AstNetlist* rootp) {
	m_curVarsp = NULL;
	m_cellVarsp = NULL;
	m_cellp = NULL;
	m_modp = NULL;
	m_ftaskp = NULL;
	m_packagep = NULL;
	m_paramNum = 0;
	m_beginNum = 0;
	m_modBeginNum = 0;
	m_inAlways = false;
	m_inGenerate = false;
	m_valueModp = NULL;
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
