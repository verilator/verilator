// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Combine common code into functions
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
// V3Combine's Transformations:
//
//	For every function that we spit out
//	Examine code to find largest common blocks
//	    Hash each node depth first
//		Hash includes varp name and operator type, and constants
//		Form lookup table based on hash of each statement  w/ nodep and next nodep
//	    GO through table
//		Lookup in hash, while next of each statement match, grow that common block
//	Foreach common block
//	    If common block large enough (> 20 statements) & used 2x or more
//		Make new function
//		Move common block to function
//		Replace each common block ref with funccall
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>
#include <map>

#include "V3Global.h"
#include "V3Combine.h"
#include "V3Hashed.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################

#define COMBINE_MIN_STATEMENTS 50	// Min # of statements to be worth making a function

//######################################################################

class CombBaseVisitor : public AstNVisitor {
protected:
    // STATE

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    virtual ~CombBaseVisitor() {}

    //***** optimization levels
    static bool emptyFunctionDeletion() { return true; }
    static bool duplicateFunctionCombine() { return true; }
    // Note this is disabled, it still needed work
    // Also repair it for DPI functions; when make __common need to insure proper
    // flags get inherited from the old to new AstCFunc, and that AstText doesn't
    // get split between functions causing the text to have a danginling reference.
    bool statementCombine() { return false && duplicateFunctionCombine(); }
};

//######################################################################
// Combine replacement function

class CombCallVisitor : CombBaseVisitor {
    // Find all CCALLS of each CFUNC, so that we can later rename them
private:
    // NODE STATE
    bool	m_find;		// Find mode vs. delete mode
    typedef multimap<AstCFunc*,AstCCall*> CallMmap;
    CallMmap	m_callMmap;	// Associative array of {function}{call}
    // METHODS
public:
    void replaceFunc (AstCFunc* oldfuncp, AstCFunc* newfuncp) {
	if (oldfuncp==newfuncp) return;
	if (newfuncp) {
	    UINFO(4, "   Replace "<<oldfuncp<<" -WITH-> "<<newfuncp<<endl);
	} else UINFO(4, "   Remove "<<oldfuncp<<endl);
	pair <CallMmap::iterator,CallMmap::iterator> eqrange = m_callMmap.equal_range(oldfuncp);
	for (CallMmap::iterator nextit = eqrange.first; nextit != eqrange.second;) {
	    CallMmap::iterator eqit = nextit++;
	    AstCCall* callp = eqit->second;
	    if (!callp->user3()) {  // !already done
		UINFO(4, "     Called "<<callp<<endl);
		if (callp->funcp() != oldfuncp) callp->v3fatalSrc("Call list broken, points to call w/different func");
		if (newfuncp) {
		    AstCCall* newp = new AstCCall(callp, newfuncp);
		    // Special new AstCCall form above transfers children of callp to newfuncp
		    callp->replaceWith(newp);
		    addCall(newp); // Fix the table
		} else { // Just deleting empty function
		    callp->unlinkFrBack();
		}
		callp->user3(true);	// Dead now
		pushDeletep(callp); callp=NULL;
		m_callMmap.erase(eqit);	// Fix the table
	    }
	}
    }
    // METHODS
    void addCall(AstCCall* nodep) {
	m_callMmap.insert(make_pair(nodep->funcp(), nodep));
    }
    void deleteCall(AstCCall* nodep) {
	pair <CallMmap::iterator,CallMmap::iterator> eqrange = m_callMmap.equal_range(nodep->funcp());
	for (CallMmap::iterator nextit = eqrange.first; nextit != eqrange.second;) {
	    CallMmap::iterator eqit = nextit++;
	    AstCCall* callp = eqit->second;
	    if (callp==nodep) {
		m_callMmap.erase(eqit);
		return;
	    }
	}
	nodep->v3fatalSrc("deleteCall node not found in table");
    }
private:
    // VISITORS
    virtual void visit(AstCCall* nodep, AstNUser*) {
	addCall(nodep);
    }
    // Speed things up
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {}
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    CombCallVisitor() {
	m_find = false;
    }
    virtual ~CombCallVisitor() {}
    void main(AstNetlist* nodep) {
	nodep->accept(*this);
    }
};

//######################################################################
// Combine marking function

class CombMarkVisitor : CombBaseVisitor {
    // Mark all nodes under specified one.
private:
    // OUTPUT:
    //  AstNode::user3()	-> bool. True to indicate duplicated
    // VISITORS
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->user3(true);
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    CombMarkVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~CombMarkVisitor() {}
};

//######################################################################
// Combine state, as a visitor of each AstNode

class CombineVisitor : CombBaseVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNodeStmt::user()	-> bool.  True if iterated already
    //  AstCFunc::user3p()	-> AstCFunc*, If set, replace ccalls to this func with new func
    //  AstNodeStmt::user3()	-> AstNode*.  True if to ignore this cell
    //  AstNodeStmt::user4()	-> V3Hashed::V3Hash.  Hash value of this node (hash of 0 is illegal)
    AstUser1InUse	m_inuser1;
    AstUser3InUse	m_inuser3;
    //AstUser4InUse	part of V3Hashed

    // STATE
    typedef enum {STATE_IDLE, STATE_HASH, STATE_DUP} CombineState;
    V3Double0		m_statCombs;	// Statistic tracking
    CombineState	m_state;	// Major state
    AstNodeModule*	m_modp;		// Current module
    AstCFunc*		m_funcp;	// Current function
    V3Hash		m_lowerHash;	// Hash of the statement we're building
    CombCallVisitor	m_call;		// Tracking of function call users
    int			m_modNFuncs;	// Number of functions made
    AstNode*		m_walkLast1p;	// Final node that is the same in duplicate list
    AstNode*		m_walkLast2p;	// Final node that is the same in duplicate list
    V3Hashed		m_hashed;	// Hash for every node in module

    // METHODS
    void hashStatement(AstNode* nodep) {
	// Compute hash on entire tree of this statement
	m_hashed.hashAndInsert(nodep);
	//UINFO(9,"  stmthash "<<hex<<nodep->user4()<<"  "<<nodep<<endl);
    }
    void hashFunctions(AstCFunc* nodep) {
	// Compute hash of all statement trees in the function
	CombineState oldState = m_state;
	{
	    m_state = STATE_HASH;
	    nodep->accept(*this);
	}
	m_state = oldState;
    }
    void walkEmptyFuncs() {
	for (V3Hashed::iterator it = m_hashed.begin(); it != m_hashed.end(); ++it) {
	    AstNode* node1p = it->second;
	    AstCFunc* oldfuncp = node1p->castCFunc();
	    if (oldfuncp
		&& oldfuncp->emptyBody()
		&& !oldfuncp->dontCombine()) {
		UINFO(5,"     EmptyFunc "<<hex<<V3Hash(oldfuncp->user4p())<<" "<<oldfuncp<<endl);
		// Mark user3p on entire old tree, so we don't process it more
		CombMarkVisitor visitor(oldfuncp);
		m_call.replaceFunc(oldfuncp, NULL);
		oldfuncp->unlinkFrBack();
		pushDeletep(oldfuncp); oldfuncp=NULL;
	    }
	}
    }
    void walkDupFuncs() {
	for (V3Hashed::iterator it = m_hashed.begin(); it != m_hashed.end(); ++it) {
	    V3Hash hashval = it->first;
	    AstNode* node1p = it->second;
	    if (!node1p->castCFunc()) continue;
	    if (hashval.isIllegal()) node1p->v3fatalSrc("Illegal (unhashed) nodes\n");
	    for (V3Hashed::iterator eqit = it; eqit != m_hashed.end(); ++eqit) {
		AstNode* node2p = eqit->second;
		if (!(eqit->first == hashval)) break;
		if (node1p==node2p) continue;  // Identical iterator
		if (node1p->user3p() || node2p->user3p()) continue;   // Already merged
		if (node1p->sameTree(node2p)) { // walk of tree has same comparison
		    // Replace AstCCall's that point here
		    replaceFuncWFunc(node2p->castCFunc(), node1p->castCFunc());
		    // Replacement may promote a slow routine to fast path
		    if (!node2p->castCFunc()->slow()) node1p->castCFunc()->slow(false);
		}
	    }
	}
    }
    void replaceFuncWFunc(AstCFunc* oldfuncp, AstCFunc* newfuncp) {
	UINFO(5,"     DupFunc "<<hex<<V3Hash(newfuncp->user4p())<<" "<<newfuncp<<endl);
	UINFO(5,"         and "<<hex<<V3Hash(oldfuncp->user4p())<<" "<<oldfuncp<<endl);
	// Mark user3p on entire old tree, so we don't process it more
	++m_statCombs;
	CombMarkVisitor visitor(oldfuncp);
	m_call.replaceFunc(oldfuncp, newfuncp);
	oldfuncp->unlinkFrBack();
	pushDeletep(oldfuncp); oldfuncp=NULL;
    }
    void replaceOnlyCallFunc(AstCCall* nodep) {
	if (AstCFunc* oldfuncp = nodep->backp()->castCFunc()) {
	    //oldfuncp->dumpTree(cout,"MAYDEL: ");
	    if (nodep->nextp()==NULL
		&& oldfuncp->initsp()==NULL
		&& oldfuncp->stmtsp()==nodep
		&& oldfuncp->finalsp()==NULL) {
		UINFO(9,"     Function only has call "<<oldfuncp<<endl);
		m_call.deleteCall(nodep);
		CombMarkVisitor visitor(oldfuncp);
		replaceFuncWFunc(oldfuncp, nodep->funcp());  nodep=NULL;
	    }
	}
    }

    void walkDupCodeStart(AstNode* node1p) {
	V3Hash hashval (node1p->user4p());
	//UINFO(4,"    STMT "<<hashval<<" "<<node1p<<endl);
	//
	int	 bestDepth = 0;		// Best substitution found in the search
	AstNode* bestNode2p = NULL;
	AstNode* bestLast1p = NULL;
	AstNode* bestLast2p = NULL;
	//
	pair <V3Hashed::iterator,V3Hashed::iterator> eqrange = m_hashed.mmap().equal_range(hashval);
	for (V3Hashed::iterator eqit = eqrange.first; eqit != eqrange.second; ++eqit) {
	    AstNode* node2p = eqit->second;
	    if (node1p==node2p) continue;
	    //
	    // We need to mark iteration to prevent matching code inside code (abab matching in ababab)
	    AstNode::user1ClearTree();	// user1p() used on entire tree
	    m_walkLast1p = NULL;
	    m_walkLast2p = NULL;
	    int depth = walkDupCodeNext(node1p, node2p, 1);
	    if (depth>COMBINE_MIN_STATEMENTS
		&& depth>bestDepth) {
		bestDepth = depth;
		bestNode2p = node2p;
		bestLast1p = m_walkLast1p;
		bestLast2p = m_walkLast2p;
	    }
	}
	if (bestDepth) {
	    // Found a replacement
	    UINFO(5,"     Duplicate of depth "<<bestDepth<<endl);
	    UINFO(5,"       DupFunc "<<" "<<node1p<<endl);
	    UINFO(5,"           and "<<" "<<bestNode2p<<endl);
	    UINFO(5,"       Through "<<" "<<bestLast1p<<endl);
	    UINFO(5,"           and "<<" "<<bestLast2p<<endl);
	    //
	    walkReplace(node1p, bestNode2p, bestLast1p, bestLast2p);
	}
    }

    int walkDupCodeNext(AstNode* node1p, AstNode* node2p, int level) {
	// Find number of common statements between the two node1p_nextp's...
	if (node1p->user1p() || node2p->user1p()) return 0;   // Already iterated
	if (node1p->user3p() || node2p->user3p()) return 0;   // Already merged
	if (!m_hashed.sameNodes(node1p,node2p)) return 0; // walk of tree has same comparison
	V3Hash hashval(node1p->user4p());
	//UINFO(9,"        wdup1 "<<level<<" "<<V3Hash(node1p->user4p())<<" "<<node1p<<endl);
	//UINFO(9,"        wdup2 "<<level<<" "<<V3Hash(node2p->user4p())<<" "<<node2p<<endl);
	m_walkLast1p = node1p;
	m_walkLast2p = node2p;
	node1p->user1(true);
	node2p->user1(true);
	if (node1p->nextp() && node2p->nextp()) {
	    return hashval.depth()+walkDupCodeNext(node1p->nextp(), node2p->nextp(), level+1);
	}
	return hashval.depth();
    }

    void walkReplace(AstNode* node1p, AstNode* node2p,
		     AstNode* last1p, AstNode* last2p) {  // Final node in linked list, maybe null if all statements to be grabbed
	// Make new function
	string oldname = m_funcp->name();
	string::size_type pos;
	if ((pos=oldname.find("_common")) != string::npos) {
	    oldname.erase(pos);
	}
	if ((pos=oldname.find("__")) != string::npos) {
	    oldname.erase(pos);
	}
	AstCFunc* newfuncp = new AstCFunc(node1p->fileline(),
					  oldname+"_common"+cvtToStr(++m_modNFuncs),
					  NULL);
	m_modp->addStmtp(newfuncp);
	// Create calls
	AstCCall* call1p = new AstCCall(node1p->fileline(), newfuncp);
	AstCCall* call2p = new AstCCall(node2p->fileline(), newfuncp);
	// Grab statement bodies
	AstNRelinker relink1Handle;
	AstNRelinker relink2Handle;
	for (AstNode* nextp, *walkp = node1p; 1; walkp = nextp) {
	    nextp = walkp->nextp();
	    if (walkp==node1p) 	walkp->unlinkFrBack(&relink1Handle);
	    else { walkp->unlinkFrBack(); node1p->addNext(walkp); }
	    if (walkp==last1p) break;
	}
	for (AstNode* nextp, *walkp = node2p; 1; walkp = nextp) {
	    nextp = walkp->nextp();
	    if (walkp==node2p) 	walkp->unlinkFrBack(&relink2Handle);
	    else { walkp->unlinkFrBack(); node2p->addNext(walkp); }
	    if (walkp==last2p) break;
	}
	// Move node1 statements to new function
	newfuncp->addStmtsp(node1p);
	//newfuncp->dumpTree(cout," newfunctree: ");
	// Mark node2 statements as dead
	CombMarkVisitor visitor(node2p);
	pushDeletep(node2p);	// Delete later
	// Link in new function
	relink1Handle.relink(call1p);
	relink2Handle.relink(call2p);
	// Hash the new function
	hashFunctions(newfuncp);
	m_call.addCall(call1p);
	m_call.addCall(call2p);
	// If either new statement makes a func with only a single call, replace
	// the above callers to call it directly
	replaceOnlyCallFunc(call1p); call1p=NULL;
	replaceOnlyCallFunc(call2p); call2p=NULL;
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Track all callers of each function
	m_call.main(nodep);
	//
	//In V3Hashed AstNode::user4ClearTree();	// user4p() used on entire tree
	// Iterate modules backwards, in bottom-up order.
	// Required so that a module instantiating another can benefit from collapsing.
	nodep->iterateChildrenBackwards(*this);
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_modNFuncs = 0;
	m_hashed.clear();
	// Compute hash of all statement trees in the function
	m_state = STATE_HASH;
	nodep->iterateChildren(*this);
	m_state = STATE_IDLE;
	if (debug()>=9) {
	    m_hashed.dumpFilePrefixed("combine");
	}
	// Walk the hashes removing empty functions
	if (emptyFunctionDeletion()) {
	    walkEmptyFuncs();
	}
	// Walk the hashes looking for duplicate functions
	if (duplicateFunctionCombine()) {
	    walkDupFuncs();
	}
	// Walk the statements looking for large replicated code sections
	if (statementCombine()) {
	    m_state = STATE_DUP;
	    nodep->iterateChildren(*this);
	    m_state = STATE_IDLE;
	}
	m_modp = NULL;
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_funcp = nodep;
	if (!nodep->dontCombine()) {
	    if (m_state == STATE_HASH) {
		hashStatement(nodep);  // Hash the entire function - it might be identical
	    } else if (m_state == STATE_DUP) {
		nodep->iterateChildren(*this);
	    }
	}
	m_funcp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	if (m_state == STATE_HASH && m_funcp) {
	    hashStatement(nodep);
	}
	else if (m_state == STATE_DUP && m_funcp) {
	    walkDupCodeStart(nodep);
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*, AstNUser*) {}
    virtual void visit(AstTraceDecl*, AstNUser*) {}
    virtual void visit(AstTraceInc*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    CombineVisitor(AstNetlist* nodep) {
	m_modp=NULL;
	m_funcp = NULL;
	m_state = STATE_IDLE;
	nodep->accept(*this);
    }
    virtual ~CombineVisitor() {
	V3Stats::addStat("Optimizations, Combined CFuncs", m_statCombs);
    }
};

//######################################################################
// Combine class functions

void V3Combine::combineAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CombineVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("combine.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
