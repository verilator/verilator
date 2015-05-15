// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
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
// V3Broken's Transformations:
//
// Entire netlist
//	Mark all nodes
//	Check all links point to marked nodes
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <map>

#include "V3Global.h"
#include "V3Broken.h"
#include "V3Ast.h"

// This visitor does not edit nodes, and is called at error-exit, so should use constant iterators
#include "V3AstConstOnly.h"

//######################################################################

class BrokenTable : public AstNVisitor {
    // Table of brokenExists node pointers
private:
    // MEMBERS
    //   For each node, we keep if it exists or not.
    typedef map<const AstNode*,int> NodeMap;
    static NodeMap s_nodes;	// Set of all nodes that exist
    // BITMASK
    enum { FLAG_ALLOCATED	= 0x01 };	// new() and not delete()ed
    enum { FLAG_IN_TREE		= 0x02 };	// Is in netlist tree
    enum { FLAG_LINKABLE	= 0x04 };	// Is in netlist tree, can be linked to
    enum { FLAG_LEAKED		= 0x08 };	// Known to have been leaked
    enum { FLAG_UNDER_NOW	= 0x10 };	// Is in tree as parent of current node
public:
    // METHODS
    static void deleted(const AstNode* nodep) {
	// Called by operator delete on any node - only if VL_LEAK_CHECKS
	if (debug()>=9) cout<<"-nodeDel:  "<<(void*)(nodep)<<endl;
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter==s_nodes.end() || !(iter->second & FLAG_ALLOCATED)) {
	    ((AstNode*)(nodep))->v3fatalSrc("Deleting AstNode object that was never tracked or already deleted\n");
	}
	if (iter!=s_nodes.end()) s_nodes.erase(iter);
    }
    static void addNewed(const AstNode* nodep) {
	// Called by operator new on any node - only if VL_LEAK_CHECKS
	if (debug()>=9) cout<<"-nodeNew:  "<<(void*)(nodep)<<endl;
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter!=s_nodes.end() || (iter->second & FLAG_ALLOCATED)) {
	    ((AstNode*)(nodep))->v3fatalSrc("Newing AstNode object that is already allocated\n");
	}
	if (iter == s_nodes.end()) {
	    int flags = FLAG_ALLOCATED;  // This int needed to appease GCC 4.1.2
	    s_nodes.insert(make_pair(nodep,flags));
	}
    }
    static void setUnder(const AstNode* nodep, bool flag) {
	// Called by BrokenCheckVisitor when each node entered/exited
	if (!okIfLinkedTo(nodep)) return;
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter!=s_nodes.end()) {
	    iter->second &= ~FLAG_UNDER_NOW;
	    if (flag) iter->second |=  FLAG_UNDER_NOW;
	}
    }
    static void addInTree(AstNode* nodep, bool linkable) {
#ifndef VL_LEAK_CHECKS
	if (!linkable) return;  // save some time, else the map will get huge!
#endif
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter == s_nodes.end()) {
#ifdef VL_LEAK_CHECKS
	    nodep->v3fatalSrc("AstNode is in tree, but not allocated\n");
#endif
	} else {
	    if (!(iter->second & FLAG_ALLOCATED)) {
#ifdef VL_LEAK_CHECKS
		nodep->v3fatalSrc("AstNode is in tree, but not allocated\n");
#endif
	    }
	    if (iter->second & FLAG_IN_TREE) {
		nodep->v3fatalSrc("AstNode is already in tree at another location\n");
	    }
	}
	int or_flags = FLAG_IN_TREE | (linkable?FLAG_LINKABLE:0);
	if (iter == s_nodes.end()) {
	    s_nodes.insert(make_pair(nodep,or_flags));
	} else {
	    iter->second |= or_flags;
	}
    }
    static bool okIfLinkedTo(const AstNode* nodep) {
	// Someone has a pointer to this node.  Is it kosher?
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter == s_nodes.end()) return false;
#ifdef VL_LEAK_CHECKS
	if (!(iter->second & FLAG_ALLOCATED)) return false;
#endif
	if (!(iter->second & FLAG_IN_TREE)) return false;
	if (!(iter->second & FLAG_LINKABLE)) return false;
	return true;
    }
    static bool okIfBelow(const AstNode* nodep) {
	// Must be linked to and below current node
	if (!okIfLinkedTo(nodep)) return false;
	NodeMap::iterator iter = s_nodes.find(nodep);
	if (iter == s_nodes.end()) return false;
	if (!(iter->second & FLAG_UNDER_NOW)) return false;
	return true;
    }
    static void prepForTree() {
#ifndef VL_LEAK_CHECKS
	s_nodes.clear();
#endif
	for (NodeMap::iterator it = s_nodes.begin(); it != s_nodes.end(); ++it) {
	    it->second &= ~FLAG_IN_TREE;
	    it->second &= ~FLAG_LINKABLE;
	}
    }
    static void doneWithTree() {
	for (int backs=0; backs<2; backs++) {  // Those with backp() are probably under one leaking without
	    for (NodeMap::iterator it = s_nodes.begin(); it != s_nodes.end(); ++it) {
		if ((it->second & FLAG_ALLOCATED)
		    && !(it->second & FLAG_IN_TREE)
		    && !(it->second & FLAG_LEAKED)
		    && (it->first->backp() ? backs==1 : backs==0)) {
		    // Use only AstNode::dump instead of the virtual one, as there
		    // may be varp() and other cross links that are bad.
		    if (v3Global.opt.debugCheck()) {
			cerr<<"%Error: LeakedNode"<<(it->first->backp()?"Back: ":": ");
			((AstNode*)(it->first))->AstNode::dump(cerr);
			cerr<<endl;
			V3Error::incErrors();
		    }
		    it->second |= FLAG_LEAKED;
		}
	    }
	}
    }
public:
    // CONSTUCTORS
    BrokenTable() {}
    virtual ~BrokenTable() {}
};

BrokenTable::NodeMap BrokenTable::s_nodes;

bool AstNode::brokeExists() const {
    // Called by node->broken() routines to do table lookup
    return BrokenTable::okIfLinkedTo(this);
}
bool AstNode::brokeExistsAbove() const {
    // Called by node->broken() routines to do table lookup
    return BrokenTable::okIfBelow(this);
}

//######################################################################

class BrokenMarkVisitor : public AstNVisitor {
    // Mark every node in the tree
private:
    // NODE STATE
    //  Nothing!	// This may be called deep inside other routines
    //			// so userp and friends may not be used
    // VISITORS
    virtual void visit(AstNode* nodep, AstNUser*) {
	BrokenTable::addInTree(nodep, nodep->maybePointedTo());
	nodep->iterateChildrenConst(*this);
    }
public:
    // CONSTUCTORS
    BrokenMarkVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~BrokenMarkVisitor() {}
};

//######################################################################
// Broken state, as a visitor of each AstNode

class BrokenCheckVisitor : public AstNVisitor {
private:
    void checkWidthMin(AstNode* nodep) {
	if (nodep->width() != nodep->widthMin()
	    && v3Global.widthMinUsage()==VWidthMinUsage::MATCHES_WIDTH) {
	    nodep->v3fatalSrc("Width != WidthMin");
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	BrokenTable::setUnder(nodep,true);
	if (const char* whyp=nodep->broken()) {
	    nodep->v3fatalSrc("Broken link in node (or something without maybePointedTo): "<<whyp);
	}
	if (nodep->dtypep()) {
	    if (!nodep->dtypep()->brokeExists()) { nodep->v3fatalSrc("Broken link in node->dtypep() to "<<(void*)nodep->dtypep()); }
	    else if (!nodep->dtypep()->castNodeDType()) { nodep->v3fatalSrc("Non-dtype link in node->dtypep() to "<<(void*)nodep->dtypep()); }
	}
	if (v3Global.assertDTypesResolved()) {
	    if (nodep->hasDType()) {
		if (!nodep->dtypep()) nodep->v3fatalSrc("No dtype on node with hasDType(): "<<nodep->prettyTypeName());
	    } else {
		if (nodep->dtypep()) nodep->v3fatalSrc("DType on node without hasDType(): "<<nodep->prettyTypeName());
	    }
	    if (nodep->getChildDTypep()) nodep->v3fatalSrc("childDTypep() non-null on node after should have removed");
	    if (AstNodeDType* dnodep = nodep->castNodeDType()) checkWidthMin(dnodep);
	}
	checkWidthMin(nodep);
	nodep->iterateChildrenConst(*this);
	BrokenTable::setUnder(nodep,false);
    }
public:
    // CONSTUCTORS
    BrokenCheckVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~BrokenCheckVisitor() {}
};

//######################################################################
// Broken class functions

void V3Broken::brokenAll(AstNetlist* nodep) {
    //UINFO(9,__FUNCTION__<<": "<<endl);
    static bool inBroken = false;
    if (inBroken) {
	// A error called by broken can recurse back into broken; avoid this
	UINFO(1,"Broken called under broken, skipping recursion.\n");
    } else {
	inBroken = true;
	BrokenTable::prepForTree();
	BrokenMarkVisitor mvisitor (nodep);
	BrokenCheckVisitor cvisitor (nodep);
	BrokenTable::doneWithTree();
	inBroken = false;
    }
}

void V3Broken::addNewed(AstNode* nodep) {
    BrokenTable::addNewed(nodep);
}
void V3Broken::deleted(AstNode* nodep) {
    BrokenTable::deleted(nodep);
}
