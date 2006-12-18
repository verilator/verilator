// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Find broken links in tree
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
// V3Broken's Transformations:
//		
// Entire netlist
//	Mark all nodes
//	Check all links point to marked nodes
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>
#include <set>

#include "V3Global.h"
#include "V3Broken.h"
#include "V3Ast.h"

//######################################################################

class BrokenTable : public AstNVisitor {
    // Table of brokenExists node pointers
private:
    // MEMBERS
    //   For each node, we keep if it exists or not.
    typedef set<const AstNode*> NodeSet;
    static NodeSet s_nodes;	// Set of all nodes that exist
public:
    // METHODS
    static void add(const AstNode* nodep) {
	s_nodes.insert(nodep);
    }
    static bool exists(const AstNode* nodep) {
	NodeSet::iterator iter = s_nodes.find(nodep);
	return (iter != s_nodes.end());
    }
    static void clear() {
	s_nodes.clear();
    }
public:
    // CONSTUCTORS
    BrokenTable() {}
    virtual ~BrokenTable() {}
};

BrokenTable::NodeSet BrokenTable::s_nodes;

bool AstNode::brokeExists() const {
    // Called by node->broken() routines to do table lookup
    return BrokenTable::exists(this);
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
	if (nodep->maybePointedTo()) {
	    BrokenTable::add(nodep);
	}
	nodep->iterateChildren(*this);
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
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (nodep->broken()) {
	    nodep->v3fatalSrc("Broken link in node (or something without maybePointedTo)\n");
	}
	if (v3Global.assertWidthsSame()) {
	    if (nodep->width() != nodep->widthMin()) {
		nodep->v3fatalSrc("Width != WidthMin\n");
	    }
	    if (!nodep->width() && nodep->castNodeMath()) {
		nodep->v3fatalSrc("Math node has no assigned width\n");
	    }
	}
	nodep->iterateChildren(*this);
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
    BrokenTable::clear();
    BrokenMarkVisitor mvisitor (nodep);
    BrokenCheckVisitor cvisitor (nodep);
    BrokenTable::clear();
}
