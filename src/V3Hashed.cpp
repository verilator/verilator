// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Hashed common code into functions
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
// V3Hashed's Transformations:
//		
//	    Hash each node depth first
//		Hash includes varp name and operator type, and constants
//		Form lookup table based on hash of each statement  w/ nodep and next nodep
//		
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Hashed.h"
#include "V3Ast.h"

//######################################################################
// Hashed state, as a visitor of each AstNode

class HashedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNodeStmt::user4()	-> V3Hash.  Hash value of this node (hash of 0 is illegal)

    // STATE
    V3Hash		m_lowerHash;	// Hash of the statement we're building

    //int debug() { return 9; }

    // METHODS
    void hashNodeIterate(AstNode* nodep) {
	if (!nodep->user4()) {
	    if (nodep->backp()->castCFunc()
		&& !(nodep->castNodeStmt() || nodep->castCFunc())) {
		nodep->v3fatalSrc("Node "<<nodep->typeName()<<" in statement position but not marked stmt (node under function)");
	    }
	    V3Hash oldHash = m_lowerHash;
	    {
		m_lowerHash = nodep->sameHash();
		if (m_lowerHash.isIllegal()) {
		    nodep->v3fatalSrc("sameHash function undefined (returns 0) for node under CFunc.");
		}
		m_lowerHash = V3Hash(m_lowerHash, V3Hash(nodep->type()<<6 | nodep->width()));
		// Now update m_lowerHash for our children's (and next children) contributions
		nodep->iterateChildren(*this);
		// Store the hash value
		nodep->user4(m_lowerHash.fullValue());
		//UINFO(9, "    hashnode "<<m_lowerHash<<"  "<<nodep<<endl);
	    }
	    m_lowerHash = oldHash;
	}
	// Update what will become the above node's hash
	m_lowerHash += V3Hash(nodep->user4p());
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	hashNodeIterate(nodep);
    }

public:
    // CONSTUCTORS
    HashedVisitor(AstNode* nodep) {
	hashNodeIterate(nodep);
	//UINFO(9,"  stmthash "<<hex<<nodep->user4()<<"  "<<nodep<<endl);
    }
    virtual ~HashedVisitor() {}
};

//######################################################################
// Hashed class functions

V3Hashed::V3Hashed() {
    AstNode::user4ClearTree();	// userp() used on entire tree
}

void V3Hashed::hashAndInsert(AstNode* nodep) {
    UINFO(8,"   hashI "<<nodep<<endl);
    if (!nodep->user4p()) {
	HashedVisitor visitor (nodep);
    }
    m_hashMmap.insert(make_pair(V3Hash(nodep->user4p()), nodep));
}

bool V3Hashed::sameNodes(AstNode* node1p, AstNode* node2p) {
    if (!node1p->user4p()) node1p->v3fatalSrc("Called isIdentical on non-hashed nodes");
    if (!node2p->user4p()) node2p->v3fatalSrc("Called isIdentical on non-hashed nodes");
    return (node1p->user4p() == node2p->user4p()  // Same hash
	    && node1p->sameTree(node2p));
}

void V3Hashed::erase(iterator it) {
    AstNode* nodep = iteratorNodep(it);
    UINFO(8,"   erase "<<nodep<<endl);
    if (!nodep->user4p()) nodep->v3fatalSrc("Called removeNode on non-hashed node");
    m_hashMmap.erase(it);
    nodep->user4p(NULL);   // So we don't allow removeNode again
}

V3Hashed::iterator V3Hashed::findDuplicate(AstNode* nodep) {
    UINFO(8,"   findD "<<nodep<<endl);
    if (!nodep->user4p()) nodep->v3fatalSrc("Called findDuplicate on non-hashed node");
    pair <HashMmap::iterator,HashMmap::iterator> eqrange = mmap().equal_range(V3Hash(nodep->user4p()));
    for (HashMmap::iterator eqit = eqrange.first; eqit != eqrange.second; ++eqit) {
	AstNode* node2p = eqit->second;
	if (nodep != node2p && sameNodes(nodep, node2p)) {
	    return eqit;
	}
    }
    return end();
}
