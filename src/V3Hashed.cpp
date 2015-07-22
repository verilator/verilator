// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hashed common code into functions
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
// V3Hashed's Transformations:
//
//	    Hash each node depth first
//		Hash includes varp name and operator type, and constants
//		Form lookup table based on hash of each statement  w/ nodep and next nodep
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <iomanip>
#include <map>
#include <memory>

#include "V3Global.h"
#include "V3Hashed.h"
#include "V3Ast.h"
#include "V3File.h"

//######################################################################
// Hashed state, as a visitor of each AstNode

class HashedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNodeStmt::user4()	-> V3Hash.  Hash value of this node (hash of 0 is illegal)
    //AstUser4InUse	in V3Hashed.h

    // STATE
    V3Hash		m_lowerHash;	// Hash of the statement we're building

    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // METHODS
    void nodeHashIterate(AstNode* nodep) {
	if (!nodep->user4()) {
	    if (nodep->backp()->castCFunc()
		&& !(nodep->castNodeStmt() || nodep->castCFunc())) {
		nodep->v3fatalSrc("Node "<<nodep->prettyTypeName()<<" in statement position but not marked stmt (node under function)");
	    }
	    V3Hash oldHash = m_lowerHash;
	    {
		m_lowerHash = nodep->sameHash();
		if (m_lowerHash.isIllegal()) {
		    nodep->v3fatalSrc("sameHash function undefined (returns 0) for node under CFunc.");
		}
		// For identical nodes, the type should be the same thus dtypep should be the same too
		m_lowerHash = V3Hash(m_lowerHash, V3Hash(nodep->type()<<6, V3Hash(nodep->dtypep())));
		// Now update m_lowerHash for our children's (and next children) contributions
		nodep->iterateChildren(*this);
		// Store the hash value
		nodep->user4(m_lowerHash.fullValue());
		//UINFO(9, "    hashnode "<<m_lowerHash<<"  "<<nodep<<endl);
	    }
	    m_lowerHash = oldHash;
	}
	// Update what will become the above node's hash
	m_lowerHash += V3Hashed::nodeHash(nodep);
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*, AstNUser*) {}
    virtual void visit(AstTypedef*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodeHashIterate(nodep);
    }

public:
    // CONSTUCTORS
    HashedVisitor(AstNode* nodep) {
	nodeHashIterate(nodep);
	//UINFO(9,"  stmthash "<<hex<<V3Hashed::nodeHash(nodep)<<"  "<<nodep<<endl);
    }
    virtual ~HashedVisitor() {}
};

//######################################################################
// Hashed class functions

V3Hashed::iterator V3Hashed::hashAndInsert(AstNode* nodep) {
    hash(nodep);
    return m_hashMmap.insert(make_pair(nodeHash(nodep), nodep));
}

void V3Hashed::hash(AstNode* nodep) {
    UINFO(8,"   hashI "<<nodep<<endl);
    if (!nodep->user4p()) {
	HashedVisitor visitor (nodep);
    }
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

void V3Hashed::dumpFilePrefixed(const string& nameComment, bool tree) {
    if (v3Global.opt.dumpTree()) {
	dumpFile(v3Global.debugFilename(nameComment)+".hash", tree);
    }
}

void V3Hashed::dumpFile(const string& filename, bool tree) {
    const auto_ptr<ofstream> logp (V3File::new_ofstream(filename));
    if (logp->fail()) v3fatalSrc("Can't write "<<filename);

    map<int,int> dist;

    V3Hash lasthash;
    int num_in_bucket = 0;
    for (HashMmap::iterator it=begin(); 1; ++it) {
	if (lasthash != it->first || it==end()) {
	    if (it!=end()) lasthash = it->first;
	    if (num_in_bucket) {
		if (dist.find(num_in_bucket)==dist.end()) {
		    dist.insert(make_pair(num_in_bucket,1));
		} else {
		    ++dist[num_in_bucket];
		}
	    }
	    num_in_bucket = 0;
	}
	if (it==end()) break;
	num_in_bucket++;
    }
    *logp <<"\n*** STATS:\n"<<endl;
    *logp<<"    #InBucket   Occurrences\n";
    for (map<int,int>::iterator it=dist.begin(); it!=dist.end(); ++it) {
	*logp<<"    "<<setw(9)<<it->first<<"  "<<setw(12)<<it->second<<endl;
    }

    *logp <<"\n*** Dump:\n"<<endl;
    for (HashMmap::iterator it=begin(); it!=end(); ++it) {
	if (lasthash != it->first) {
	    lasthash = it->first;
	    *logp <<"    "<<it->first<<endl;
	}
	*logp <<"\t"<<it->second<<endl;
	// Dumping the entire tree may make nearly N^2 sized dumps,
	// because the nodes under this one may also be in the hash table!
	if (tree) it->second->dumpTree(*logp,"\t\t");
    }
}

V3Hashed::iterator V3Hashed::findDuplicate(AstNode* nodep) {
    UINFO(8,"   findD "<<nodep<<endl);
    if (!nodep->user4p()) nodep->v3fatalSrc("Called findDuplicate on non-hashed node");
    pair <HashMmap::iterator,HashMmap::iterator> eqrange = mmap().equal_range(nodeHash(nodep));
    for (HashMmap::iterator eqit = eqrange.first; eqit != eqrange.second; ++eqit) {
	AstNode* node2p = eqit->second;
	if (nodep != node2p && sameNodes(nodep, node2p)) {
	    return eqit;
	}
    }
    return end();
}

V3Hashed::iterator V3Hashed::findDuplicate(AstNode* nodep, V3HashedUserCheck* checkp) {
    UINFO(8,"   findD "<<nodep<<endl);
    if (!nodep->user4p()) nodep->v3fatalSrc("Called findDuplicate on non-hashed node");
    pair <HashMmap::iterator,HashMmap::iterator> eqrange = mmap().equal_range(nodeHash(nodep));
    for (HashMmap::iterator eqit = eqrange.first; eqit != eqrange.second; ++eqit) {
	AstNode* node2p = eqit->second;
	if (nodep != node2p && checkp->check(nodep,node2p) && sameNodes(nodep, node2p)) {
	    return eqit;
	}
    }
    return end();
}

