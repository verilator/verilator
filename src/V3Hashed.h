// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2005-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3HASHED_H_
#define _V3HASHED_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3Ast.h"

#include <map>

//============================================================================

class VHashedBase {
public:
    // CONSTRUCTORS
    VHashedBase() {}
    ~VHashedBase() {}

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//============================================================================

struct V3HashedUserCheck {
    // Functor for V3Hashed::findDuplicate
    virtual bool check(AstNode*,AstNode*) =0;
    V3HashedUserCheck() {}
    virtual ~V3HashedUserCheck() {}
};

class V3Hashed : public VHashedBase {
    // NODE STATE
    //  AstNode::user4()	-> V3Hash.  Hash value of this node (hash of 0 is illegal)
    AstUser4InUse	m_inuser4;

    // TYPES
    typedef multimap<V3Hash,AstNode*> HashMmap;
public:
    typedef HashMmap::iterator iterator;
private:
    // MEMBERS
    HashMmap		m_hashMmap;	// hashvalue -> nodes with that hash

public:
    // CONSTRUCTORS
    V3Hashed() { clear(); }
    ~V3Hashed() {}

    // ACCESSORS
    HashMmap& mmap() { return m_hashMmap; }	// Return map for iteration
    iterator begin() { return m_hashMmap.begin(); }
    iterator end() { return m_hashMmap.end(); }

    // METHODS
    void clear() { m_hashMmap.clear(); AstNode::user4ClearTree(); }
    iterator hashAndInsert(AstNode* nodep);	// Hash the node, and insert into map. Return iterator to inserted
    void hash(AstNode* nodep);	// Only hash the node
    bool sameNodes(AstNode* node1p, AstNode* node2p);	// After hashing, and tell if identical
    void erase(iterator it);		// Remove node from structures
    iterator findDuplicate(AstNode* nodep);	// Return duplicate in hash, if any
    iterator findDuplicate(AstNode* nodep, V3HashedUserCheck* checkp);	// Extra user checks for sameness
    AstNode* iteratorNodep(iterator it) { return it->second; }
    void dumpFile(const string& filename, bool tree);
    void dumpFilePrefixed(const string& nameComment, bool tree=false);
    static V3Hash nodeHash(AstNode* nodep) { return V3Hash(nodep->user4p()); }
};

#endif // Guard
