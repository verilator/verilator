// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2012 by Wilson Snyder.  This program is free software; you can
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

class V3Hashed {
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
    V3Hashed();
    ~V3Hashed() {}
    // ACCESSORS
    HashMmap& mmap() { return m_hashMmap; }	// Return map for iteration
    HashMmap::iterator begin() { return m_hashMmap.begin(); }
    HashMmap::iterator end() { return m_hashMmap.end(); }

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
    void clear() { m_hashMmap.clear(); }
    void hashAndInsert(AstNode* nodep);	// Hash the node, and insert into map
    bool sameNodes(AstNode* node1p, AstNode* node2p);	// After hashing, and tell if identical
    void erase(iterator it);		// Remove node from structures
    iterator findDuplicate(AstNode* nodep);	// Return duplicate in hash, if any
    AstNode* iteratorNodep(iterator it) { return it->second; }
    void dumpFile(const string& filename, bool tree);
    void dumpFilePrefixed(const string& nameComment, bool tree=false);
};

#endif // Guard
