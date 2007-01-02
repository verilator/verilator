// $Id$ //-*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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

    // TYPES
    typedef multimap<V3Hash,AstNode*> HashMmap;
public:
    typedef HashMmap::iterator iterator;
private:
    // MEMBERS
    HashMmap		m_hashMmap;	// hashvalue -> nodes with that hash
    int debug() { return 0; }
public:
    // CONSTRUCTORS
    V3Hashed();
    ~V3Hashed() {}
    // ACCESSORS
    HashMmap& mmap() { return m_hashMmap; }	// Return map for iteration
    HashMmap::iterator begin() { return m_hashMmap.begin(); }
    HashMmap::iterator end() { return m_hashMmap.end(); }
    // METHODS
    void clear() { m_hashMmap.clear(); }
    void hashAndInsert(AstNode* nodep);	// Hash the node, and insert into map
    bool sameNodes(AstNode* node1p, AstNode* node2p);	// After hashing, and tell if identical
    void erase(iterator it);		// Remove node from structures
    iterator findDuplicate(AstNode* nodep);	// Return duplicate in hash, if any
    AstNode* iteratorNodep(iterator it) { return it->second; }
};

#endif // Guard
