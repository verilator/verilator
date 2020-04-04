// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3HASHED_H_
#define _V3HASHED_H_ 1
#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class VHashedBase {
public:
    // CONSTRUCTORS
    VHashedBase() {}
    ~VHashedBase() {}

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
};

//============================================================================

struct V3HashedUserSame {
    // Functor for V3Hashed::findDuplicate
    virtual bool isSame(AstNode*, AstNode*) = 0;
    V3HashedUserSame() {}
    virtual ~V3HashedUserSame() {}
};

class V3Hashed : public VHashedBase {
    // NODE STATE
    //  AstNode::user4()        -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    AstUser4InUse m_inuser4;

    // TYPES
public:
    typedef std::multimap<V3Hash,AstNode*> HashMmap;
    typedef HashMmap::iterator iterator;
private:
    // MEMBERS
    HashMmap m_hashMmap;  // hashvalue -> nodes with that hash

public:
    // CONSTRUCTORS
    V3Hashed() { clear(); }
    ~V3Hashed() {}

    // ACCESSORS
    HashMmap& mmap() { return m_hashMmap; }  // Return map for iteration
    iterator begin() { return m_hashMmap.begin(); }
    iterator end() { return m_hashMmap.end(); }

    // METHODS
    void clear() { m_hashMmap.clear(); AstNode::user4ClearTree(); }
    void check();  // Check assertions on structure
    iterator hashAndInsert(AstNode* nodep);  // Hash the node, and insert into map. Return iterator to inserted
    void hash(AstNode* nodep);  // Only hash the node
    bool sameNodes(AstNode* node1p, AstNode* node2p);  // After hashing, and tell if identical
    void erase(iterator it);  // Remove node from structures
    // Return duplicate in hash, if any, with optional user check for sameness
    iterator findDuplicate(AstNode* nodep, V3HashedUserSame* checkp=NULL);
    AstNode* iteratorNodep(iterator it) { return it->second; }
    void dumpFile(const string& filename, bool tree);
    void dumpFilePrefixed(const string& nameComment, bool tree=false);
    static V3Hash nodeHash(AstNode* nodep) { return V3Hash(nodep->user4p()); }
    // Hash of the nodep tree, without caching in user4.
    static V3Hash uncachedHash(const AstNode* nodep);
};

#endif  // Guard
