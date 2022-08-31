// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hash AST trees to find duplicates
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//  V3Hasher handles computation of AstNode hashes
//
//*************************************************************************

#ifndef VERILATOR_V3HASHER_H_
#define VERILATOR_V3HASHER_H_
#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3Hash.h"

//============================================================================

class V3Hasher final {
    // NODE STATE
    //  AstNode::user4()    -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    const VNUser4InUse m_inuser4;

public:
    // CONSTRUCTORS
    V3Hasher() = default;
    ~V3Hasher() = default;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Compute hash of node. This method caches the hash in the node's user4().
    V3Hash operator()(AstNode* nodep) const;

    // Re-compute hash of this node, discarding cached value, but used cached hash of children.
    V3Hash rehash(AstNode* nodep) const;

    // Compute hash of node, without caching in user4.
    static V3Hash uncachedHash(const AstNode* nodep);
};

#endif  // Guard
