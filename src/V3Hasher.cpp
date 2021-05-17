// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hashed common code into functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Hasher.h"

//######################################################################
// Visitor that computes node hashes

class HasherVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  AstNode::user4() -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    // AstUser4InUse     in V3Hasher.h

    // STATE
    V3Hash m_lowerHash;  // Hash of the statement we're building
    const bool m_cacheInUser4;  // Use user4 to cache each V3Hash?

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    //--------------------
    virtual void visit(AstVar*) override {}
    virtual void visit(AstTypedef*) override {}
    virtual void visit(AstParamTypeDType*) override {}

    virtual void visit(AstNode* nodep) override {
        V3Hash thisHash;
        if (!m_cacheInUser4 || !nodep->user4()) {
            VL_RESTORER(m_lowerHash);
            {
                m_lowerHash = nodep->sameHash();
                UASSERT_OBJ(!m_lowerHash.isIllegal(), nodep,
                            "sameHash function undefined (returns 0) for node under CFunc.");
                // For identical nodes, the type should be the same thus
                // dtypep should be the same too
                m_lowerHash = V3Hash(m_lowerHash,
                                     V3Hash(V3Hash(nodep->type() << 6), V3Hash(nodep->dtypep())));
                // Now update m_lowerHash for our children's (and next children) contributions
                iterateChildrenConst(nodep);
                // Store the hash value
                if (m_cacheInUser4) { nodep->user4(m_lowerHash.fullValue()); }
                thisHash = m_lowerHash;
            }
        }
        // Update what will become the above node's hash
        m_lowerHash += m_cacheInUser4 ? V3Hash(nodep->user4()) : thisHash;
    }

public:
    // CONSTRUCTORS
    explicit HasherVisitor(AstNode* nodep)
        : m_cacheInUser4{true} {
        iterate(nodep);
    }
    explicit HasherVisitor(const AstNode* nodep)
        : m_cacheInUser4{false} {
        iterate(const_cast<AstNode*>(nodep));
    }
    V3Hash finalHash() const { return m_lowerHash; }
    virtual ~HasherVisitor() override = default;
};

//######################################################################
// V3Hasher methods

V3Hash V3Hasher::operator()(AstNode* nodep) const {
    if (!nodep->user4()) { HasherVisitor visitor(nodep); }
    return V3Hash(nodep->user4());
}

V3Hash V3Hasher::uncachedHash(const AstNode* nodep) {
    HasherVisitor visitor(nodep);
    return visitor.finalHash();
}
