// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode hash computation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Hasher.h"

#include <functional>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Visitor that computes node hashes

class HasherVisitor final : public VNVisitorConst {
    // NODE STATE
    //  AstNode::user4() -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    // VNUser4InUse     in V3Hasher.h

    // STATE
    V3Hash m_hash;  // Hash value accumulator
    const bool m_cacheInUser4;  // Use user4 to cache each V3Hash?

    // METHODS

    V3Hash hashNodeAndIterate(AstNode* nodep, bool hashDType, bool hashChildren,
                              std::function<void()>&& f) {
        // See comments in visit(AstCFunc) about this breaking recursion
        if (m_cacheInUser4 && nodep->user4()) {
            return V3Hash{nodep->user4()};
        } else {
            VL_RESTORER(m_hash);
            // Reset accumulator
            m_hash = V3Hash{nodep->type()};  // Node type
            f();  // Node specific hash
            if (hashDType && nodep != nodep->dtypep())
                iterateConstNull(nodep->dtypep());  // Node dtype
            if (hashChildren) iterateChildrenConst(nodep);  // Children
            if (m_cacheInUser4) nodep->user4(m_hash.value());
            return m_hash;
        }
    }

    // VISITORS

    constexpr static bool HASH_DTYPE = true;
    constexpr static bool HASH_CHILDREN = true;

    // Each visitor below contributes to the hash any node specific content
    // that is not dependent on either of the following, as these are
    // included by default by hashNode:
    // - Node type (as given by AstNode::type())
    // - Node dtype (unless !hashDType)
    // - child nodes (unless !hashChildren)
    //
    // The hash must be stable, which means in particular it cannot rely on
    // pointer values, or any other value that might differ between separate
    // invocations of Verilator over the same design.
    //
    // Note there is a circularity problem where some child nodes can back
    // to their ancestral nodes via member pointers, which can lead to an
    // infinite traversal. To break this, nodes that are subject to such
    // referencing and represent code which can reasonably be assumed not to
    // be equivalent to any other code, are hashed either by name (e.g.:
    // AstNodeModule), or by unique identifier (e.g.: AstNodeUOrStructDType).

    //------------------------------------------------------------
    // AstNode - Warns to help find missing cases

    void visit(AstNode* nodep) override {
#if VL_DEBUG
        UINFO(0, "%Warning: Hashing node as AstNode: " << nodep << endl);
#endif
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }

    //------------------------------------------------------------
    // AstNodeDType
    void visit(AstNodeArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {
            iterateConstNull(nodep->virtRefDTypep());
            m_hash += nodep->left();
            m_hash += nodep->right();
        });
    }
    void visit(AstNodeUOrStructDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, false, [this, nodep]() {  //
            m_hash += nodep->uniqueNum();
        });
    }
    void visit(AstParamTypeDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            m_hash += nodep->varType();
        });
    }
    void visit(AstMemberDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstDefImplicitDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->uniqueNum();
        });
    }
    void visit(AstAssocArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {
            iterateConstNull(nodep->virtRefDTypep());
            iterateConstNull(nodep->virtRefDType2p());
        });
    }
    void visit(AstDynArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->virtRefDTypep());
        });
    }
    void visit(AstUnsizedArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->virtRefDTypep());
        });
    }
    void visit(AstWildcardArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->virtRefDTypep());
        });
    }
    void visit(AstBasicDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->keyword();
            m_hash += nodep->numeric();
            m_hash += nodep->nrange().left();
            m_hash += nodep->nrange().right();
        });
    }
    void visit(AstCDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstConstDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->virtRefDTypep());
        });
    }
    void visit(AstClassRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->classp());
        });
    }
    void visit(AstIfaceRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->cellp());
        });
    }
    void visit(AstQueueDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->virtRefDTypep());
        });
    }
    void visit(AstRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->typedefp());
            iterateConstNull(nodep->refDTypep());
        });
    }
    void visit(AstStreamDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, []() {});
    }
    void visit(AstVoidDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, []() {});
    }
    void visit(AstEnumDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, false, [this, nodep]() {  //
            m_hash += nodep->uniqueNum();
        });
    }

    //------------------------------------------------------------
    // AstNodeExpr
    void visit(AstNodeExpr* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstConst* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->num().toHash();
        });
    }
    void visit(AstNullCheck* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstCCast* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->size();
        });
    }
    void visit(AstVarRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            if (nodep->varScopep()) {
                iterateConstNull(nodep->varScopep());
            } else {
                iterateConstNull(nodep->varp());
                m_hash += nodep->selfPointer().asString();
            }
        });
    }
    void visit(AstVarXRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            iterateConstNull(nodep->varp());
            m_hash += nodep->dotted();
        });
    }
    void visit(AstMemberSel* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstFScanF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->text();
        });
    }
    void visit(AstSScanF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->text();
        });
    }
    void visit(AstAddrOfCFunc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->funcp());
        });
    }

    //------------------------------------------------------------
    // AstNodeStmt
    void visit(AstNodeStmt* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, []() {});
    }
    void visit(AstNodeText* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->text();
        });
    }
    void visit(AstNodeCCall* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->funcp());
        });
    }
    void visit(AstNodeFTaskRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {
            iterateConstNull(nodep->taskp());
            iterateConstNull(nodep->classOrPackagep());
        });
    }
    void visit(AstCMethodHard* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstCAwait* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->sensesp());
        });
    }
    void visit(AstCLocalScope* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstCoverInc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->declp());
        });
    }
    void visit(AstDisplay* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->displayType();
        });
    }
    void visit(AstMonitorOff* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->off();
        });
    }
    void visit(AstJumpGo* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->labelp());
        });
    }
    void visit(AstTraceInc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->declp());
        });
    }
    void visit(AstNodeCoverOrAssert* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }

    //------------------------------------------------------------
    // AstNode direct descendants
    void visit(AstNodeRange* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstNodeModule* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, false, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstNodePreSel* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstClassExtends* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstSelLoopVars* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstDefParam* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstArg* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstParseRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->expect();
            m_hash += nodep->name();
        });
    }
    void visit(AstClassOrPackageRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->classOrPackageNodep());
        });
    }
    void visit(AstSenItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->edgeType();
        });
    }
    void visit(AstSenTree* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstSFormatF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->text();
        });
    }
    void visit(AstElabDisplay* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->displayType();
        });
    }
    void visit(AstInitItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstInitArray* nodep) override {
        if (const AstAssocArrayDType* const dtypep = VN_CAST(nodep->dtypep(), AssocArrayDType)) {
            if (nodep->defaultp()) {
                m_hash
                    += hashNodeAndIterate(nodep->defaultp(), HASH_DTYPE, HASH_CHILDREN, []() {});
            }
            const auto& mapr = nodep->map();
            for (const auto& itr : mapr) {  // mapr is sorted, so hash should get stable results
                m_hash += itr.first;
                m_hash += hashNodeAndIterate(itr.second, HASH_DTYPE, HASH_CHILDREN, []() {});
            }
        } else if (const AstUnpackArrayDType* const dtypep
                   = VN_CAST(nodep->dtypep(), UnpackArrayDType)) {
            // Hash unpacked array initializers by value, as the order of initializer nodes does
            // not matter, and we want semantically equivalent initializers to map to the same
            // hash.
            m_hash += hashNodeAndIterate(
                nodep, HASH_DTYPE, /* hashChildren: */ !dtypep, [this, nodep, dtypep]() {
                    if (dtypep) {
                        const uint32_t size = dtypep->elementsConst();
                        for (uint32_t n = 0; n < size; ++n) {  //
                            iterateConstNull(nodep->getIndexDefaultedValuep(n));
                        }
                    }
                });
        }
    }
    void visit(AstPragma* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->pragType();
        });
    }
    void visit(AstAttrOf* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->attrType();
        });
    }
    void visit(AstNodeFile* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstCFunc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            // We might be in a recursive function, if so on *second* call
            // here we need to break what would be an infinite loop.
            nodep->user4(V3Hash{1}.value());  // Set this "first" call
            // So that a second call will then exit hashNodeAndIterate
            // Having a constant in the hash just means the recursion will
            // end, it shouldn't change the CFunc having a unique hash itself.
            m_hash += nodep->isLoose();
        });
    }
    void visit(AstVar* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            m_hash += nodep->varType();
        });
    }
    void visit(AstScope* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, false, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->aboveScopep());
        });
    }
    void visit(AstVarScope* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            iterateConstNull(nodep->varp());
            iterateConstNull(nodep->scopep());
        });
    }
    void visit(AstEnumItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstTypedef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstTypedefFwd* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstActive* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            iterateConstNull(nodep->sensesp());
        });
    }
    void visit(AstCell* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->modp());
        });
    }
    void visit(AstCellInline* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->scopep());
        });
    }
    void visit(AstNodeFTask* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstModport* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstModportVarRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->varp());
        });
    }
    void visit(AstModportFTaskRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            iterateConstNull(nodep->ftaskp());
        });
    }
    void visit(AstMTaskBody* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstNodeProcedure* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, []() {});
    }
    void visit(AstNodeBlock* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {  //
            m_hash += nodep->name();
        });
    }
    void visit(AstPin* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [this, nodep]() {
            m_hash += nodep->name();
            m_hash += nodep->pinNum();
        });
    }

public:
    // CONSTRUCTORS
    explicit HasherVisitor(AstNode* nodep)
        : m_cacheInUser4{true} {
        iterateConst(nodep);
    }
    class Uncached {};
    HasherVisitor(const AstNode* nodep, Uncached)
        : m_cacheInUser4{false} {
        iterateConst(const_cast<AstNode*>(nodep));
    }
    V3Hash finalHash() const { return m_hash; }
    ~HasherVisitor() override = default;
};

//######################################################################
// V3Hasher methods

V3Hash V3Hasher::operator()(AstNode* nodep) const {
    if (!nodep->user4()) HasherVisitor{nodep};
    return V3Hash{nodep->user4()};
}

V3Hash V3Hasher::rehash(AstNode* nodep) const {
    nodep->user4(0);
    { HasherVisitor{nodep}; }
    return V3Hash{nodep->user4()};
}

V3Hash V3Hasher::uncachedHash(const AstNode* nodep) {
    const HasherVisitor visitor{nodep, HasherVisitor::Uncached{}};
    return visitor.finalHash();
}

//######################################################################
// This is used by the std::hash specialization for VNRef.
// Declared separately to avoid a circular header dependency.

size_t V3HasherUncachedHash(const AstNode& node) {
    return static_cast<size_t>(V3Hasher::uncachedHash(&node).value());
}
