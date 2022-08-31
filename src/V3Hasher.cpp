// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode hash computation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Hasher.h"

#include <functional>

//######################################################################
// Visitor that computes node hashes

class HasherVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstNode::user4() -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    // VNUser4InUse     in V3Hasher.h

    // STATE
    V3Hash m_hash;  // Hash value accumulator
    const bool m_cacheInUser4;  // Use user4 to cache each V3Hash?

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    V3Hash hashNodeAndIterate(AstNode* nodep, bool hashDType, bool hashChildren,
                              std::function<void()>&& f) {
        // See comments in visit(AstCFunc) about this breaking recursion
        if (m_cacheInUser4 && nodep->user4()) {
            return V3Hash(nodep->user4());
        } else {
            VL_RESTORER(m_hash);
            // Reset accumulator
            m_hash = V3Hash(nodep->type());  // Node type
            f();  // Node specific hash
            if (hashDType && nodep != nodep->dtypep()) iterateNull(nodep->dtypep());  // Node dtype
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

    virtual void visit(AstNode* nodep) override {
#if VL_DEBUG
        UINFO(0, "%Warning: Hashing node as AstNode: " << nodep << endl);
#endif
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }

    //------------------------------------------------------------
    // AstNodeDType
    virtual void visit(AstNodeArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {
            iterateNull(nodep->virtRefDTypep());
            m_hash += nodep->left();
            m_hash += nodep->right();
        });
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, false, [=]() {  //
            m_hash += nodep->uniqueNum();
        });
    }
    virtual void visit(AstParamTypeDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            m_hash += nodep->varType();
        });
    }
    virtual void visit(AstMemberDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstDefImplicitDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->uniqueNum();
        });
    }
    virtual void visit(AstAssocArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {
            iterateNull(nodep->virtRefDTypep());
            iterateNull(nodep->virtRefDType2p());
        });
    }
    virtual void visit(AstDynArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->virtRefDTypep());
        });
    }
    virtual void visit(AstUnsizedArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->virtRefDTypep());
        });
    }
    virtual void visit(AstWildcardArrayDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->virtRefDTypep());
        });
    }
    virtual void visit(AstBasicDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {
            m_hash += nodep->keyword();
            m_hash += nodep->nrange().left();
            m_hash += nodep->nrange().right();
        });
    }
    virtual void visit(AstConstDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->virtRefDTypep());
        });
    }
    virtual void visit(AstClassRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->classp());
        });
    }
    virtual void visit(AstIfaceRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->cellp());
        });
    }
    virtual void visit(AstQueueDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->virtRefDTypep());
        });
    }
    virtual void visit(AstRefDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->typedefp());
            iterateNull(nodep->refDTypep());
        });
    }
    virtual void visit(AstVoidDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstEnumDType* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, false, [=]() {  //
            m_hash += nodep->uniqueNum();
        });
    }

    //------------------------------------------------------------
    // AstNodeMath
    virtual void visit(AstNodeMath* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstConst* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->num().toHash();
        });
    }
    virtual void visit(AstNullCheck* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstCCast* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->size();
        });
    }
    virtual void visit(AstVarRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            if (nodep->varScopep()) {
                iterateNull(nodep->varScopep());
            } else {
                iterateNull(nodep->varp());
                m_hash += nodep->selfPointer();
            }
        });
    }
    virtual void visit(AstVarXRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            iterateNull(nodep->varp());
            m_hash += nodep->dotted();
        });
    }
    virtual void visit(AstMemberSel* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstFScanF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->text();
        });
    }
    virtual void visit(AstSScanF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->text();
        });
    }
    virtual void visit(AstAddrOfCFunc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->funcp());
        });
    }

    //------------------------------------------------------------
    // AstNodeStmt
    virtual void visit(AstNodeStmt* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstNodeText* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->text();
        });
    }
    virtual void visit(AstNodeCCall* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->funcp());
        });
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {
            iterateNull(nodep->taskp());
            iterateNull(nodep->classOrPackagep());
        });
    }
    virtual void visit(AstCMethodHard* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstCoverInc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->declp());
        });
    }
    virtual void visit(AstDisplay* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->displayType();
        });
    }
    virtual void visit(AstMonitorOff* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->off();
        });
    }
    virtual void visit(AstJumpGo* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->labelp());
        });
    }
    virtual void visit(AstTraceInc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->declp());
        });
    }
    virtual void visit(AstNodeCoverOrAssert* nodep) override {
        m_hash += hashNodeAndIterate(nodep, false, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }

    //------------------------------------------------------------
    // AstNode direct descendents
    virtual void visit(AstNodeRange* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstNodeModule* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, false, [=]() {  //
            m_hash += nodep->origName();
        });
    }
    virtual void visit(AstNodePreSel* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstClassExtends* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstSelLoopVars* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstDefParam* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstArg* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstParseRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->expect();
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstClassOrPackageRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->classOrPackageNodep());
        });
    }
    virtual void visit(AstSenItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->edgeType();
        });
    }
    virtual void visit(AstSenTree* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstSFormatF* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->text();
        });
    }
    virtual void visit(AstElabDisplay* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->displayType();
        });
    }
    virtual void visit(AstInitItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstInitArray* nodep) override {
        if (const AstAssocArrayDType* const dtypep = VN_CAST(nodep->dtypep(), AssocArrayDType)) {
            if (nodep->defaultp()) {
                m_hash
                    += hashNodeAndIterate(nodep->defaultp(), HASH_DTYPE, HASH_CHILDREN, [=]() {});
            }
            const auto& mapr = nodep->map();
            for (const auto& itr : mapr) {  // mapr is sorted, so hash should get stable results
                m_hash += itr.first;
                m_hash += hashNodeAndIterate(itr.second, HASH_DTYPE, HASH_CHILDREN, [=]() {});
            }
        } else if (const AstUnpackArrayDType* const dtypep
                   = VN_CAST(nodep->dtypep(), UnpackArrayDType)) {
            // Hash unpacked array initializers by value, as the order of initializer nodes does
            // not matter, and we want semantically equivalent initializers to map to the same
            // hash.
            m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, /* hashChildren: */ !dtypep, [=]() {
                if (dtypep) {
                    const uint32_t size = dtypep->elementsConst();
                    for (uint32_t n = 0; n < size; ++n) {  //
                        iterateNull(nodep->getIndexDefaultedValuep(n));
                    }
                }
            });
        }
    }
    virtual void visit(AstPragma* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->pragType();
        });
    }
    virtual void visit(AstAttrOf* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->attrType();
        });
    }
    virtual void visit(AstNodeFile* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstCFunc* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            // We might be in a recursive function, if so on *second* call
            // here we need to break what would be an infinite loop.
            nodep->user4(V3Hash(1).value());  // Set this "first" call
            // So that a second call will then exit hashNodeAndIterate
            // Having a constant in the hash just means the recursion will
            // end, it shouldn't change the CFunc having a unique hash itself.
            m_hash += nodep->isLoose();
        });
    }
    virtual void visit(AstVar* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            m_hash += nodep->varType();
        });
    }
    virtual void visit(AstScope* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, false, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->aboveScopep());
        });
    }
    virtual void visit(AstVarScope* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            iterateNull(nodep->varp());
            iterateNull(nodep->scopep());
        });
    }
    virtual void visit(AstEnumItem* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstTypedef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstTypedefFwd* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstActive* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            iterateNull(nodep->sensesp());
        });
    }
    virtual void visit(AstCell* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->modp());
        });
    }
    virtual void visit(AstCellInline* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->scopep());
        });
    }
    virtual void visit(AstNodeFTask* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstModport* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstModportVarRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->varp());
        });
    }
    virtual void visit(AstModportFTaskRef* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            iterateNull(nodep->ftaskp());
        });
    }
    virtual void visit(AstMTaskBody* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstNodeProcedure* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {});
    }
    virtual void visit(AstNodeBlock* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {  //
            m_hash += nodep->name();
        });
    }
    virtual void visit(AstPin* nodep) override {
        m_hash += hashNodeAndIterate(nodep, HASH_DTYPE, HASH_CHILDREN, [=]() {
            m_hash += nodep->name();
            m_hash += nodep->pinNum();
        });
    }

public:
    // CONSTRUCTORS
    explicit HasherVisitor(AstNode* nodep)
        : m_cacheInUser4{true} {
        iterate(nodep);
    }
    class Uncached {};
    HasherVisitor(const AstNode* nodep, Uncached)
        : m_cacheInUser4{false} {
        iterate(const_cast<AstNode*>(nodep));
    }
    V3Hash finalHash() const { return m_hash; }
    virtual ~HasherVisitor() override = default;
};

//######################################################################
// V3Hasher methods

V3Hash V3Hasher::operator()(AstNode* nodep) const {
    if (!nodep->user4()) HasherVisitor{nodep};
    return V3Hash(nodep->user4());
}

V3Hash V3Hasher::rehash(AstNode* nodep) const {
    nodep->user4(0);
    { HasherVisitor{nodep}; }
    return V3Hash(nodep->user4());
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
