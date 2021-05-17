// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstNode hash computation
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

#include <functional>

//######################################################################
// Visitor that computes node hashes

class HasherVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  AstNode::user4() -> V3Hash.  Hash value of this node (hash of 0 is illegal)
    // AstUser4InUse     in V3Hasher.h

    // STATE
    V3Hash m_hash;  // Hash value accumulator
    const bool m_cacheInUser4;  // Use user4 to cache each V3Hash?

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    inline void walk(AstNode* nodep) {  //
        if (VL_LIKELY(nodep)) iterate(nodep);
    }

    V3Hash hashNode(AstNode* nodep, bool hashDType, bool hashChildren, std::function<void()>&& f) {
        if (m_cacheInUser4 && nodep->user4()) {
            return V3Hash(nodep->user4());
        } else {
            VL_RESTORER(m_hash);
            // Reset accumulator
            m_hash = V3Hash(nodep->type());  // Node type
            f();  // Node specific hash
            if (hashDType && nodep != nodep->dtypep()) walk(nodep->dtypep());  // Node dtype
            if (hashChildren) iterateChildrenConst(nodep);  // Children
            if (m_cacheInUser4) { nodep->user4(m_hash.value()); }
            return m_hash;
        }
    }

    // VISITORS

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

#define VISIT(kind, hashDType, hashChildren, body) \
    virtual void visit(kind* nodep) override { \
        const V3Hash hash = hashNode(nodep, hashDType, hashChildren, [=]() body); \
        m_hash += hash; \
    }

    //------------------------------------------------------------
    // AstNode - Warns to help find missing cases

    VISIT(AstNode, true, true, {  //
        UINFO(4, "WARNING! Hashing node as AstNode: " << nodep);
    })

    //------------------------------------------------------------
    // AstNodeDType
    VISIT(AstNodeArrayDType, false, true, {
        walk(nodep->virtRefDTypep());
        m_hash += nodep->left();
        m_hash += nodep->right();
    })
    VISIT(AstNodeUOrStructDType, false, false, {  //
        m_hash += nodep->uniqueNum();
    })
    VISIT(AstParamTypeDType, true, true, {
        m_hash += nodep->name();
        m_hash += nodep->varType();
    })
    VISIT(AstMemberDType, false, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstDefImplicitDType, true, true, {  //
        m_hash += nodep->uniqueNum();
    })
    VISIT(AstAssocArrayDType, false, true, {
        walk(nodep->virtRefDTypep());
        walk(nodep->virtRefDType2p());
    })
    VISIT(AstDynArrayDType, false, true, {  //
        walk(nodep->virtRefDTypep());
    })
    VISIT(AstUnsizedArrayDType, false, true, {  //
        walk(nodep->virtRefDTypep());
    })
    VISIT(AstBasicDType, false, true, {
        m_hash += nodep->keyword();
        m_hash += nodep->nrange().left();
        m_hash += nodep->nrange().right();
    })
    VISIT(AstConstDType, true, true, {  //
        walk(nodep->virtRefDTypep());
    })
    VISIT(AstClassRefDType, false, true, {  //
        walk(nodep->classp());
    })
    VISIT(AstIfaceRefDType, false, true, {  //
        walk(nodep->cellp());
    })
    VISIT(AstQueueDType, false, true, {  //
        walk(nodep->virtRefDTypep());
    })
    VISIT(AstRefDType, false, true, {
        m_hash += nodep->name();
        walk(nodep->typedefp());
        walk(nodep->refDTypep());
    })
    VISIT(AstVoidDType, false, true, {})
    VISIT(AstEnumDType, false, false, {  //
        m_hash += nodep->uniqueNum();
    })

    //------------------------------------------------------------
    // AstNodeMath
    VISIT(AstNodeMath, true, true, {})
    VISIT(AstConst, true, true, {  //
        m_hash += nodep->num().toHash();
    })
    VISIT(AstNullCheck, true, true, {})
    VISIT(AstCCast, true, true, {  //
        m_hash += nodep->size();
    })
    VISIT(AstVarRef, true, true, {
        if (nodep->varScopep()) {
            walk(nodep->varScopep());
        } else {
            walk(nodep->varp());
            m_hash += nodep->hiernameToProt();
        }
    })
    VISIT(AstVarXRef, true, true, {
        walk(nodep->varp());
        m_hash += nodep->dotted();
    })
    VISIT(AstMemberSel, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstFScanF, true, true, {  //
        m_hash += nodep->text();
    })
    VISIT(AstSScanF, true, true, {  //
        m_hash += nodep->text();
    })
    VISIT(AstTestPlusArgs, true, true, {  //
        m_hash += nodep->text();
    })

    //------------------------------------------------------------
    // AstNodeStmt
    VISIT(AstNodeStmt, false, true, {})
    VISIT(AstNodeText, false, true, {  //
        m_hash += nodep->text();
    })
    VISIT(AstNodeCCall, false, true, {  //
        walk(nodep->funcp());
    })
    VISIT(AstNodeFTaskRef, false, true, {  //
        walk(nodep->taskp());
        walk(nodep->classOrPackagep());
    })
    VISIT(AstCMethodHard, false, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstCoverInc, false, true, {  //
        walk(nodep->declp());
    })
    VISIT(AstDisplay, false, true, {  //
        m_hash += nodep->displayType();
    })
    VISIT(AstMonitorOff, false, true, {  //
        m_hash += nodep->off();
    })
    VISIT(AstJumpGo, false, true, {  //
        walk(nodep->labelp());
    })
    VISIT(AstTraceInc, false, true, {  //
        walk(nodep->declp());
    })
    VISIT(AstNodeCoverOrAssert, false, true, {  //
        m_hash += nodep->name();
    })

    //------------------------------------------------------------
    // AstNode direct descendents
    VISIT(AstNodeRange, true, true, {})
    VISIT(AstNodeModule, true, false, {  //
        m_hash += nodep->origName();
        m_hash += nodep->hierName();
    })
    VISIT(AstNodePreSel, true, true, {})
    VISIT(AstClassExtends, true, true, {})
    VISIT(AstSelLoopVars, true, true, {})
    VISIT(AstDefParam, true, true, {})
    VISIT(AstArg, true, true, {})
    VISIT(AstParseRef, true, true, {
        m_hash += nodep->expect();
        m_hash += nodep->name();
    })
    VISIT(AstClassOrPackageRef, true, true, {  //
        walk(nodep->classOrPackageNodep());
    })
    VISIT(AstSenItem, true, true, {  //
        m_hash += nodep->edgeType();
    })
    VISIT(AstSenTree, true, true, {})
    VISIT(AstSFormatF, true, true, {  //
        m_hash += nodep->text();
    })
    VISIT(AstElabDisplay, true, true, {  //
        m_hash += nodep->displayType();
    })
    VISIT(AstInitItem, true, true, {})
    VISIT(AstInitArray, true, true,
          {
              // Could hash nodep->map(), but is not very important right now
          })
    VISIT(AstPragma, true, true, {  //
        m_hash += nodep->pragType();
    })
    VISIT(AstAttrOf, true, true, {  //
        m_hash += nodep->attrType();
    })
    VISIT(AstNodeFile, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstCFunc, true, true, {/* Should we hash some bits here? */})
    VISIT(AstVar, true, true, {
        m_hash += nodep->name();
        m_hash += nodep->varType();
    })
    VISIT(AstScope, true, false, {
        m_hash += nodep->name();
        walk(nodep->aboveScopep());
    })
    VISIT(AstVarScope, true, true, {
        walk(nodep->varp());
        walk(nodep->scopep());
    })
    VISIT(AstEnumItem, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstTypedef, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstTypedefFwd, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstActive, true, true, {  //
        walk(nodep->sensesp());
    })
    VISIT(AstCell, true, true, {  //
        m_hash += nodep->name();
        walk(nodep->modp());
    })
    VISIT(AstCellInline, true, true, {  //
        m_hash += nodep->name();
        walk(nodep->scopep());
    })
    VISIT(AstNodeFTask, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstModport, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstModportVarRef, true, true, {  //
        m_hash += nodep->name();
        walk(nodep->varp());
    })
    VISIT(AstModportFTaskRef, true, true, {  //
        m_hash += nodep->name();
        walk(nodep->ftaskp());
    })
    VISIT(AstNodeProcedure, true, true, {})
    VISIT(AstNodeBlock, true, true, {  //
        m_hash += nodep->name();
    })
    VISIT(AstPin, true, true, {  //
        m_hash += nodep->name();
        m_hash += nodep->pinNum();
    })

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
    V3Hash finalHash() const { return m_hash; }
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
