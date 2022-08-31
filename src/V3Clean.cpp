// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for clean nodes
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
// V3Clean's Transformations:
//
// Each module:
//      For each math operator, if it requires a clean operand,
//      and the operand is dirty, insert a CLEAN node.
//      Resize operands to C++ 32/64/wide types.
//      Copy all width() values to widthMin() so RANGE, etc can still see orig widths
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Clean.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>

//######################################################################
// Clean state, as a visitor of each AstNode

class CleanVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNode::user()         -> CleanState.  For this node, 0==UNKNOWN
    //  AstNode::user2()        -> bool.  True indicates widthMin has been propagated
    //  AstNodeDType::user3()   -> AstNodeDType*.  Alternative node with C size
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;

    // TYPES
    enum CleanState : uint8_t { CS_UNKNOWN, CS_CLEAN, CS_DIRTY };

    // STATE
    const AstNodeModule* m_modp = nullptr;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Width resetting
    int cppWidth(AstNode* nodep) {
        if (nodep->width() <= VL_IDATASIZE) {
            return VL_IDATASIZE;
        } else if (nodep->width() <= VL_QUADSIZE) {
            return VL_QUADSIZE;
        } else {
            return nodep->widthWords() * VL_EDATASIZE;
        }
    }
    void setCppWidth(AstNode* nodep) {
        nodep->user2(true);  // Don't resize it again
        AstNodeDType* const old_dtypep = nodep->dtypep();
        const int width = cppWidth(nodep);  // widthMin is unchanged
        if (old_dtypep->width() != width) {
            // Since any given dtype's cppWidth() is the same, we can just
            // remember one conversion for each, and reuse it
            if (AstNodeDType* const new_dtypep = VN_CAST(old_dtypep->user3p(), NodeDType)) {
                nodep->dtypep(new_dtypep);
            } else {
                nodep->dtypeChgWidth(width, nodep->widthMin());
                AstNodeDType* const new_dtypep2 = nodep->dtypep();
                UASSERT_OBJ(new_dtypep2 != old_dtypep, nodep,
                            "Dtype didn't change when width changed");
                old_dtypep->user3p(new_dtypep2);  // Remember for next time
            }
        }
    }
    void computeCppWidth(AstNode* nodep) {
        if (!nodep->user2() && nodep->hasDType()) {
            if (VN_IS(nodep, Var)
                || VN_IS(nodep, NodeDType)  // Don't want to change variable widths!
                || VN_IS(nodep->dtypep()->skipRefp(), AssocArrayDType)  // Or arrays
                || VN_IS(nodep->dtypep()->skipRefp(), WildcardArrayDType)
                || VN_IS(nodep->dtypep()->skipRefp(), DynArrayDType)
                || VN_IS(nodep->dtypep()->skipRefp(), ClassRefDType)
                || VN_IS(nodep->dtypep()->skipRefp(), QueueDType)
                || VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType)
                || VN_IS(nodep->dtypep()->skipRefp(), VoidDType)) {
            } else {
                setCppWidth(nodep);
            }
        }
    }

    // Store the clean state in the userp on each node
    void setCleanState(AstNode* nodep, CleanState clean) { nodep->user1(clean); }
    CleanState getCleanState(AstNode* nodep) { return static_cast<CleanState>(nodep->user1()); }
    bool isClean(AstNode* nodep) {
        const CleanState clstate = getCleanState(nodep);
        if (clstate == CS_CLEAN) return true;
        if (clstate == CS_DIRTY) return false;
        nodep->v3fatalSrc("Unknown clean state on node: " + nodep->prettyTypeName());
        return false;
    }
    void setClean(AstNode* nodep, bool isClean) {
        computeCppWidth(nodep);  // Just to be sure it's in widthMin
        const bool wholeUint
            = (nodep->widthMin() == VL_IDATASIZE || nodep->widthMin() == VL_QUADSIZE
               || (nodep->widthMin() % VL_EDATASIZE) == 0);
        setCleanState(nodep, ((isClean || wholeUint) ? CS_CLEAN : CS_DIRTY));
    }

    // Operate on nodes
    void insertClean(AstNode* nodep) {  // We'll insert ABOVE passed node
        UINFO(4, "  NeedClean " << nodep << endl);
        VNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        //
        computeCppWidth(nodep);
        V3Number mask(nodep, cppWidth(nodep));
        mask.setMask(nodep->widthMin());
        AstNode* const cleanp
            = new AstAnd(nodep->fileline(), new AstConst(nodep->fileline(), mask), nodep);
        cleanp->dtypeFrom(nodep);  // Otherwise the AND normally picks LHS
        relinkHandle.relink(cleanp);
    }
    void ensureClean(AstNode* nodep) {
        computeCppWidth(nodep);
        if (!isClean(nodep)) insertClean(nodep);
    }
    void ensureCleanAndNext(AstNode* nodep) {
        // Editing list, careful looping!
        for (AstNode* exprp = nodep; exprp;) {
            AstNode* const nextp = exprp->nextp();
            ensureClean(exprp);
            exprp = nextp;
        }
    }

    // Base type handling methods
    void operandBiop(AstNodeBiop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        // no setClean.. must do it in each user routine.
    }
    void operandTriop(AstNodeTriop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        if (nodep->cleanThs()) ensureClean(nodep->thsp());
        // no setClean.. must do it in each user routine.
    }
    void operandQuadop(AstNodeQuadop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        if (nodep->cleanThs()) ensureClean(nodep->thsp());
        if (nodep->cleanFhs()) ensureClean(nodep->fhsp());
        // no setClean.. must do it in each user routine.
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeBiop* nodep) override {
        operandBiop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstAnd* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) || isClean(nodep->rhsp()));
    }
    virtual void visit(AstXor* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstOr* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstNodeQuadop* nodep) override {
        operandQuadop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeMath* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeAssign* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
    }
    virtual void visit(AstText* nodep) override {  //
        setClean(nodep, true);
    }
    virtual void visit(AstScopeName* nodep) override {  //
        setClean(nodep, true);
    }
    virtual void visit(AstCNew* nodep) override {
        iterateChildren(nodep);
        setClean(nodep, true);
    }
    virtual void visit(AstSel* nodep) override {
        operandTriop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstUCFunc* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        setClean(nodep, false);
        // We always clean, as we don't trust those pesky users.
        if (!VN_IS(nodep->backp(), And)) insertClean(nodep);
        ensureCleanAndNext(nodep->bodysp());
    }
    virtual void visit(AstTraceDecl* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }
    virtual void visit(AstTraceInc* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->valuep());
    }
    virtual void visit(AstTypedef* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }
    virtual void visit(AstParamTypeDType* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }

    // Control flow operators
    virtual void visit(AstNodeCond* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
        setClean(nodep, isClean(nodep->expr1p()) && isClean(nodep->expr2p()));
    }
    virtual void visit(AstWhile* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
    }
    virtual void visit(AstNodeIf* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
    }
    virtual void visit(AstSFormatF* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->exprsp());
        setClean(nodep, true);  // generates a string, so not relevant
    }
    virtual void visit(AstUCStmt* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->bodysp());
    }
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->argsp());
        setClean(nodep, true);
    }
    virtual void visit(AstCMethodHard* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->pinsp());
        setClean(nodep, true);
    }
    virtual void visit(AstWith* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->exprp());
        setClean(nodep, true);
    }
    virtual void visit(AstIntfRef* nodep) override {
        iterateChildren(nodep);
        setClean(nodep, true);  // generates a string, so not relevant
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CleanVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~CleanVisitor() override = default;
};

//######################################################################
// Clean class functions

void V3Clean::cleanAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CleanVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("clean", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
