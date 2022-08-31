// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for premit nodes
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
// V3Premit's Transformations:
//
// Each module:
//      For each wide OP, make a a temporary variable with the wide value
//      For each deep expression, assign expression to temporary.
//
// Each display (independent transformation; here as Premit is a good point)
//      If autoflush, insert a flush
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Premit.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <algorithm>

constexpr int STATIC_CONST_MIN_WIDTH = 256;  // Minimum size to extract to static constant

//######################################################################
// Premit state, as a visitor of each AstNode

class PremitVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstNodeMath::user()     -> bool.  True if iterated already
    //  AstShiftL::user2()      -> bool.  True if converted to conditional
    //  AstShiftR::user2()      -> bool.  True if converted to conditional
    //  *::user3()              -> Used when visiting AstNodeAssign
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // Current block
    AstNode* m_stmtp = nullptr;  // Current statement
    AstWhile* m_inWhilep = nullptr;  // Inside while loop, special statement additions
    AstTraceInc* m_inTracep = nullptr;  // Inside while loop, special statement additions
    bool m_assignLhs = false;  // Inside assignment lhs, don't breakup extracts
    V3UniqueNames m_tempNames;  // For generating unique temporary variable names

    VDouble0 m_extractedToConstPool;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool assignNoTemp(AstNodeAssign* nodep) {
        return (VN_IS(nodep->lhsp(), VarRef) && !AstVar::scVarRecurse(nodep->lhsp())
                && VN_IS(nodep->rhsp(), Const));
    }
    void checkNode(AstNode* nodep) {
        // Consider adding a temp for this expression.
        // We need to avoid adding temps to the following:
        //   ASSIGN(x, *here*)
        //   ASSIGN(CONST*here*, VARREF(!sc))
        //   ARRAYSEL(*here*, ...)   (No wides can be in any argument but first,
        //                            so we don't check which arg is wide)
        //   ASSIGN(x, SEL*HERE*(ARRAYSEL()...)   (m_assignLhs==true handles this.)
        // UINFO(9, "   Check: " << nodep << endl);
        // UINFO(9, "     Detail stmtp=" << (m_stmtp?"Y":"N") << " U=" << (nodep->user1()?"Y":"N")
        // << " IW=" << (nodep->isWide()?"Y":"N") << endl);
        if (m_stmtp && !nodep->user1()) {  // Not already done
            if (nodep->isWide()) {
                if (m_assignLhs) {
                } else if (nodep->firstAbovep() && VN_IS(nodep->firstAbovep(), NodeAssign)
                           && assignNoTemp(VN_AS(nodep->firstAbovep(), NodeAssign))) {
                    // Not much point if it's just a direct assignment to a constant
                } else if (VN_IS(nodep->backp(), Sel)
                           && VN_AS(nodep->backp(), Sel)->widthp() == nodep) {
                    // AstSel::width must remain a constant
                } else if ((nodep->firstAbovep() && VN_IS(nodep->firstAbovep(), ArraySel))
                           || ((VN_IS(m_stmtp, CCall) || VN_IS(m_stmtp, CStmt))
                               && VN_IS(nodep, ArraySel))) {
                    // ArraySel's are pointer refs, ignore
                } else {
                    UINFO(4, "Cre Temp: " << nodep << endl);
                    createDeepTemp(nodep, false);
                }
            }
        }
    }

    void insertBeforeStmt(AstNode* newp) {
        // Insert newp before m_stmtp
        if (m_inWhilep) {
            // Statements that are needed for the 'condition' in a while
            // actually have to be put before & after the loop, since we
            // can't do any statements in a while's (cond).
            m_inWhilep->addPrecondsp(newp);
        } else if (m_inTracep) {
            m_inTracep->addPrecondsp(newp);
        } else if (m_stmtp) {
            m_stmtp->addHereThisAsNext(newp);
        } else {
            newp->v3fatalSrc("No statement insertion point.");
        }
    }

    void createDeepTemp(AstNode* nodep, bool noSubst) {
        if (nodep->user1SetOnce()) return;  // Only add another assignment for this node

        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);

        FileLine* const fl = nodep->fileline();
        AstVar* varp = nullptr;
        AstConst* const constp = VN_CAST(nodep, Const);
        const bool useConstPool = constp  // Is a constant
                                  && (constp->width() >= STATIC_CONST_MIN_WIDTH)  // Large enough
                                  && !constp->num().isFourState()  // Not four state
                                  && !constp->num().isString();  // Not a string
        if (useConstPool) {
            // Extract into constant pool.
            const bool merge = v3Global.opt.fMergeConstPool();
            varp = v3Global.rootp()->constPoolp()->findConst(constp, merge)->varp();
            nodep->deleteTree();
            ++m_extractedToConstPool;
        } else {
            // Keep as local temporary. Name based on hash of node for output stability.
            varp = new AstVar(fl, VVarType::STMTTEMP, m_tempNames.get(nodep), nodep->dtypep());
            m_cfuncp->addInitsp(varp);
            // Put assignment before the referencing statement
            insertBeforeStmt(new AstAssign(fl, new AstVarRef(fl, varp, VAccess::WRITE), nodep));
        }

        // Do not remove VarRefs to this in V3Const
        if (noSubst) varp->noSubst(true);

        // Replace node with VarRef to new Var
        relinker.relink(new AstVarRef(fl, varp, VAccess::READ));
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        UINFO(4, " MOD   " << nodep << endl);
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            m_tempNames.reset();
            iterateChildren(nodep);
        }
    }
    void startStatement(AstNode* nodep) {
        m_assignLhs = false;
        if (m_cfuncp) m_stmtp = nodep;
    }
    virtual void visit(AstWhile* nodep) override {
        UINFO(4, "  WHILE  " << nodep << endl);
        startStatement(nodep);
        iterateAndNextNull(nodep->precondsp());
        startStatement(nodep);
        m_inWhilep = nodep;
        iterateAndNextNull(nodep->condp());
        m_inWhilep = nullptr;
        startStatement(nodep);
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        m_stmtp = nullptr;
    }
    virtual void visit(AstNodeAssign* nodep) override {
        startStatement(nodep);
        {
            bool noopt = false;
            {
                const VNUser3InUse user3InUse;
                nodep->lhsp()->foreach<AstVarRef>([](const AstVarRef* refp) {
                    if (refp->access().isWriteOrRW()) refp->varp()->user3(true);
                });
                nodep->rhsp()->foreach<AstVarRef>([&noopt](const AstVarRef* refp) {
                    if (refp->access().isReadOnly() && refp->varp()->user3()) noopt = true;
                });
            }

            if (noopt && !nodep->user1()) {
                nodep->user1(true);
                // Need to do this even if not wide, as e.g. a select may be on a wide operator
                UINFO(4, "Deep temp for LHS/RHS\n");
                createDeepTemp(nodep->rhsp(), false);
            }
        }
        iterateAndNextNull(nodep->rhsp());
        m_assignLhs = true;
        iterateAndNextNull(nodep->lhsp());
        m_assignLhs = false;
        m_stmtp = nullptr;
    }
    virtual void visit(AstNodeStmt* nodep) override {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        UINFO(4, "  STMT  " << nodep << endl);
        startStatement(nodep);
        iterateChildren(nodep);
        m_stmtp = nullptr;
    }
    virtual void visit(AstTraceInc* nodep) override {
        startStatement(nodep);
        m_inTracep = nodep;
        iterateChildren(nodep);
        m_inTracep = nullptr;
        m_stmtp = nullptr;
    }
    void visitShift(AstNodeBiop* nodep) {
        // Shifts of > 32/64 bits in C++ will wrap-around and generate non-0s
        if (!nodep->user2SetOnce()) {
            UINFO(4, "  ShiftFix  " << nodep << endl);
            const AstConst* const shiftp = VN_CAST(nodep->rhsp(), Const);
            if (shiftp && shiftp->num().mostSetBitP1() > 32) {
                shiftp->v3error(
                    "Unsupported: Shifting of by over 32-bit number isn't supported."
                    << " (This isn't a shift of 32 bits, but a shift of 2^32, or 4 billion!)\n");
            }
            if (nodep->widthMin() <= 64  // Else we'll use large operators which work right
                                         // C operator's width must be < maximum shift which is
                                         // based on Verilog width
                && nodep->width() < (1LL << nodep->rhsp()->widthMin())) {
                VNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                AstNode* constzerop;
                const int m1value
                    = nodep->widthMin() - 1;  // Constant of width-1; not changing dtype width
                if (nodep->signedFlavor()) {
                    // Then over shifting gives the sign bit, not all zeros
                    // Note *NOT* clean output -- just like normal shift!
                    // Create equivalent of VL_SIGNONES_(node_width)
                    constzerop = new AstNegate(
                        nodep->fileline(),
                        new AstShiftR(nodep->fileline(), nodep->lhsp()->cloneTree(false),
                                      new AstConst(nodep->fileline(), m1value), nodep->width()));
                } else {
                    constzerop = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                              nodep->width(), 0);
                }
                constzerop->dtypeFrom(nodep);  // unsigned

                AstNode* const constwidthp
                    = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                   nodep->rhsp()->widthMin(), m1value);
                constwidthp->dtypeFrom(nodep->rhsp());  // unsigned
                AstCond* const newp = new AstCond(
                    nodep->fileline(),
                    new AstGte(nodep->fileline(), constwidthp, nodep->rhsp()->cloneTree(false)),
                    nodep, constzerop);
                replaceHandle.relink(newp);
            }
        }
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstShiftL* nodep) override { visitShift(nodep); }
    virtual void visit(AstShiftR* nodep) override { visitShift(nodep); }
    virtual void visit(AstShiftRS* nodep) override { visitShift(nodep); }
    // Operators
    virtual void visit(AstNodeTermop* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstNodeBiop* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstRand* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstUCFunc* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            iterateAndNextNull(nodep->lsbp());
            iterateAndNextNull(nodep->widthp());
        }
        checkNode(nodep);
    }
    virtual void visit(AstArraySel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            iterateAndNextNull(nodep->bitp());
        }
        checkNode(nodep);
    }
    virtual void visit(AstAssocSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            iterateAndNextNull(nodep->bitp());
        }
        checkNode(nodep);
    }
    virtual void visit(AstConst* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    virtual void visit(AstNodeCond* nodep) override {
        iterateChildren(nodep);
        if (nodep->expr1p()->isWide() && !VN_IS(nodep->condp(), Const)
            && !VN_IS(nodep->condp(), VarRef)) {
            // We're going to need the expression several times in the expanded code,
            // so might as well make it a common expression
            createDeepTemp(nodep->condp(), false);
        }
        checkNode(nodep);
    }

    // Autoflush
    virtual void visit(AstDisplay* nodep) override {
        startStatement(nodep);
        iterateChildren(nodep);
        m_stmtp = nullptr;
        if (v3Global.opt.autoflush()) {
            const AstNode* searchp = nodep->nextp();
            while (searchp && VN_IS(searchp, Comment)) searchp = searchp->nextp();
            if (searchp && VN_IS(searchp, Display)
                && nodep->filep()->sameGateTree(VN_AS(searchp, Display)->filep())) {
                // There's another display next; we can just wait to flush
            } else {
                UINFO(4, "Autoflush " << nodep << endl);
                nodep->addNextHere(new AstFFlush(nodep->fileline(),
                                                 AstNode::cloneTreeNull(nodep->filep(), true)));
            }
        }
    }
    virtual void visit(AstSFormatF* nodep) override {
        iterateChildren(nodep);
        // Any strings sent to a display must be var of string data type,
        // to avoid passing a pointer to a temporary.
        for (AstNode* expp = nodep->exprsp(); expp; expp = expp->nextp()) {
            if (expp->dtypep()->basicp() && expp->dtypep()->basicp()->isString()
                && !VN_IS(expp, VarRef)) {
                createDeepTemp(expp, true);
            }
        }
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*) override {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit PremitVisitor(AstNetlist* nodep)
        : m_tempNames{"__Vtemp"} {
        iterate(nodep);
    }
    ~PremitVisitor() override {
        V3Stats::addStat("Optimizations, Prelim extracted value to ConstPool",
                         m_extractedToConstPool);
    }
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Premit class functions

void V3Premit::premitAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { PremitVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("premit", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
