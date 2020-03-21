// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for premit nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
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

#include "V3Global.h"
#include "V3Premit.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <list>

//######################################################################
// Structure for global state

class PremitAssignVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstVar::user4()         // bool; occurs on LHS of current assignment
    AstUser4InUse       m_inuser4;

    // STATE
    bool        m_noopt;        // Disable optimization of variables in this block

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        //AstNode::user4ClearTree();  // Implied by AstUser4InUse
        // LHS first as fewer varrefs
        iterateAndNextNull(nodep->lhsp());
        // Now find vars marked as lhs
        iterateAndNextNull(nodep->rhsp());
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        // it's LHS var is used so need a deep temporary
        if (nodep->lvalue()) {
            nodep->varp()->user4(true);
        } else {
            if (nodep->varp()->user4()) {
                if (!m_noopt) UINFO(4, "Block has LHS+RHS var: "<<nodep<<endl);
                m_noopt = true;
            }
        }
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit PremitAssignVisitor(AstNodeAssign* nodep) {
        UINFO(4,"  PremitAssignVisitor on "<<nodep<<endl);
        m_noopt = false;
        iterate(nodep);
    }
    virtual ~PremitAssignVisitor() {}
    bool noOpt() const { return m_noopt; }
};

//######################################################################
// Premit state, as a visitor of each AstNode

class PremitVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstNodeMath::user()     -> bool.  True if iterated already
    //  AstShiftL::user2()      -> bool.  True if converted to conditional
    //  AstShiftR::user2()      -> bool.  True if converted to conditional
    //  *::user4()              -> See PremitAssignVisitor
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;

    // STATE
    AstNodeModule*      m_modp;         // Current module
    AstCFunc*           m_funcp;        // Current block
    AstNode*            m_stmtp;        // Current statement
    AstWhile*           m_inWhilep;     // Inside while loop, special statement additions
    AstTraceInc*        m_inTracep;     // Inside while loop, special statement additions
    bool                m_assignLhs;    // Inside assignment lhs, don't breakup extracts

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool assignNoTemp(AstNodeAssign* nodep) {
        return (VN_IS(nodep->lhsp(), VarRef)
                && !AstVar::scVarRecurse(nodep->lhsp())
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
        //UINFO(9, "   Check: "<<nodep<<endl);
        //UINFO(9, "     Detail stmtp="<<(m_stmtp?"Y":"N")<<" U="<<(nodep->user1()?"Y":"N")<<" IW="<<(nodep->isWide()?"Y":"N")<<endl);
        if (m_stmtp
            && !nodep->user1()) {  // Not already done
            if (nodep->isWide()) {
                if (m_assignLhs) {
                } else if (nodep->firstAbovep()
                           && VN_IS(nodep->firstAbovep(), NodeAssign)
                           && assignNoTemp(VN_CAST(nodep->firstAbovep(), NodeAssign))) {
                    // Not much point if it's just a direct assignment to a constant
                } else if (VN_IS(nodep->backp(), Sel)
                           && VN_CAST(nodep->backp(), Sel)->widthp() == nodep) {
                    // AstSel::width must remain a constant
                } else if (nodep->firstAbovep()
                           && VN_IS(nodep->firstAbovep(), ArraySel)) {
                    // ArraySel's are pointer refs, ignore
                } else {
                    UINFO(4,"Cre Temp: "<<nodep<<endl);
                    createDeepTemp(nodep, false);
                }
            }
        }
    }

    AstVar* getBlockTemp(AstNode* nodep) {
        string newvarname = (string("__Vtemp")+cvtToStr(m_modp->varNumGetInc()));
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::STMTTEMP, newvarname,
                                  nodep->dtypep());
        m_funcp->addInitsp(varp);
        return varp;
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
            AstNRelinker linker;
            m_stmtp->unlinkFrBack(&linker);
            newp->addNext(m_stmtp);
            linker.relink(newp);
        } else {
            newp->v3fatalSrc("No statement insertion point.");
        }
    }

    void createDeepTemp(AstNode* nodep, bool noSubst) {
        if (debug()>8) nodep->dumpTree(cout, "deepin:");

        AstNRelinker linker;
        nodep->unlinkFrBack(&linker);

        AstVar* varp = getBlockTemp(nodep);
        if (noSubst) varp->noSubst(true);  // Do not remove varrefs to this in V3Const
        // Replace node tree with reference to var
        AstVarRef* newp = new AstVarRef(nodep->fileline(), varp, false);
        linker.relink(newp);
        // Put assignment before the referencing statement
        AstAssign* assp = new AstAssign(nodep->fileline(),
                                        new AstVarRef(nodep->fileline(), varp, true),
                                        nodep);
        insertBeforeStmt(assp);
        if (debug()>8) assp->dumpTree(cout, "deepou:");
        nodep->user1(true);  // Don't add another assignment
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        UINFO(4," MOD   "<<nodep<<endl);
        AstNodeModule* origModp = m_modp;
        {
            m_modp = nodep;
            m_funcp = NULL;
            iterateChildren(nodep);
        }
        m_modp = origModp;
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        m_funcp = nodep;
        iterateChildren(nodep);
        m_funcp = NULL;
    }
    void startStatement(AstNode* nodep) {
        m_assignLhs = false;
        if (m_funcp) m_stmtp = nodep;
    }
    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        UINFO(4,"  WHILE  "<<nodep<<endl);
        startStatement(nodep);
        iterateAndNextNull(nodep->precondsp());
        startStatement(nodep);
        m_inWhilep = nodep;
        iterateAndNextNull(nodep->condp());
        m_inWhilep = NULL;
        startStatement(nodep);
        iterateAndNextNull(nodep->bodysp());
        iterateAndNextNull(nodep->incsp());
        m_stmtp = NULL;
    }
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        startStatement(nodep);
        {
            bool noopt = PremitAssignVisitor(nodep).noOpt();
            if (noopt && !nodep->user1()) {
                // Need to do this even if not wide, as e.g. a select may be on a wide operator
                UINFO(4,"Deep temp for LHS/RHS\n");
                createDeepTemp(nodep->rhsp(), false);
            }
        }
        iterateAndNextNull(nodep->rhsp());
        m_assignLhs = true;
        iterateAndNextNull(nodep->lhsp());
        m_assignLhs = false;
        m_stmtp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep) VL_OVERRIDE {
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        UINFO(4,"  STMT  "<<nodep<<endl);
        startStatement(nodep);
        iterateChildren(nodep);
        m_stmtp = NULL;
    }
    virtual void visit(AstTraceInc* nodep) VL_OVERRIDE {
        startStatement(nodep);
        m_inTracep = nodep;
        iterateChildren(nodep);
        m_inTracep = NULL;
        m_stmtp = NULL;
    }
    void visitShift(AstNodeBiop* nodep) {
        // Shifts of > 32/64 bits in C++ will wrap-around and generate non-0s
        if (!nodep->user2SetOnce()) {
            UINFO(4,"  ShiftFix  "<<nodep<<endl);
            const AstConst* shiftp = VN_CAST(nodep->rhsp(), Const);
            if (shiftp && shiftp->num().mostSetBitP1() > 32) {
                shiftp->v3error("Unsupported: Shifting of by over 32-bit number isn't supported."
                                <<" (This isn't a shift of 32 bits, but a shift of 2^32, or 4 billion!)\n");
            }
            if (nodep->widthMin() <= 64  // Else we'll use large operators which work right
                // C operator's width must be < maximum shift which is based on Verilog width
                && nodep->width() < (1LL<<nodep->rhsp()->widthMin())) {
                AstNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                AstNode* constzerop;
                int m1value = nodep->widthMin()-1;  // Constant of width-1; not changing dtype width
                if (nodep->signedFlavor()) {
                    // Then over shifting gives the sign bit, not all zeros
                    // Note *NOT* clean output -- just like normal shift!
                    // Create equivalent of VL_SIGNONES_(node_width)
                    constzerop = new AstNegate(nodep->fileline(),
                                               new AstShiftR(nodep->fileline(),
                                                             nodep->lhsp()->cloneTree(false),
                                                             new AstConst(nodep->fileline(),
                                                                          m1value),
                                                             nodep->width()));
                } else {
                    constzerop = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                              nodep->width(), 0);
                }
                constzerop->dtypeFrom(nodep);  // unsigned

                AstNode* constwidthp = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                    nodep->rhsp()->widthMin(), m1value);
                constwidthp->dtypeFrom(nodep->rhsp());  // unsigned
                AstCond* newp =
                    new AstCond(nodep->fileline(),
                                new AstGte(nodep->fileline(),
                                           constwidthp,
                                           nodep->rhsp()->cloneTree(false)),
                                nodep,
                                constzerop);
                replaceHandle.relink(newp);
            }
        }
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstShiftL* nodep) VL_OVERRIDE {
        visitShift(nodep);
    }
    virtual void visit(AstShiftR* nodep) VL_OVERRIDE {
        visitShift(nodep);
    }
    virtual void visit(AstShiftRS* nodep) VL_OVERRIDE {
        visitShift(nodep);
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep) VL_OVERRIDE {
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstNodeUniop* nodep) VL_OVERRIDE {
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstNodeBiop* nodep) VL_OVERRIDE {
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstUCFunc* nodep) VL_OVERRIDE {
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstSel* nodep) VL_OVERRIDE {
        iterateAndNextNull(nodep->fromp());
        {   // Only the 'from' is part of the assignment LHS
            bool prevAssign = m_assignLhs;
            m_assignLhs = false;
            iterateAndNextNull(nodep->lsbp());
            iterateAndNextNull(nodep->widthp());
            m_assignLhs = prevAssign;
        }
        checkNode(nodep);
    }
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        iterateAndNextNull(nodep->fromp());
        {   // Only the 'from' is part of the assignment LHS
            bool prevAssign = m_assignLhs;
            m_assignLhs = false;
            iterateAndNextNull(nodep->bitp());
            m_assignLhs = prevAssign;
        }
        checkNode(nodep);
    }
    virtual void visit(AstAssocSel* nodep) VL_OVERRIDE {
        iterateAndNextNull(nodep->fromp());
        {   // Only the 'from' is part of the assignment LHS
            bool prevAssign = m_assignLhs;
            m_assignLhs = false;
            iterateAndNextNull(nodep->bitp());
            m_assignLhs = prevAssign;
        }
        checkNode(nodep);
    }
    virtual void visit(AstConst* nodep) VL_OVERRIDE {
        iterateChildren(nodep); checkNode(nodep);
    }
    virtual void visit(AstNodeCond* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (nodep->expr1p()->isWide()
            && !VN_IS(nodep->condp(), Const)
            && !VN_IS(nodep->condp(), VarRef)) {
            // We're going to need the expression several times in the expanded code,
            // so might as well make it a common expression
            createDeepTemp(nodep->condp(), false);
        }
        checkNode(nodep);
    }

    // Autoflush
    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        startStatement(nodep);
        iterateChildren(nodep);
        m_stmtp = NULL;
        if (v3Global.opt.autoflush()) {
            AstNode* searchp = nodep->nextp();
            while (searchp && VN_IS(searchp, Comment)) searchp = searchp->nextp();
            if (searchp
                && VN_IS(searchp, Display)
                && nodep->filep()->sameGateTree(VN_CAST(searchp, Display)->filep())) {
                // There's another display next; we can just wait to flush
            } else {
                UINFO(4,"Autoflush "<<nodep<<endl);
                nodep->addNextHere(new AstFFlush(nodep->fileline(),
                                                 AstNode::cloneTreeNull(nodep->filep(), true)));
            }
        }
    }
    virtual void visit(AstSFormatF* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Any strings sent to a display must be var of string data type,
        // to avoid passing a pointer to a temporary.
        for (AstNode* expp=nodep->exprsp(); expp; expp = expp->nextp()) {
            if (expp->dtypep()->basicp()
                && expp->dtypep()->basicp()->isString()
                && !VN_IS(expp, VarRef)) {
                createDeepTemp(expp, true);
            }
        }
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep) VL_OVERRIDE {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit PremitVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_funcp = NULL;
        m_stmtp = NULL;
        m_inWhilep = NULL;
        m_inTracep = NULL;
        m_assignLhs = false;
        iterate(nodep);
    }
    virtual ~PremitVisitor() {}
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Premit class functions

void V3Premit::premitAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        PremitVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("premit", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
