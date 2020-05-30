// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace return/continue with jumps
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
// V3LinkJump's Transformations:
//
// Each module:
//   Look for BEGINs
//      BEGIN(VAR...) -> VAR ... {renamed}
//   FOR -> WHILEs
//
//   Add JumpLabel which branches to after statements within JumpLabel
//      RETURN -> JUMPBLOCK(statements with RETURN changed to JUMPGO, ..., JUMPLABEL)
//      WHILE(... BREAK) -> JUMPBLOCK(WHILE(... statements with BREAK changed to JUMPGO),
//                                    ... JUMPLABEL)
//      WHILE(... CONTINUE) -> WHILE(JUMPBLOCK(... statements with CONTINUE changed to JUMPGO,
//                                    ... JUMPPABEL))
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LinkJump.h"
#include "V3Ast.h"

#include <algorithm>
#include <vector>

//######################################################################

class LinkJumpVisitor : public AstNVisitor {
private:
    // TYPES
    typedef std::vector<AstNodeBlock*> BlockStack;

    // STATE
    AstNodeModule* m_modp;  // Current module
    AstNodeFTask* m_ftaskp;  // Current function/task
    AstWhile* m_loopp;  // Current loop
    bool m_loopInc;  // In loop increment
    bool m_inFork;  // Under fork
    int m_modRepeatNum;  // Repeat counter
    BlockStack m_blockStack;  // All begin blocks above current node

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstJumpLabel* findAddLabel(AstNode* nodep, bool endOfIter) {
        // Put label under given node, and if WHILE optionally at end of iteration
        UINFO(4, "Create label for " << nodep << endl);
        if (VN_IS(nodep, JumpLabel)) return VN_CAST(nodep, JumpLabel);  // Done

        AstNode* underp = NULL;
        bool under_and_next = true;
        if (VN_IS(nodep, NodeBlock)) {
            underp = VN_CAST(nodep, NodeBlock)->stmtsp();
        } else if (VN_IS(nodep, NodeFTask)) {
            underp = VN_CAST(nodep, NodeFTask)->stmtsp();
        } else if (VN_IS(nodep, While)) {
            if (endOfIter) {
                // Note we jump to end of bodysp; a FOR loop has its
                // increment under incsp() which we don't skip
                underp = VN_CAST(nodep, While)->bodysp();
            } else {
                underp = nodep;
                under_and_next = false;  // IE we skip the entire while
            }
        } else {
            nodep->v3fatalSrc("Unknown jump point for break/disable/continue");
            return NULL;
        }
        // Skip over variables as we'll just move them in a moment
        // Also this would otherwise prevent us from using a label twice
        // see t_func_return test.
        while (underp && VN_IS(underp, Var)) underp = underp->nextp();
        UASSERT_OBJ(underp, nodep, "Break/disable/continue not under expected statement");
        UINFO(5, "  Underpoint is " << underp << endl);

        if (VN_IS(underp, JumpLabel)) {
            return VN_CAST(underp, JumpLabel);
        } else {  // Move underp stuff to be under a new label
            AstJumpBlock* blockp = new AstJumpBlock(nodep->fileline(), NULL);
            AstJumpLabel* labelp = new AstJumpLabel(nodep->fileline(), blockp);
            blockp->labelp(labelp);

            AstNRelinker repHandle;
            if (under_and_next) {
                underp->unlinkFrBackWithNext(&repHandle);
            } else {
                underp->unlinkFrBack(&repHandle);
            }
            repHandle.relink(blockp);

            blockp->addStmtsp(underp);
            // Keep any AstVars under the function not under the new JumpLabel
            for (AstNode *nextp, *varp = underp; varp; varp = nextp) {
                nextp = varp->nextp();
                if (VN_IS(varp, Var)) blockp->addPrev(varp->unlinkFrBack());
            }
            // Label goes last
            blockp->addEndStmtsp(labelp);
            return labelp;
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        if (nodep->dead()) return;
        AstNodeModule* origModp = m_modp;
        int origRepeatNum = m_modRepeatNum;
        {
            m_modp = nodep;
            m_modRepeatNum = 0;
            iterateChildren(nodep);
        }
        m_modp = origModp;
        m_modRepeatNum = origRepeatNum;
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = NULL;
    }
    virtual void visit(AstNodeBlock* nodep) VL_OVERRIDE {
        UINFO(8, "  " << nodep << endl);
        bool oldFork = m_inFork;
        m_blockStack.push_back(nodep);
        {
            m_inFork = m_inFork || VN_IS(nodep, Fork);
            iterateChildren(nodep);
        }
        m_blockStack.pop_back();
        m_inFork = oldFork;
    }
    virtual void visit(AstRepeat* nodep) VL_OVERRIDE {
        // So later optimizations don't need to deal with them,
        //    REPEAT(count,body) -> loop=count,WHILE(loop>0) { body, loop-- }
        // Note var can be signed or unsigned based on original number.
        AstNode* countp = nodep->countp()->unlinkFrBackWithNext();
        string name = string("__Vrepeat") + cvtToStr(m_modRepeatNum++);
        // Spec says value is integral, if negative is ignored
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::BLOCKTEMP, name,
                                  nodep->findSigned32DType());
        varp->usedLoopIdx(true);
        m_modp->addStmtp(varp);
        AstNode* initsp = new AstAssign(nodep->fileline(),
                                        new AstVarRef(nodep->fileline(), varp, true), countp);
        AstNode* decp = new AstAssign(
            nodep->fileline(), new AstVarRef(nodep->fileline(), varp, true),
            new AstSub(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, false),
                       new AstConst(nodep->fileline(), 1)));
        AstNode* zerosp = new AstConst(nodep->fileline(), AstConst::Signed32(), 0);
        AstNode* condp
            = new AstGtS(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, false), zerosp);
        AstNode* bodysp = nodep->bodysp();
        if (bodysp) bodysp->unlinkFrBackWithNext();
        AstNode* newp = new AstWhile(nodep->fileline(), condp, bodysp, decp);
        initsp = initsp->addNext(newp);
        newp = initsp;
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        // Don't need to track AstRepeat/AstFor as they have already been converted
        AstWhile* lastLoopp = m_loopp;
        bool lastInc = m_loopInc;
        m_loopp = nodep;
        m_loopInc = false;
        iterateAndNextNull(nodep->precondsp());
        iterateAndNextNull(nodep->condp());
        iterateAndNextNull(nodep->bodysp());
        m_loopInc = true;
        iterateAndNextNull(nodep->incsp());
        m_loopInc = lastInc;
        m_loopp = lastLoopp;
    }
    virtual void visit(AstReturn* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        AstFunc* funcp = VN_CAST(m_ftaskp, Func);
        if (m_inFork) {
            nodep->v3error("Return isn't legal under fork (IEEE 1800-2017 9.2.3)");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        } else if (!m_ftaskp) {
            nodep->v3error("Return isn't underneath a task or function");
        } else if (funcp && !nodep->lhsp()) {
            nodep->v3error("Return underneath a function should have return value");
        } else if (!funcp && nodep->lhsp()) {
            nodep->v3error("Return underneath a task shouldn't have return value");
        } else {
            if (funcp && nodep->lhsp()) {
                // Set output variable to return value
                nodep->addPrev(new AstAssign(
                    nodep->fileline(),
                    new AstVarRef(nodep->fileline(), VN_CAST(funcp->fvarp(), Var), true),
                    nodep->lhsp()->unlinkFrBackWithNext()));
            }
            // Jump to the end of the function call
            AstJumpLabel* labelp = findAddLabel(m_ftaskp, false);
            nodep->addPrev(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstBreak* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (!m_loopp) {
            nodep->v3error("break isn't underneath a loop");
        } else {
            // Jump to the end of the loop
            AstJumpLabel* labelp = findAddLabel(m_loopp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstContinue* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (!m_loopp) {
            nodep->v3error("continue isn't underneath a loop");
        } else {
            // Jump to the end of this iteration
            // If a "for" loop then need to still do the post-loop increment
            AstJumpLabel* labelp = findAddLabel(m_loopp, true);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstDisable* nodep) VL_OVERRIDE {
        UINFO(8, "   DISABLE " << nodep << endl);
        iterateChildren(nodep);
        AstNodeBlock* blockp = NULL;
        for (BlockStack::reverse_iterator it = m_blockStack.rbegin(); it != m_blockStack.rend();
             ++it) {
            UINFO(9, "    UNDERBLK  " << *it << endl);
            if ((*it)->name() == nodep->name()) {
                blockp = *it;
                break;
            }
        }
        // if (debug() >= 9) { UINFO(0, "\n"); blockp->dumpTree(cout, "  labeli: "); }
        if (!blockp) {
            nodep->v3error("disable isn't underneath a begin with name: " << nodep->prettyNameQ());
        } else if (AstBegin* beginp = VN_CAST(blockp, Begin)) {
            // Jump to the end of the named block
            AstJumpLabel* labelp = findAddLabel(beginp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        } else {
            nodep->v3error("Unsupported: disable fork");
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        // if (debug() >= 9) { UINFO(0, "\n"); beginp->dumpTree(cout, "  labelo: "); }
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (m_loopInc && nodep->varp()) nodep->varp()->usedLoopIdx(true);
    }
    virtual void visit(AstConst*) VL_OVERRIDE {}
    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkJumpVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_ftaskp = NULL;
        m_inFork = false;
        m_loopp = NULL;
        m_loopInc = false;
        m_modRepeatNum = 0;
        iterate(nodep);
    }
    virtual ~LinkJumpVisitor() {}
};

//######################################################################
// Task class functions

void V3LinkJump::linkJump(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { LinkJumpVisitor bvisitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("link", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
