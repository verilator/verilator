// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace return/continue with jumps
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

#include "V3LinkJump.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <algorithm>
#include <vector>

//######################################################################

class LinkJumpVisitor final : public VNVisitor {
private:
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNode* m_loopp = nullptr;  // Current loop
    bool m_loopInc = false;  // In loop increment
    bool m_inFork = false;  // Under fork
    int m_modRepeatNum = 0;  // Repeat counter
    std::vector<AstNodeBlock*> m_blockStack;  // All begin blocks above current node

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstJumpLabel* findAddLabel(AstNode* nodep, bool endOfIter) {
        // Put label under given node, and if WHILE optionally at end of iteration
        UINFO(4, "Create label for " << nodep << endl);
        if (VN_IS(nodep, JumpLabel)) return VN_AS(nodep, JumpLabel);  // Done

        AstNode* underp = nullptr;
        bool under_and_next = true;
        if (VN_IS(nodep, NodeBlock)) {
            underp = VN_AS(nodep, NodeBlock)->stmtsp();
        } else if (VN_IS(nodep, NodeFTask)) {
            underp = VN_AS(nodep, NodeFTask)->stmtsp();
        } else if (VN_IS(nodep, Foreach)) {
            if (endOfIter) {
                underp = VN_AS(nodep, Foreach)->bodysp();
            } else {
                underp = nodep;
                under_and_next = false;  // IE we skip the entire foreach
            }
        } else if (VN_IS(nodep, While)) {
            if (endOfIter) {
                // Note we jump to end of bodysp; a FOR loop has its
                // increment under incsp() which we don't skip
                underp = VN_AS(nodep, While)->bodysp();
            } else {
                underp = nodep;
                under_and_next = false;  // IE we skip the entire while
            }
        } else {
            nodep->v3fatalSrc("Unknown jump point for break/disable/continue");
            return nullptr;
        }
        // Skip over variables as we'll just move them in a moment
        // Also this would otherwise prevent us from using a label twice
        // see t_func_return test.
        while (underp && VN_IS(underp, Var)) underp = underp->nextp();
        UASSERT_OBJ(underp, nodep, "Break/disable/continue not under expected statement");
        UINFO(5, "  Underpoint is " << underp << endl);

        if (VN_IS(underp, JumpLabel)) {
            return VN_AS(underp, JumpLabel);
        } else {  // Move underp stuff to be under a new label
            AstJumpBlock* const blockp = new AstJumpBlock(nodep->fileline(), nullptr);
            AstJumpLabel* const labelp = new AstJumpLabel(nodep->fileline(), blockp);
            blockp->labelp(labelp);

            VNRelinker repHandle;
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
    virtual void visit(AstNodeModule* nodep) override {
        if (nodep->dead()) return;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modRepeatNum);
        {
            m_modp = nodep;
            m_modRepeatNum = 0;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = nullptr;
    }
    virtual void visit(AstNodeBlock* nodep) override {
        UINFO(8, "  " << nodep << endl);
        VL_RESTORER(m_inFork);
        m_blockStack.push_back(nodep);
        {
            m_inFork = m_inFork || VN_IS(nodep, Fork);
            iterateChildren(nodep);
        }
        m_blockStack.pop_back();
    }
    virtual void visit(AstRepeat* nodep) override {
        // So later optimizations don't need to deal with them,
        //    REPEAT(count,body) -> loop=count,WHILE(loop>0) { body, loop-- }
        // Note var can be signed or unsigned based on original number.
        AstNode* const countp = nodep->countp()->unlinkFrBackWithNext();
        const string name = string("__Vrepeat") + cvtToStr(m_modRepeatNum++);
        // Spec says value is integral, if negative is ignored
        AstVar* const varp
            = new AstVar(nodep->fileline(), VVarType::BLOCKTEMP, name, nodep->findSigned32DType());
        varp->usedLoopIdx(true);
        m_modp->addStmtp(varp);
        AstNode* initsp = new AstAssign(
            nodep->fileline(), new AstVarRef(nodep->fileline(), varp, VAccess::WRITE), countp);
        AstNode* const decp = new AstAssign(
            nodep->fileline(), new AstVarRef(nodep->fileline(), varp, VAccess::WRITE),
            new AstSub(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, VAccess::READ),
                       new AstConst(nodep->fileline(), 1)));
        AstNode* const zerosp = new AstConst(nodep->fileline(), AstConst::Signed32(), 0);
        AstNode* const condp = new AstGtS(
            nodep->fileline(), new AstVarRef(nodep->fileline(), varp, VAccess::READ), zerosp);
        AstNode* const bodysp = nodep->bodysp();
        if (bodysp) bodysp->unlinkFrBackWithNext();
        AstNode* newp = new AstWhile(nodep->fileline(), condp, bodysp, decp);
        initsp = initsp->addNext(newp);
        newp = initsp;
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstWait* nodep) override {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: wait statements");
        // Statements we'll just execute immediately; equivalent to if they followed this
        if (AstNode* const bodysp = nodep->bodysp()) {
            bodysp->unlinkFrBackWithNext();
            nodep->replaceWith(bodysp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstWhile* nodep) override {
        // Don't need to track AstRepeat/AstFor as they have already been converted
        VL_RESTORER(m_loopp);
        VL_RESTORER(m_loopInc);
        {
            m_loopp = nodep;
            m_loopInc = false;
            iterateAndNextNull(nodep->precondsp());
            iterateAndNextNull(nodep->condp());
            iterateAndNextNull(nodep->bodysp());
            m_loopInc = true;
            iterateAndNextNull(nodep->incsp());
        }
    }
    virtual void visit(AstForeach* nodep) override {
        VL_RESTORER(m_loopp);
        {
            m_loopp = nodep;
            iterateAndNextNull(nodep->bodysp());
        }
    }
    virtual void visit(AstReturn* nodep) override {
        iterateChildren(nodep);
        const AstFunc* const funcp = VN_CAST(m_ftaskp, Func);
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
                    new AstVarRef(nodep->fileline(), VN_AS(funcp->fvarp(), Var), VAccess::WRITE),
                    nodep->lhsp()->unlinkFrBackWithNext()));
            }
            // Jump to the end of the function call
            AstJumpLabel* const labelp = findAddLabel(m_ftaskp, false);
            nodep->addPrev(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstBreak* nodep) override {
        iterateChildren(nodep);
        if (!m_loopp) {
            nodep->v3error("break isn't underneath a loop");
        } else {
            // Jump to the end of the loop
            AstJumpLabel* const labelp = findAddLabel(m_loopp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstContinue* nodep) override {
        iterateChildren(nodep);
        if (!m_loopp) {
            nodep->v3error("continue isn't underneath a loop");
        } else {
            // Jump to the end of this iteration
            // If a "for" loop then need to still do the post-loop increment
            AstJumpLabel* const labelp = findAddLabel(m_loopp, true);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstDisable* nodep) override {
        UINFO(8, "   DISABLE " << nodep << endl);
        iterateChildren(nodep);
        AstNodeBlock* blockp = nullptr;
        for (AstNodeBlock* const stackp : vlstd::reverse_view(m_blockStack)) {
            UINFO(9, "    UNDERBLK  " << stackp << endl);
            if (stackp->name() == nodep->name()) {
                blockp = stackp;
                break;
            }
        }
        // if (debug() >= 9) { UINFO(0, "\n"); blockp->dumpTree(cout, "  labeli: "); }
        if (!blockp) {
            nodep->v3error("disable isn't underneath a begin with name: " << nodep->prettyNameQ());
        } else if (AstBegin* const beginp = VN_CAST(blockp, Begin)) {
            // Jump to the end of the named block
            AstJumpLabel* const labelp = findAddLabel(beginp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        } else {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: disable fork");
        }
        nodep->unlinkFrBack();
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        // if (debug() >= 9) { UINFO(0, "\n"); beginp->dumpTree(cout, "  labelo: "); }
    }
    virtual void visit(AstVarRef* nodep) override {
        if (m_loopInc && nodep->varp()) nodep->varp()->usedLoopIdx(true);
    }
    virtual void visit(AstConst*) override {}
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkJumpVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~LinkJumpVisitor() override = default;
};

//######################################################################
// Task class functions

void V3LinkJump::linkJump(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { LinkJumpVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkjump", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
