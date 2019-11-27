// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace return/continue with jumps
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3LinkJump's Transformations:
//
// Each module:
//      Look for BEGINs
//          BEGIN(VAR...) -> VAR ... {renamed}
//      FOR -> WHILEs
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3LinkJump.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>
#include <vector>

//######################################################################

class LinkJumpVisitor : public AstNVisitor {
private:
    // TYPES
    typedef std::vector<AstBegin*> BeginStack;

    // STATE
    AstNodeModule*      m_modp;         // Current module
    AstNodeFTask*       m_ftaskp;       // Current function/task
    AstWhile*           m_loopp;        // Current loop
    bool                m_loopInc;      // In loop increment
    int                 m_repeatNum;    // Repeat counter
    BeginStack          m_beginStack;   // All begin blocks above current node

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstJumpLabel* findAddLabel(AstNode* nodep, bool endOfIter) {
        // Put label under given node, and if WHILE optionally at end of iteration
        UINFO(4,"Create label for "<<nodep<<endl);
        if (VN_IS(nodep, JumpLabel)) return VN_CAST(nodep, JumpLabel);  // Done

        AstNode* underp = NULL;
        bool     under_and_next = true;
        if (VN_IS(nodep, Begin)) underp = VN_CAST(nodep, Begin)->stmtsp();
        else if (VN_IS(nodep, NodeFTask)) underp = VN_CAST(nodep, NodeFTask)->stmtsp();
        else if (VN_IS(nodep, While)) {
            if (endOfIter) {
                // Note we jump to end of bodysp; a FOR loop has its
                // increment under incsp() which we don't skip
                underp = VN_CAST(nodep, While)->bodysp();
            } else {
                underp = nodep; under_and_next = false;  // IE we skip the entire while
            }
        }
        else {
            nodep->v3fatalSrc("Unknown jump point for break/disable/continue");
            return NULL;
        }
        // Skip over variables as we'll just move them in a moment
        // Also this would otherwise prevent us from using a label twice
        // see t_func_return test.
        while (underp && VN_IS(underp, Var)) underp = underp->nextp();
        UASSERT_OBJ(underp, nodep, "Break/disable/continue not under expected statement");
        UINFO(5,"  Underpoint is "<<underp<<endl);

        if (VN_IS(underp, JumpLabel)) {
            return VN_CAST(underp, JumpLabel);
        } else {  // Move underp stuff to be under a new label
            AstJumpLabel* labelp = new AstJumpLabel(nodep->fileline(), NULL);

            AstNRelinker repHandle;
            if (under_and_next) underp->unlinkFrBackWithNext(&repHandle);
            else underp->unlinkFrBack(&repHandle);
            repHandle.relink(labelp);

            labelp->addStmtsp(underp);
            // Keep any AstVars under the function not under the new JumpLabel
            for (AstNode* nextp, *varp=underp; varp; varp = nextp) {
                nextp = varp->nextp();
                if (VN_IS(varp, Var)) {
                    labelp->addPrev(varp->unlinkFrBack());
                }
            }
            return labelp;
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) {
        if (nodep->dead()) return;
        m_modp = nodep;
        m_repeatNum = 0;
        iterateChildren(nodep);
        m_modp = NULL;
    }
    virtual void visit(AstNodeFTask* nodep) {
        m_ftaskp = nodep;
        iterateChildren(nodep);
        m_ftaskp = NULL;
    }
    virtual void visit(AstBegin* nodep) {
        UINFO(8,"  "<<nodep<<endl);
        m_beginStack.push_back(nodep);
        iterateChildren(nodep);
        m_beginStack.pop_back();
    }
    virtual void visit(AstRepeat* nodep) {
        // So later optimizations don't need to deal with them,
        //    REPEAT(count,body) -> loop=count,WHILE(loop>0) { body, loop-- }
        // Note var can be signed or unsigned based on original number.
        AstNode* countp = nodep->countp()->unlinkFrBackWithNext();
        string name = string("__Vrepeat")+cvtToStr(m_repeatNum++);
        // Spec says value is integral, if negative is ignored
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::BLOCKTEMP, name,
                                  nodep->findSigned32DType());
        varp->usedLoopIdx(true);
        m_modp->addStmtp(varp);
        AstNode* initsp = new AstAssign(nodep->fileline(),
                                        new AstVarRef(nodep->fileline(), varp, true),
                                        countp);
        AstNode* decp = new AstAssign(nodep->fileline(),
                                      new AstVarRef(nodep->fileline(), varp, true),
                                      new AstSub(nodep->fileline(),
                                                 new AstVarRef(nodep->fileline(), varp, false),
                                                 new AstConst(nodep->fileline(), 1)));
        AstNode* zerosp = new AstConst(nodep->fileline(), AstConst::Signed32(), 0);
        AstNode* condp = new AstGtS(nodep->fileline(),
                                    new AstVarRef(nodep->fileline(), varp, false),
                                    zerosp);
        AstNode* bodysp = nodep->bodysp(); if (bodysp) bodysp->unlinkFrBackWithNext();
        AstNode* newp = new AstWhile(nodep->fileline(),
                                     condp,
                                     bodysp,
                                     decp);
        initsp = initsp->addNext(newp);
        newp = initsp;
        nodep->replaceWith(newp);
        nodep->deleteTree(); VL_DANGLING(nodep);
    }
    virtual void visit(AstWhile* nodep) {
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
    virtual void visit(AstReturn* nodep) {
        iterateChildren(nodep);
        AstFunc* funcp = VN_CAST(m_ftaskp, Func);
        if (!m_ftaskp) {
            nodep->v3error("Return isn't underneath a task or function");
        } else if (funcp  && !nodep->lhsp()) {
            nodep->v3error("Return underneath a function should have return value");
        } else if (!funcp &&  nodep->lhsp()) {
            nodep->v3error("Return underneath a task shouldn't have return value");
        } else {
            if (funcp && nodep->lhsp()) {
                // Set output variable to return value
                nodep->addPrev(new AstAssign(nodep->fileline(),
                                             new AstVarRef(nodep->fileline(),
                                                           VN_CAST(funcp->fvarp(), Var), true),
                                             nodep->lhsp()->unlinkFrBackWithNext()));
            }
            // Jump to the end of the function call
            AstJumpLabel* labelp = findAddLabel(m_ftaskp, false);
            nodep->addPrev(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
    }
    virtual void visit(AstBreak* nodep) {
        iterateChildren(nodep);
        if (!m_loopp) { nodep->v3error("break isn't underneath a loop"); }
        else {
            // Jump to the end of the loop
            AstJumpLabel* labelp = findAddLabel(m_loopp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
    }
    virtual void visit(AstContinue* nodep) {
        iterateChildren(nodep);
        if (!m_loopp) { nodep->v3error("continue isn't underneath a loop"); }
        else {
            // Jump to the end of this iteration
            // If a "for" loop then need to still do the post-loop increment
            AstJumpLabel* labelp = findAddLabel(m_loopp, true);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
    }
    virtual void visit(AstDisable* nodep) {
        UINFO(8,"   DISABLE "<<nodep<<endl);
        iterateChildren(nodep);
        AstBegin* beginp = NULL;
        for (BeginStack::reverse_iterator it = m_beginStack.rbegin();
             it != m_beginStack.rend(); ++it) {
            UINFO(9,"    UNDERBLK  "<<*it<<endl);
            if ((*it)->name() == nodep->name()) {
                beginp = *it;
                break;
            }
        }
        //if (debug()>=9) { UINFO(0,"\n"); beginp->dumpTree(cout, "  labeli: "); }
        if (!beginp) { nodep->v3error("disable isn't underneath a begin with name: "
                                      <<nodep->prettyNameQ()); }
        else {
            // Jump to the end of the named begin
            AstJumpLabel* labelp = findAddLabel(beginp, false);
            nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
        }
        nodep->unlinkFrBack(); pushDeletep(nodep); VL_DANGLING(nodep);
        //if (debug()>=9) { UINFO(0,"\n"); beginp->dumpTree(cout, "  labelo: "); }
    }
    virtual void visit(AstVarRef* nodep) {
        if (m_loopInc && nodep->varp()) nodep->varp()->usedLoopIdx(true);
    }

    virtual void visit(AstConst* nodep) {}
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit LinkJumpVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_ftaskp = NULL;
        m_loopp = NULL;
        m_loopInc = false;
        m_repeatNum = 0;
        iterate(nodep);
    }
    virtual ~LinkJumpVisitor() {}
};

//######################################################################
// Task class functions

void V3LinkJump::linkJump(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        LinkJumpVisitor bvisitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("link", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
