// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Assert.h"
#include "V3Ast.h"
#include "V3GraphDfa.h"
#include "V3Stats.h"

#include <cstdarg>
#include <iomanip>

//######################################################################
// Assert class functions

class AssertVisitor : public AstNVisitor {
private:
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user()         -> bool.  True if processed
    AstUser1InUse       m_inuser1;

    // STATE
    AstNodeModule*      m_modp;         // Last module
    AstBegin*   m_beginp;       // Last begin
    unsigned    m_modPastNum;   // Module past numbering
    VDouble0    m_statCover;  // Statistic tracking
    VDouble0    m_statAsNotImm;  // Statistic tracking
    VDouble0    m_statAsImm;    // Statistic tracking
    VDouble0    m_statAsFull;   // Statistic tracking

    // METHODS
    string assertDisplayMessage(AstNode* nodep, const string& prefix, const string& message) {
        return (string("[%0t] "+prefix+": ")+nodep->fileline()->filebasename()
                +":"+cvtToStr(nodep->fileline()->lineno())
                +": Assertion failed in %m"
                +((message != "")?": ":"")+message
                +"\n");
    }
    void replaceDisplay(AstDisplay* nodep, const string& prefix) {
        nodep->displayType(AstDisplayType::DT_WRITE);
        nodep->fmtp()->text(assertDisplayMessage(nodep, prefix, nodep->fmtp()->text()));
        // cppcheck-suppress nullPointer
        AstNode* timenewp = new AstTime(nodep->fileline());
        if (AstNode* timesp = nodep->fmtp()->exprsp()) {
            timesp->unlinkFrBackWithNext();
            timenewp->addNext(timesp);
        }
        nodep->fmtp()->addExprsp(timenewp);
        if (!nodep->fmtp()->scopeNamep() && nodep->fmtp()->formatScopeTracking()) {
            nodep->fmtp()->scopeNamep(new AstScopeName(nodep->fileline()));
        }
    }

    AstNode* newIfAssertOn(AstNode* nodep) {
        // Add a internal if to check assertions are on.
        // Don't make this a AND term, as it's unlikely to need to test this.
        FileLine* fl = nodep->fileline();
        AstNode* newp
            = new AstIf(fl,
                        // If assertions are off, have constant propagation rip them out later
                        // This allows syntax errors and such to be detected normally.
                        (v3Global.opt.assertOn()
                         ? static_cast<AstNode*>(new AstCMath(fl, "Verilated::assertOn()", 1))
                         : static_cast<AstNode*>(new AstConst(fl, AstConst::LogicFalse()))),
                        nodep, NULL);
        newp->user1(true);  // Don't assert/cover this if
        return newp;
    }

    AstNode* newFireAssertUnchecked(AstNode* nodep, const string& message) {
        // Like newFireAssert() but omits the asserts-on check
        AstDisplay* dispp = new AstDisplay(nodep->fileline(),
                                           AstDisplayType::DT_ERROR, message, NULL, NULL);
        AstNode* bodysp = dispp;
        replaceDisplay(dispp, "%%Error");  // Convert to standard DISPLAY format
        bodysp->addNext(new AstStop(nodep->fileline(), true));
        return bodysp;
    }

    AstNode* newFireAssert(AstNode* nodep, const string& message) {
        AstNode* bodysp = newFireAssertUnchecked(nodep, message);
        bodysp = newIfAssertOn(bodysp);
        return bodysp;
    }

    void newPslAssertion(AstNodeCoverOrAssert* nodep, AstNode* failsp) {
        if (m_beginp && nodep->name() == "") nodep->name(m_beginp->name());

        AstNode* propp = nodep->propp()->unlinkFrBackWithNext();
        AstSenTree* sentreep = nodep->sentreep();
        const string& message = nodep->name();
        AstNode* passsp = nodep->passsp();
        if (passsp) passsp->unlinkFrBackWithNext();
        if (failsp) failsp->unlinkFrBackWithNext();

        if (nodep->immediate()) {
            UASSERT_OBJ(!sentreep, nodep, "Immediate assertions don't have sensitivity");
        } else {
            UASSERT_OBJ(sentreep, nodep, "Concurrent assertions must have sensitivity");
            sentreep->unlinkFrBack();
        }
        //
        AstNode* bodysp = NULL;
        bool selfDestruct = false;
        AstIf* ifp = NULL;
        if (AstCover* snodep = VN_CAST(nodep, Cover)) {
            ++m_statCover;
            if (!v3Global.opt.coverageUser()) {
                selfDestruct = true;
            } else {
                // V3Coverage assigned us a bucket to increment.
                AstCoverInc* covincp = VN_CAST(snodep->coverincp(), CoverInc);
                UASSERT_OBJ(covincp, snodep, "Missing AstCoverInc under assertion");
                covincp->unlinkFrBackWithNext();  // next() might have  AstAssign for trace
                if (message!="") covincp->declp()->comment(message);
                bodysp = covincp;
            }

            if (bodysp && passsp) bodysp = bodysp->addNext(passsp);
            ifp = new AstIf(nodep->fileline(), propp, bodysp, NULL);
            bodysp = ifp;
        } else if (VN_IS(nodep, Assert)) {
            if (nodep->immediate()) ++m_statAsImm;
            else ++m_statAsNotImm;
            if (passsp) passsp = newIfAssertOn(passsp);
            if (failsp) failsp = newIfAssertOn(failsp);
            if (!failsp) failsp = newFireAssertUnchecked(nodep, "'assert' failed.");
            ifp = new AstIf(nodep->fileline(), propp, passsp, failsp);
            // It's more LIKELY that we'll take the NULL if clause
            // than the sim-killing else clause:
            ifp->branchPred(VBranchPred::BP_LIKELY);
            bodysp = newIfAssertOn(ifp);
        } else {
            nodep->v3fatalSrc("Unknown node type");
        }

        AstNode* newp;
        if (sentreep) {
            newp = new AstAlways(nodep->fileline(),
                                 VAlwaysKwd::ALWAYS, sentreep, bodysp);
        } else { newp = bodysp; }
        // Install it
        if (selfDestruct) {
            // Delete it after making the tree.  This way we can tell the user
            // if it wasn't constructed nicely or has other errors without needing --coverage.
            VL_DO_DANGLING(newp->deleteTree(), newp);
            nodep->unlinkFrBack();
        } else {
            nodep->replaceWith(newp);
        }
        // Bye
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    virtual void visit(AstIf* nodep) VL_OVERRIDE {
        if (nodep->user1SetOnce()) return;
        if (nodep->uniquePragma() || nodep->unique0Pragma()) {
            AstNodeIf* ifp = nodep;
            AstNode* propp = NULL;
            bool hasDefaultElse = false;
            do {
                // If this statement ends with 'else if', then nextIf will point to the
                // nextIf statement.  Otherwise it will be null.
                AstNodeIf* nextifp = dynamic_cast<AstNodeIf*>(ifp->elsesp());
                iterateAndNextNull(ifp->condp());

                // Recurse into the true case.
                iterateAndNextNull(ifp->ifsp());

                // If the last else is not an else if, recurse into that too.
                if (ifp->elsesp() && !nextifp) {
                    iterateAndNextNull(ifp->elsesp());
                }

                // Build a bitmask of the true predicates
                AstNode* predp = ifp->condp()->cloneTree(false);
                if (propp) {
                    propp = new AstConcat(nodep->fileline(), predp, propp);
                } else {
                    propp = predp;
                }

                // Record if this ends with an 'else' that does not have an if
                if (ifp->elsesp() && !nextifp) {
                    hasDefaultElse = true;
                }

                ifp = nextifp;
            } while (ifp);

            AstNode *newifp = nodep->cloneTree(false);
            bool allow_none = nodep->unique0Pragma();

            // Empty case means no property
            if (!propp) propp = new AstConst(nodep->fileline(), AstConst::LogicFalse());

            // Note: if this ends with an 'else', then we don't need to validate that one of the
            // predicates evaluates to true.
            AstNode* ohot = ((allow_none || hasDefaultElse)
                             ? static_cast<AstNode*>(new AstOneHot0(nodep->fileline(), propp))
                             : static_cast<AstNode*>(new AstOneHot(nodep->fileline(), propp)));
            AstIf* checkifp = new AstIf(nodep->fileline(),
                                        new AstLogNot(nodep->fileline(), ohot),
                                        newFireAssert(nodep, "'unique if' statement violated"),
                                        newifp);
            checkifp->branchPred(VBranchPred::BP_UNLIKELY);
            nodep->replaceWith(checkifp);
            pushDeletep(nodep);
        } else {
            iterateChildren(nodep);
        }
    }

    //========== Case assertions
    virtual void visit(AstCase* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            bool has_default = false;
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
                if (itemp->isDefault()) has_default = true;
            }
            if (nodep->fullPragma() || nodep->priorityPragma()) {
                // Simply need to add a default if there isn't one already
                ++m_statAsFull;
                if (!has_default) {
                    nodep->addItemsp(new AstCaseItem(nodep->fileline(), NULL/*DEFAULT*/,
                                                     newFireAssert(nodep, "synthesis full_case, but non-match found")));
                }
            }
            if (nodep->parallelPragma() || nodep->uniquePragma() || nodep->unique0Pragma()) {
                // Need to check that one, and only one of the case items match at any moment
                // If there's a default, we allow none to match, else exactly one must match
                ++m_statAsFull;
                if (!has_default && !nodep->itemsp()) {
                    // Not parallel, but harmlessly so.
                } else {
                    AstNode* propp = NULL;
                    for (AstCaseItem* itemp = nodep->itemsp();
                         itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
                        for (AstNode* icondp = itemp->condsp();
                             icondp!=NULL; icondp=icondp->nextp()) {
                            AstNode* onep;
                            if (nodep->casex() || nodep->casez() || nodep->caseInside()) {
                                onep = AstEqWild::newTyped(itemp->fileline(),
                                                           nodep->exprp()->cloneTree(false),
                                                           icondp->cloneTree(false));
                            } else {
                                onep = AstEq::newTyped(icondp->fileline(),
                                                       nodep->exprp()->cloneTree(false),
                                                       icondp->cloneTree(false));
                            }
                            if (propp) propp = new AstConcat(icondp->fileline(), onep, propp);
                            else propp = onep;
                        }
                    }
                    // Empty case means no property
                    if (!propp) propp = new AstConst(nodep->fileline(), AstConst::LogicFalse());

                    bool allow_none = has_default || nodep->unique0Pragma();
                    AstNode* ohot
                        = (allow_none
                           ? static_cast<AstNode*>(new AstOneHot0(nodep->fileline(), propp))
                           : static_cast<AstNode*>(new AstOneHot(nodep->fileline(), propp)));
                    AstIf* ifp = new AstIf(nodep->fileline(),
                                           new AstLogNot(nodep->fileline(), ohot),
                                           newFireAssert(nodep, "synthesis parallel_case, but multiple matches found"),
                                           NULL);
                    ifp->branchPred(VBranchPred::BP_UNLIKELY);
                    nodep->addNotParallelp(ifp);
                }
            }
        }
    }

    //========== Past
    virtual void visit(AstPast* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        uint32_t ticks = 1;
        if (nodep->ticksp()) {
            UASSERT_OBJ(VN_IS(nodep->ticksp(), Const), nodep,
                        "Expected constant ticks, checked in V3Width");
            ticks = VN_CAST(nodep->ticksp(), Const)->toUInt();
        }
        UASSERT_OBJ(ticks>=1, nodep, "0 tick should have been checked in V3Width");
        AstNode* inp = nodep->exprp()->unlinkFrBack();
        AstVar* invarp = NULL;
        AstSenTree* sentreep = nodep->sentreep(); sentreep->unlinkFrBack();
        AstAlways* alwaysp = new AstAlways(nodep->fileline(), VAlwaysKwd::ALWAYS,
                                           sentreep, NULL);
        m_modp->addStmtp(alwaysp);
        for (uint32_t i=0; i<ticks; ++i) {
            AstVar* outvarp = new AstVar(nodep->fileline(), AstVarType::MODULETEMP,
                                         "_Vpast_"+cvtToStr(m_modPastNum++)+"_"+cvtToStr(i),
                                         inp->dtypep());
            m_modp->addStmtp(outvarp);
            AstNode* assp = new AstAssignDly(nodep->fileline(),
                                             new AstVarRef(nodep->fileline(), outvarp, true),
                                             inp);
            alwaysp->addStmtp(assp);
            //if (debug()>-9) assp->dumpTree(cout, "-ass: ");
            invarp = outvarp;
            inp = new AstVarRef(nodep->fileline(), invarp, false);
        }
        nodep->replaceWith(inp);
    }
    virtual void visit(AstSampled* nodep) VL_OVERRIDE {
        nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    //========== Statements
    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // Replace the special types with standard text
        if (nodep->displayType()==AstDisplayType::DT_INFO) {
            replaceDisplay(nodep, "-Info");
        } else if (nodep->displayType()==AstDisplayType::DT_WARNING) {
            replaceDisplay(nodep, "%%Warning");
        } else if (nodep->displayType()==AstDisplayType::DT_ERROR
                   || nodep->displayType()==AstDisplayType::DT_FATAL) {
            replaceDisplay(nodep, "%%Error");
        }
    }

    virtual void visit(AstAssert* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        newPslAssertion(nodep, nodep->failsp());
    }
    virtual void visit(AstCover* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        newPslAssertion(nodep, NULL);
    }
    virtual void visit(AstRestrict* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        // IEEE says simulator ignores these
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        AstNodeModule* origModp = m_modp;
        unsigned origPastNum = m_modPastNum;
        {
            m_modp = nodep;
            m_modPastNum = 0;
            iterateChildren(nodep);
        }
        m_modp = origModp;
        m_modPastNum = origPastNum;
    }
    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        // This code is needed rather than a visitor in V3Begin,
        // because V3Assert is called before V3Begin
        AstBegin* lastp = m_beginp;
        {
            m_beginp = nodep;
            iterateChildren(nodep);
        }
        m_beginp = lastp;
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit AssertVisitor(AstNetlist* nodep) {
        m_beginp = NULL;
        m_modp = NULL;
        m_modPastNum = 0;
        // Process
        iterate(nodep);
    }
    virtual ~AssertVisitor() {
        V3Stats::addStat("Assertions, assert non-immediate statements", m_statAsNotImm);
        V3Stats::addStat("Assertions, assert immediate statements", m_statAsImm);
        V3Stats::addStat("Assertions, cover statements", m_statCover);
        V3Stats::addStat("Assertions, full/parallel case", m_statAsFull);
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        AssertVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assert", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
