// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for unroll nodes
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
// V3Unroll's Transformations:
//      Note is called twice.  Once on modules for GenFor unrolling,
//      Again after V3Scope for normal for loop unrolling.
//
// Each module:
//      Look for "FOR" loops and unroll them if <= 32 loops.
//      (Eventually, a better way would be to simulate the entire loop; ala V3Table.)
//      Convert remaining FORs to WHILEs
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Unroll.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Simulate.h"
#include "V3Stats.h"

#include <algorithm>

//######################################################################
// Unroll state, as a visitor of each AstNode

class UnrollVisitor final : public VNVisitor {
private:
    // STATE
    AstVar* m_forVarp;  // Iterator variable
    const AstVarScope* m_forVscp;  // Iterator variable scope (nullptr for generate pass)
    AstConst* m_varValuep;  // Current value of loop
    const AstNode* m_ignoreIncp;  // Increment node to ignore
    bool m_varModeCheck;  // Just checking RHS assignments
    bool m_varModeReplace;  // Replacing varrefs
    bool m_varAssignHit;  // Assign var hit
    bool m_generate;  // Expand single generate For loop
    int m_unrollLimit;  // Unrolling limit
    string m_beginName;  // What name to give begin iterations
    VDouble0 m_statLoops;  // Statistic tracking
    VDouble0 m_statIters;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    bool cantUnroll(AstNode* nodep, const char* reason) const {
        if (m_generate)
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Can't unroll generate for; " << reason);
        UINFO(3, "   Can't Unroll: " << reason << " :" << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree(cout, "-cant-");
        V3Stats::addStatSum(std::string{"Unrolling gave up, "} + reason, 1);
        return false;
    }

    bool bodySizeOverRecurse(AstNode* nodep, int& bodySize, int bodyLimit) {
        if (!nodep) return false;
        bodySize++;
        // Exit once exceeds limits, rather than always total
        // so don't go O(n^2) when can't unroll
        if (bodySize > bodyLimit) return true;
        if (bodySizeOverRecurse(nodep->op1p(), bodySize, bodyLimit)) return true;
        if (bodySizeOverRecurse(nodep->op2p(), bodySize, bodyLimit)) return true;
        if (bodySizeOverRecurse(nodep->op3p(), bodySize, bodyLimit)) return true;
        if (bodySizeOverRecurse(nodep->op4p(), bodySize, bodyLimit)) return true;
        // Tail recurse.
        return bodySizeOverRecurse(nodep->nextp(), bodySize, bodyLimit);
    }

    bool forUnrollCheck(
        AstNode* const nodep,
        AstNode* const initp,  // Maybe under nodep (no nextp), or standalone (ignore nextp)
        AstNode* const precondsp, AstNode* condp,
        AstNode* const incp,  // Maybe under nodep or in bodysp
        AstNode* bodysp) {
        // To keep the IF levels low, we return as each test fails.
        UINFO(4, " FOR Check " << nodep << endl);
        if (initp) UINFO(6, "    Init " << initp << endl);
        if (precondsp) UINFO(6, "    Pcon " << precondsp << endl);
        if (condp) UINFO(6, "    Cond " << condp << endl);
        if (incp) UINFO(6, "    Inc  " << incp << endl);

        // Initial value check
        AstAssign* const initAssp = VN_CAST(initp, Assign);
        if (!initAssp) return cantUnroll(nodep, "no initial assignment");
        UASSERT_OBJ(!(initp->nextp() && initp->nextp() != nodep), nodep,
                    "initial assignment shouldn't be a list");
        if (!VN_IS(initAssp->lhsp(), VarRef)) {
            return cantUnroll(nodep, "no initial assignment to simple variable");
        }
        //
        // Condition check
        UASSERT_OBJ(!condp->nextp(), nodep, "conditional shouldn't be a list");
        //
        // Assignment of next value check
        const AstAssign* const incAssp = VN_CAST(incp, Assign);
        if (!incAssp) return cantUnroll(nodep, "no increment assignment");
        if (incAssp->nextp()) return cantUnroll(nodep, "multiple increments");

        m_forVarp = VN_AS(initAssp->lhsp(), VarRef)->varp();
        m_forVscp = VN_AS(initAssp->lhsp(), VarRef)->varScopep();
        if (VN_IS(nodep, GenFor) && !m_forVarp->isGenVar()) {
            nodep->v3error("Non-genvar used in generate for: " << m_forVarp->prettyNameQ());
        } else if (!VN_IS(nodep, GenFor) && m_forVarp->isGenVar()) {
            nodep->v3error("Genvar not legal in non-generate for (IEEE 1800-2017 27.4): "
                           << m_forVarp->prettyNameQ() << '\n'
                           << nodep->warnMore()
                           << "... Suggest move for loop upwards to generate-level scope.");
        }
        if (m_generate) V3Const::constifyParamsEdit(initAssp->rhsp());  // rhsp may change

        // This check shouldn't be needed when using V3Simulate
        // however, for repeat loops, the loop variable is auto-generated
        // and the initp statements will reference a variable outside of the initp scope
        // alas, failing to simulate.
        const AstConst* const constInitp = VN_CAST(initAssp->rhsp(), Const);
        if (!constInitp) return cantUnroll(nodep, "non-constant initializer");

        //
        // Now, make sure there's no assignment to this variable in the loop
        m_varModeCheck = true;
        m_varAssignHit = false;
        m_ignoreIncp = incp;
        iterateAndNextNull(precondsp);
        iterateAndNextNull(bodysp);
        iterateAndNextNull(incp);
        m_varModeCheck = false;
        m_ignoreIncp = nullptr;
        if (m_varAssignHit) return cantUnroll(nodep, "genvar assigned *inside* loop");

        //
        if (m_forVscp) {
            UINFO(8, "   Loop Variable: " << m_forVscp << endl);
        } else {
            UINFO(8, "   Loop Variable: " << m_forVarp << endl);
        }
        if (debug() >= 9) nodep->dumpTree(cout, "-   for: ");

        if (!m_generate) {
            const AstAssign* const incpAssign = VN_AS(incp, Assign);
            if (!canSimulate(incpAssign->rhsp())) {
                return cantUnroll(incp, "Unable to simulate increment");
            }
            if (!canSimulate(condp)) return cantUnroll(condp, "Unable to simulate condition");

            // Check whether to we actually want to try and unroll.
            int loops;
            if (!countLoops(initAssp, condp, incp, m_unrollLimit, loops)) {
                return cantUnroll(nodep, "Unable to simulate loop");
            }

            // Less than 10 statements in the body?
            int bodySize = 0;
            int bodyLimit = v3Global.opt.unrollStmts();
            if (loops > 0) bodyLimit = v3Global.opt.unrollStmts() / loops;
            if (bodySizeOverRecurse(precondsp, bodySize /*ref*/, bodyLimit)
                || bodySizeOverRecurse(bodysp, bodySize /*ref*/, bodyLimit)
                || bodySizeOverRecurse(incp, bodySize /*ref*/, bodyLimit)) {
                return cantUnroll(nodep, "too many statements");
            }
        }
        // Finally, we can do it
        if (!forUnroller(nodep, initAssp, condp, precondsp, incp, bodysp)) {
            return cantUnroll(nodep, "Unable to unroll loop");
        }
        VL_DANGLING(nodep);
        // Cleanup
        return true;
    }

    bool canSimulate(AstNode* nodep) {
        SimulateVisitor simvis;
        AstNode* clonep = nodep->cloneTree(true);
        simvis.mainCheckTree(clonep);
        VL_DO_CLEAR(pushDeletep(clonep), clonep = nullptr);
        return simvis.optimizable();
    }

    bool simulateTree(AstNode* nodep, const V3Number* loopValue, AstNode* dtypep,
                      V3Number& outNum) {
        AstNode* clonep = nodep->cloneTree(true);
        UASSERT_OBJ(clonep, nodep, "Failed to clone tree");
        if (loopValue) {
            m_varValuep = new AstConst(nodep->fileline(), *loopValue);
            // Iteration requires a back, so put under temporary node
            AstBegin* tempp = new AstBegin(nodep->fileline(), "[EditWrapper]", clonep);
            m_varModeReplace = true;
            iterateAndNextNull(tempp->stmtsp());
            m_varModeReplace = false;
            clonep = tempp->stmtsp()->unlinkFrBackWithNext();
            tempp->deleteTree();
            tempp = nullptr;
            VL_DO_CLEAR(pushDeletep(m_varValuep), m_varValuep = nullptr);
        }
        SimulateVisitor simvis;
        simvis.mainParamEmulate(clonep);
        if (!simvis.optimizable()) {
            UINFO(3, "Unable to simulate" << endl);
            if (debug() >= 9) nodep->dumpTree(cout, "- _simtree: ");
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return false;
        }
        // Fetch the result
        V3Number* resp = simvis.fetchNumberNull(clonep);
        if (!resp) {
            UINFO(3, "No number returned from simulation" << endl);
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return false;
        }
        // Patch up datatype
        if (dtypep) {
            AstConst new_con{clonep->fileline(), *resp};
            new_con.dtypeFrom(dtypep);
            outNum = new_con.num();
            outNum.isSigned(dtypep->isSigned());
            VL_DO_DANGLING(clonep->deleteTree(), clonep);
            return true;
        }
        outNum = *resp;
        VL_DO_DANGLING(clonep->deleteTree(), clonep);
        return true;
    }

    bool countLoops(AstAssign* initp, AstNode* condp, AstNode* incp, int max, int& outLoopsr) {
        outLoopsr = 0;
        V3Number loopValue{initp};
        if (!simulateTree(initp->rhsp(), nullptr, initp, loopValue)) {  //
            return false;
        }
        while (true) {
            V3Number res{initp};
            if (!simulateTree(condp, &loopValue, nullptr, res)) {  //
                return false;
            }
            if (!res.isEqOne()) break;

            outLoopsr++;

            // Run inc
            AstAssign* const incpass = VN_AS(incp, Assign);
            V3Number newLoopValue{initp};
            if (!simulateTree(incpass->rhsp(), &loopValue, incpass, newLoopValue)) {
                return false;
            }
            loopValue.opAssign(newLoopValue);
            if (outLoopsr > max) return false;
        }
        return true;
    }

    bool forUnroller(AstNode* nodep, AstAssign* initp, AstNode* condp, AstNode* precondsp,
                     AstNode* incp, AstNode* bodysp) {
        UINFO(9, "forUnroller " << nodep << endl);
        V3Number loopValue{nodep};
        if (!simulateTree(initp->rhsp(), nullptr, initp, loopValue)) {  //
            return false;
        }
        AstNode* stmtsp = nullptr;
        if (initp) {
            initp->unlinkFrBack();  // Always a single statement; nextp() may be nodep
            // Don't add to list, we do it once, and setting loop index isn't
            // needed if we have > 1 loop, as we're constant propagating it
        }
        if (precondsp) {
            precondsp->unlinkFrBackWithNext();
            stmtsp = AstNode::addNextNull(stmtsp, precondsp);
        }
        if (bodysp) {
            bodysp->unlinkFrBackWithNext();
            stmtsp = AstNode::addNextNull(stmtsp, bodysp);  // Maybe null if no body
        }
        if (incp && !VN_IS(nodep, GenFor)) {  // Generates don't need to increment loop index
            incp->unlinkFrBackWithNext();
            stmtsp = AstNode::addNextNull(stmtsp, incp);  // Maybe null if no body
        }
        // Mark variable to disable some later warnings
        m_forVarp->usedLoopIdx(true);

        AstNode* newbodysp = nullptr;
        ++m_statLoops;
        if (stmtsp) {
            int times = 0;
            while (true) {
                UINFO(8, "      Looping " << loopValue << endl);
                V3Number res{nodep};
                if (!simulateTree(condp, &loopValue, nullptr, res)) {
                    nodep->v3error("Loop unrolling failed.");
                    return false;
                }
                if (!res.isEqOne()) {
                    break;  // Done with the loop
                } else {
                    // Replace iterator values with constant.
                    AstNode* oneloopp = stmtsp->cloneTree(true);

                    m_varValuep = new AstConst(nodep->fileline(), loopValue);

                    // Iteration requires a back, so put under temporary node
                    if (oneloopp) {
                        AstBegin* const tempp
                            = new AstBegin(oneloopp->fileline(), "[EditWrapper]", oneloopp);
                        m_varModeReplace = true;
                        iterateAndNextNull(tempp->stmtsp());
                        m_varModeReplace = false;
                        oneloopp = tempp->stmtsp()->unlinkFrBackWithNext();
                        VL_DO_DANGLING(tempp->deleteTree(), tempp);
                    }
                    if (m_generate) {
                        const string index = AstNode::encodeNumber(m_varValuep->toSInt());
                        const string nname = m_beginName + "__BRA__" + index + "__KET__";
                        oneloopp = new AstBegin(oneloopp->fileline(), nname, oneloopp, true);
                    }
                    VL_DO_CLEAR(pushDeletep(m_varValuep), m_varValuep = nullptr);
                    if (newbodysp) {
                        newbodysp->addNext(oneloopp);
                    } else {
                        newbodysp = oneloopp;
                    }

                    ++m_statIters;
                    if (++times / 3 > m_unrollLimit) {
                        nodep->v3error(
                            "Loop unrolling took too long;"
                            " probably this is an infinite loop, or set --unroll-count above "
                            << m_unrollLimit);
                        break;
                    }

                    // loopValue += valInc
                    AstAssign* const incpass = VN_AS(incp, Assign);
                    V3Number newLoopValue{nodep};
                    if (!simulateTree(incpass->rhsp(), &loopValue, incpass, newLoopValue)) {
                        nodep->v3error("Loop unrolling failed");
                        return false;
                    }
                    loopValue.opAssign(newLoopValue);
                }
            }
        }
        if (!newbodysp) {  // initp might have effects after the loop
            newbodysp = initp;  // Maybe nullptr
            initp = nullptr;
        }
        // Replace the FOR()
        if (newbodysp) {
            nodep->replaceWith(newbodysp);
        } else {
            nodep->unlinkFrBack();
        }
        if (bodysp) VL_DO_DANGLING(pushDeletep(bodysp), bodysp);
        if (precondsp) VL_DO_DANGLING(pushDeletep(precondsp), precondsp);
        if (initp) VL_DO_DANGLING(pushDeletep(initp), initp);
        if (incp && !incp->backp()) VL_DO_DANGLING(pushDeletep(incp), incp);
        if (debug() >= 9 && newbodysp) newbodysp->dumpTree(cout, "-  _new: ");
        return true;
    }

    virtual void visit(AstWhile* nodep) override {
        iterateChildren(nodep);
        if (m_varModeCheck || m_varModeReplace) {
        } else {
            // Constify before unroll call, as it may change what is underneath.
            if (nodep->precondsp()) {
                V3Const::constifyEdit(nodep->precondsp());  // precondsp may change
            }
            if (nodep->condp()) V3Const::constifyEdit(nodep->condp());  // condp may change
            // Grab initial value
            AstNode* initp = nullptr;  // Should be statement before the while.
            if (nodep->backp()->nextp() == nodep) initp = nodep->backp();
            if (initp) VL_DO_DANGLING(V3Const::constifyEdit(initp), initp);
            if (nodep->backp()->nextp() == nodep) initp = nodep->backp();
            // Grab assignment
            AstNode* incp = nullptr;  // Should be last statement
            AstNode* bodysp = nodep->bodysp();
            if (nodep->incsp()) V3Const::constifyEdit(nodep->incsp());
            // cppcheck-suppress duplicateCondition
            if (nodep->incsp()) {
                incp = nodep->incsp();
            } else {
                for (incp = nodep->bodysp(); incp && incp->nextp(); incp = incp->nextp()) {}
                if (incp) VL_DO_DANGLING(V3Const::constifyEdit(incp), incp);
                // Again, as may have changed
                bodysp = nodep->bodysp();
                for (incp = nodep->bodysp(); incp && incp->nextp(); incp = incp->nextp()) {}
                if (incp == bodysp) bodysp = nullptr;
            }
            // And check it
            if (forUnrollCheck(nodep, initp, nodep->precondsp(), nodep->condp(), incp, bodysp)) {
                VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Did replacement
            }
        }
    }
    virtual void visit(AstGenFor* nodep) override {
        if (!m_generate || m_varModeReplace) {
            iterateChildren(nodep);
        }  // else V3Param will recursively call each for loop to be unrolled for us
        if (m_varModeCheck || m_varModeReplace) {
        } else {
            // Constify before unroll call, as it may change what is underneath.
            if (nodep->initsp()) V3Const::constifyEdit(nodep->initsp());  // initsp may change
            if (nodep->condp()) V3Const::constifyEdit(nodep->condp());  // condp may change
            if (nodep->incsp()) V3Const::constifyEdit(nodep->incsp());  // incsp may change
            if (nodep->condp()->isZero()) {
                // We don't need to do any loops.  Remove the GenFor,
                // Genvar's don't care about any initial assignments.
                //
                // Note normal For's can't do exactly this deletion, as
                // we'd need to initialize the variable to the initial
                // condition, but they'll become while's which can be
                // deleted by V3Const.
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            } else if (forUnrollCheck(nodep, nodep->initsp(), nullptr, nodep->condp(),
                                      nodep->incsp(), nodep->bodysp())) {
                VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Did replacement
            } else {
                nodep->v3error("For loop doesn't have genvar index, or is malformed");
            }
        }
    }
    virtual void visit(AstNodeFor* nodep) override {
        if (m_generate) {  // Ignore for's when expanding genfor's
            iterateChildren(nodep);
        } else {
            nodep->v3error("V3Begin should have removed standard FORs");
        }
    }

    virtual void visit(AstVarRef* nodep) override {
        if (m_varModeCheck && nodep->varp() == m_forVarp && nodep->varScopep() == m_forVscp
            && nodep->access().isWriteOrRW()) {
            UINFO(8, "   Itervar assigned to: " << nodep << endl);
            m_varAssignHit = true;
        }

        if (m_varModeReplace && nodep->varp() == m_forVarp && nodep->varScopep() == m_forVscp
            && nodep->access().isReadOnly()) {
            AstNode* const newconstp = m_varValuep->cloneTree(false);
            nodep->replaceWith(newconstp);
            pushDeletep(nodep);
        }
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) override {
        if (m_varModeCheck && nodep == m_ignoreIncp) {
            // Ignore subtree that is the increment
        } else {
            iterateChildren(nodep);
        }
    }

public:
    // CONSTRUCTORS
    UnrollVisitor() { init(false, ""); }
    virtual ~UnrollVisitor() override {
        V3Stats::addStatSum("Optimizations, Unrolled Loops", m_statLoops);
        V3Stats::addStatSum("Optimizations, Unrolled Iterations", m_statIters);
    }
    // METHODS
    void init(bool generate, const string& beginName) {
        m_forVarp = nullptr;
        m_forVscp = nullptr;
        m_varValuep = nullptr;
        m_ignoreIncp = nullptr;
        m_varModeCheck = false;
        m_varModeReplace = false;
        m_varAssignHit = false;
        m_generate = generate;
        m_unrollLimit = v3Global.opt.unrollCount();
        if (generate) {
            m_unrollLimit = std::numeric_limits<int>::max() / 16 > m_unrollLimit
                                ? m_unrollLimit * 16
                                : std::numeric_limits<int>::max();
        }
        m_beginName = beginName;
    }
    void process(AstNode* nodep, bool generate, const string& beginName) {
        init(generate, beginName);
        iterate(nodep);
    }
};

//######################################################################
// Unroll class functions

UnrollStateful::UnrollStateful()
    : m_unrollerp{new UnrollVisitor} {}
UnrollStateful::~UnrollStateful() { delete m_unrollerp; }

void UnrollStateful::unrollGen(AstNodeFor* nodep, const string& beginName) {
    UINFO(5, __FUNCTION__ << ": " << endl);
    m_unrollerp->process(nodep, true, beginName);
}

void UnrollStateful::unrollAll(AstNetlist* nodep) { m_unrollerp->process(nodep, false, ""); }

void V3Unroll::unrollAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        UnrollStateful unroller;
        unroller.unrollAll(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("unroll", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
