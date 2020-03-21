// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Recreate loops to help pack caches
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
// V3Reloop's Transformations:
//
// Each CFunc:
//    Look for a series of assignments that would look better in a loop:
//
//      ASSIGN(ARRAYREF(var, #), ARRAYREF(var, #))
//      ASSIGN(ARRAYREF(var, #+1), ARRAYREF(var, #+1))
//      ->
//      Create __Vilp local variable
//      FOR(__Vilp = low; __Vilp <= high; ++__Vlip)
//         ASSIGN(ARRAYREF(var, __Vilp), ARRAYREF(var, __Vilp))
//
//   Likewise vector assign to the same constant converted to a loop.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Reloop.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <algorithm>
#include <cstdarg>

#define RELOOP_MIN_ITERS 40  // Need at least this many loops to do this optimization

//######################################################################

class ReloopVisitor : public AstNVisitor {
private:
    // TYPES
    typedef std::vector<AstNodeAssign*>  AssVec;

    // NODE STATE
    // AstCFunc::user1p      -> Var* for temp var, 0=not set yet
    AstUser1InUse       m_inuser1;

    // STATE
    VDouble0            m_statReloops;  // Statistic tracking
    VDouble0            m_statReItems;  // Statistic tracking
    AstCFunc*           m_cfuncp;       // Current block

    AssVec              m_mgAssignps;   // List of assignments merging
    AstCFunc*           m_mgCfuncp;     // Parent C function
    AstNode*            m_mgNextp;      // Next node
    AstNodeSel*         m_mgSelLp;      // Parent select, NULL = idle
    AstNodeSel*         m_mgSelRp;      // Parent select, NULL = constant
    AstNodeVarRef*      m_mgVarrefLp;   // Parent varref
    AstNodeVarRef*      m_mgVarrefRp;   // Parent varref, NULL = constant
    AstConst*           m_mgConstRp;    // Parent RHS constant, NULL = sel
    uint32_t            m_mgIndexLo;    // Merge range
    uint32_t            m_mgIndexHi;    // Merge range

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstVar* findCreateVarTemp(FileLine* fl, AstCFunc* cfuncp) {
        AstVar* varp = VN_CAST(cfuncp->user1p(), Var);
        if (!varp) {
            string newvarname = string("__Vilp");
            varp = new AstVar(fl, AstVarType::STMTTEMP,
                              newvarname, VFlagLogicPacked(), 32);
            UASSERT_OBJ(cfuncp, fl, "Assignment not under a function");
            cfuncp->addInitsp(varp);
            cfuncp->user1p(varp);
        }
        return varp;
    }
    void mergeEnd() {
        if (!m_mgAssignps.empty()) {
            uint32_t items = m_mgIndexHi - m_mgIndexLo + 1;
            UINFO(9, "End merge iter="<<items<<" "<<m_mgIndexHi<<":"<<m_mgIndexLo
                  <<" "<<m_mgAssignps[0]<<endl);
            if (items >= RELOOP_MIN_ITERS) {
                UINFO(6, "Reloop merging items="<<items<<" "<<m_mgIndexHi<<":"<<m_mgIndexLo
                      <<" "<<m_mgAssignps[0]<<endl);
                ++m_statReloops;
                m_statReItems += items;

                // Transform first assign into for loop body
                AstNodeAssign* bodyp = m_mgAssignps.front();
                UASSERT_OBJ(bodyp->lhsp() == m_mgSelLp, bodyp, "Corrupt queue/state");
                FileLine* fl = bodyp->fileline();
                AstVar* itp = findCreateVarTemp(fl, m_mgCfuncp);

                AstNode* initp = new AstAssign(fl, new AstVarRef(fl, itp, true),
                                               new AstConst(fl, m_mgIndexLo));
                AstNode* condp = new AstLte(fl, new AstVarRef(fl, itp, false),
                                            new AstConst(fl, m_mgIndexHi));
                AstNode* incp = new AstAssign(fl, new AstVarRef(fl, itp, true),
                                              new AstAdd(fl, new AstConst(fl, 1),
                                                         new AstVarRef(fl, itp, false)));
                AstWhile* whilep = new AstWhile(fl, condp, NULL, incp);
                initp->addNext(whilep);
                bodyp->replaceWith(initp);
                whilep->addBodysp(bodyp);

                // Replace constant index with new loop index
                AstNode* lbitp = m_mgSelLp->bitp();
                lbitp->replaceWith(new AstVarRef(fl, itp, false));
                VL_DO_DANGLING(lbitp->deleteTree(), lbitp);
                if (m_mgSelRp) {  // else constant and no replace
                    AstNode* rbitp = m_mgSelRp->bitp();
                    rbitp->replaceWith(new AstVarRef(fl, itp, false));
                    VL_DO_DANGLING(rbitp->deleteTree(), lbitp);
                }
                if (debug()>=9) initp->dumpTree(cout, "-new: ");
                if (debug()>=9) whilep->dumpTree(cout, "-new: ");

                // Remove remaining assigns
                for (AssVec::iterator it=m_mgAssignps.begin(); it!=m_mgAssignps.end(); ++it) {
                    AstNodeAssign* assp = *it;
                    if (assp != bodyp) {
                        VL_DO_DANGLING(assp->unlinkFrBack()->deleteTree(), assp);
                    }
                }
            }
            // Setup for next merge
            m_mgAssignps.clear();
            m_mgSelLp = NULL;
            m_mgSelRp = NULL;
            m_mgVarrefLp = NULL;
            m_mgVarrefRp = NULL;
            m_mgConstRp = NULL;
        }
    }

    // VISITORS
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        m_cfuncp = nodep;
        iterateChildren(nodep);
        m_cfuncp = NULL;
    }
    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
        if (!m_cfuncp) return;

        // Left select WordSel or ArraySel
        AstNodeSel* lselp = VN_CAST(nodep->lhsp(), NodeSel);
        if (!lselp) { mergeEnd(); return; }  // Not ever merged
        // Of a constant index
        AstConst* lbitp = VN_CAST(lselp->bitp(), Const);
        if (!lbitp) { mergeEnd(); return; }
        if (lbitp->width() > 32) { mergeEnd(); return; }  // Assoc arrays can do this
        uint32_t index = lbitp->toUInt();
        // Of variable
        AstNodeVarRef* lvarrefp = VN_CAST(lselp->fromp(), NodeVarRef);
        if (!lvarrefp) { mergeEnd(); return; }

        // RHS is a constant or a select
        AstConst* rconstp = VN_CAST(nodep->rhsp(), Const);
        AstNodeSel* rselp = VN_CAST(nodep->rhsp(), NodeSel);
        AstNodeVarRef* rvarrefp = NULL;
        if (rconstp) {  // Ok
        } else {
            if (!rselp) { mergeEnd(); return; }
            AstConst* rbitp = VN_CAST(rselp->bitp(), Const);
            rvarrefp = VN_CAST(rselp->fromp(), NodeVarRef);
            if (!rbitp || rbitp->toUInt() != index
                || !rvarrefp
                || lvarrefp->varp() == rvarrefp->varp()) {
                mergeEnd(); return;
            }
        }

        if (m_mgSelLp) {  // Old merge
            if (m_mgCfuncp == m_cfuncp
                && m_mgNextp == nodep
                && m_mgSelLp->same(lselp)
                && m_mgVarrefLp->same(lvarrefp)
                && (m_mgConstRp
                    ? (rconstp && m_mgConstRp->same(rconstp))
                    : (rselp
                       && m_mgSelRp->same(rselp)
                       && m_mgVarrefRp->same(rvarrefp)))
                && (index == m_mgIndexLo-1
                    || index == m_mgIndexHi+1)) {
                // Sequentially next to last assign; continue merge
                if (index == m_mgIndexLo-1) m_mgIndexLo = index;
                else if (index == m_mgIndexHi+1) m_mgIndexHi = index;
                UINFO(9, "Continue merge i="<<index
                      <<" "<<m_mgIndexHi<<":"<<m_mgIndexLo<<" "<<nodep<<endl);
                m_mgAssignps.push_back(nodep);
                m_mgNextp = nodep->nextp();
                return;
            }
            else {
                // This assign doesn't merge with previous assign,
                // but should start a new merge
                mergeEnd();
            }
        }

        // Merge start
        m_mgAssignps.push_back(nodep);
        m_mgCfuncp = m_cfuncp;
        m_mgNextp = nodep->nextp();
        m_mgSelLp = lselp;
        m_mgSelRp = rselp;
        m_mgVarrefLp = lvarrefp;
        m_mgVarrefRp = rvarrefp;
        m_mgConstRp = rconstp;
        m_mgIndexLo = index;
        m_mgIndexHi = index;
        UINFO(9, "Start merge i="<<index<<" "<<nodep<<endl);
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep) VL_OVERRIDE {}  // Speedup
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {}  // Speedup
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit ReloopVisitor(AstNetlist* nodep) {
        m_cfuncp = NULL;
        m_mgCfuncp = NULL;
        m_mgNextp = NULL;
        m_mgSelLp = NULL;
        m_mgSelRp = NULL;
        m_mgVarrefLp = NULL;
        m_mgVarrefRp = NULL;
        m_mgConstRp = NULL;
        m_mgIndexLo = 0;
        m_mgIndexHi = 0;
        iterate(nodep);
    }
    virtual ~ReloopVisitor() {
        V3Stats::addStat("Optimizations, Reloops", m_statReloops);
        V3Stats::addStat("Optimizations, Reloop iterations", m_statReItems);
    }
};

//######################################################################
// Reloop class functions

void V3Reloop::reloopAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ReloopVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("reloop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
