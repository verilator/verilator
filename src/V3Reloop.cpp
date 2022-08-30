// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Recreate loops to help pack caches
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
// V3Reloop's Transformations:
//
// Each CFunc:
//    Look for a series of assignments that would look better in a loop:
//
//      ASSIGN(ARRAYREF(var, #), ARRAYREF(var, #+C))
//      ASSIGN(ARRAYREF(var, #+1), ARRAYREF(var, #+1+C))
//      ->
//      Create __Vilp local variable
//      FOR(__Vilp = low; __Vilp <= high; ++__Vlip)
//         ASSIGN(ARRAYREF(var, __Vilp), ARRAYREF(var, __Vilp + C))
//
//   Likewise vector assign to the same constant converted to a loop.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Reloop.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <algorithm>

//######################################################################

class ReloopVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstCFunc::user1p      -> Var* for temp var, 0=not set yet
    const VNUser1InUse m_inuser1;

    // STATE
    VDouble0 m_statReloops;  // Statistic tracking
    VDouble0 m_statReItems;  // Statistic tracking
    AstCFunc* m_cfuncp = nullptr;  // Current block

    std::vector<AstNodeAssign*> m_mgAssignps;  // List of assignments merging
    AstCFunc* m_mgCfuncp = nullptr;  // Parent C function
    const AstNode* m_mgNextp = nullptr;  // Next node
    const AstNodeSel* m_mgSelLp = nullptr;  // Parent select, nullptr = idle
    const AstNodeSel* m_mgSelRp = nullptr;  // Parent select, nullptr = constant
    const AstNodeVarRef* m_mgVarrefLp = nullptr;  // Parent varref
    const AstNodeVarRef* m_mgVarrefRp = nullptr;  // Parent varref, nullptr = constant
    int64_t m_mgOffset = 0;  // Index offset
    const AstConst* m_mgConstRp = nullptr;  // Parent RHS constant, nullptr = sel
    uint32_t m_mgIndexLo = 0;  // Merge range
    uint32_t m_mgIndexHi = 0;  // Merge range

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    static AstVar* findCreateVarTemp(FileLine* fl, AstCFunc* cfuncp) {
        AstVar* varp = VN_AS(cfuncp->user1p(), Var);
        if (!varp) {
            const string newvarname{"__Vilp"};
            varp = new AstVar{fl, VVarType::STMTTEMP, newvarname, VFlagLogicPacked{}, 32};
            UASSERT_OBJ(cfuncp, fl, "Assignment not under a function");
            cfuncp->addInitsp(varp);
            cfuncp->user1p(varp);
        }
        return varp;
    }
    void mergeEnd() {
        if (!m_mgAssignps.empty()) {
            const uint32_t items = m_mgIndexHi - m_mgIndexLo + 1;
            UINFO(9, "End merge iter=" << items << " " << m_mgIndexHi << ":" << m_mgIndexLo << " "
                                       << m_mgOffset << " " << m_mgAssignps[0] << endl);
            if (items >= static_cast<uint32_t>(v3Global.opt.reloopLimit())) {
                UINFO(6, "Reloop merging items=" << items << " " << m_mgIndexHi << ":"
                                                 << m_mgIndexLo << " " << m_mgOffset << " "
                                                 << m_mgAssignps[0] << endl);
                ++m_statReloops;
                m_statReItems += items;

                // Transform first assign into for loop body
                AstNodeAssign* const bodyp = m_mgAssignps.front();
                UASSERT_OBJ(bodyp->lhsp() == m_mgSelLp, bodyp, "Corrupt queue/state");
                FileLine* const fl = bodyp->fileline();
                AstVar* const itp = findCreateVarTemp(fl, m_mgCfuncp);

                if (m_mgOffset > 0) {
                    UASSERT_OBJ(m_mgIndexLo >= m_mgOffset, bodyp,
                                "Reloop iteration starts at negative index");
                    m_mgIndexLo -= m_mgOffset;
                    m_mgIndexHi -= m_mgOffset;
                }

                AstNode* const initp = new AstAssign(fl, new AstVarRef(fl, itp, VAccess::WRITE),
                                                     new AstConst(fl, m_mgIndexLo));
                AstNode* const condp = new AstLte(fl, new AstVarRef(fl, itp, VAccess::READ),
                                                  new AstConst(fl, m_mgIndexHi));
                AstNode* const incp = new AstAssign(
                    fl, new AstVarRef(fl, itp, VAccess::WRITE),
                    new AstAdd(fl, new AstConst(fl, 1), new AstVarRef(fl, itp, VAccess::READ)));
                AstWhile* const whilep = new AstWhile(fl, condp, nullptr, incp);
                initp->addNext(whilep);
                bodyp->replaceWith(initp);
                whilep->addBodysp(bodyp);

                // Replace constant index with new loop index
                AstNode* const offsetp
                    = m_mgOffset == 0 ? nullptr : new AstConst(fl, std::abs(m_mgOffset));
                AstNode* const lbitp = m_mgSelLp->bitp();
                AstNode* const lvrefp = new AstVarRef(fl, itp, VAccess::READ);
                lbitp->replaceWith(m_mgOffset > 0 ? new AstAdd(fl, lvrefp, offsetp) : lvrefp);
                VL_DO_DANGLING(lbitp->deleteTree(), lbitp);
                if (m_mgSelRp) {  // else constant and no replace
                    AstNode* const rbitp = m_mgSelRp->bitp();
                    AstNode* const rvrefp = new AstVarRef(fl, itp, VAccess::READ);
                    rbitp->replaceWith(m_mgOffset < 0 ? new AstAdd(fl, rvrefp, offsetp) : rvrefp);
                    VL_DO_DANGLING(rbitp->deleteTree(), lbitp);
                }
                if (debug() >= 9) initp->dumpTree(cout, "-new: ");
                if (debug() >= 9) whilep->dumpTree(cout, "-new: ");

                // Remove remaining assigns
                for (AstNodeAssign* assp : m_mgAssignps) {
                    if (assp != bodyp) {
                        VL_DO_DANGLING(assp->unlinkFrBack()->deleteTree(), assp);
                    }
                }
            }
            // Setup for next merge
            m_mgAssignps.clear();
            m_mgSelLp = nullptr;
            m_mgSelRp = nullptr;
            m_mgVarrefLp = nullptr;
            m_mgVarrefRp = nullptr;
            m_mgOffset = 0;
            m_mgConstRp = nullptr;
        }
    }

    // VISITORS
    virtual void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            iterateChildren(nodep);
            mergeEnd();  // Finish last pending merge, if any
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        if (!m_cfuncp) return;

        // Left select WordSel or ArraySel
        AstNodeSel* const lselp = VN_CAST(nodep->lhsp(), NodeSel);
        if (!lselp) {  // Not ever merged
            mergeEnd();
            return;
        }
        // Of a constant index
        const AstConst* const lbitp = VN_CAST(lselp->bitp(), Const);
        if (!lbitp) {
            mergeEnd();
            return;
        }
        if (lbitp->width() > 32) {  // Assoc arrays can do this
            mergeEnd();
            return;
        }
        const uint32_t lindex = lbitp->toUInt();
        // Of variable
        const AstNodeVarRef* const lvarrefp = VN_CAST(lselp->fromp(), NodeVarRef);
        if (!lvarrefp) {
            mergeEnd();
            return;
        }

        // RHS is a constant or a select
        const AstConst* const rconstp = VN_CAST(nodep->rhsp(), Const);
        const AstNodeSel* const rselp = VN_CAST(nodep->rhsp(), NodeSel);
        const AstNodeVarRef* rvarrefp = nullptr;
        uint32_t rindex = lindex;
        if (rconstp) {  // Ok
        } else if (rselp) {
            const AstConst* const rbitp = VN_CAST(rselp->bitp(), Const);
            rvarrefp = VN_CAST(rselp->fromp(), NodeVarRef);
            if (!rbitp || !rvarrefp || lvarrefp->varp() == rvarrefp->varp()) {
                mergeEnd();
                return;
            }
            rindex = rbitp->toUInt();
        } else {
            mergeEnd();
            return;
        }

        if (m_mgSelLp) {  // Old merge
            if (m_mgCfuncp == m_cfuncp  // In same function
                && m_mgNextp == nodep  // Consecutive node
                && m_mgVarrefLp->same(lvarrefp)  // Same array on left hand side
                && (m_mgConstRp  // On the right hand side either ...
                        ? (rconstp && m_mgConstRp->same(rconstp))  // ... same constant
                        : (rselp && m_mgVarrefRp->same(rvarrefp)))  // ... or same array
                && (lindex == m_mgIndexLo - 1 || lindex == m_mgIndexHi + 1)  // Left index +/- 1
                && (m_mgConstRp || lindex == rindex + m_mgOffset)  // Same right index offset
            ) {
                // Sequentially next to last assign; continue merge
                if (lindex == m_mgIndexLo - 1) {
                    m_mgIndexLo = lindex;
                } else if (lindex == m_mgIndexHi + 1) {
                    m_mgIndexHi = lindex;
                }
                UINFO(9, "Continue merge i=" << lindex << " " << m_mgIndexHi << ":" << m_mgIndexLo
                                             << " " << nodep << endl);
                m_mgAssignps.push_back(nodep);
                m_mgNextp = nodep->nextp();
                return;
            } else {
                UINFO(9, "End merge i="
                             << lindex << " " << m_mgIndexHi << ":" << m_mgIndexLo << " " << nodep
                             << endl);  // This assign doesn't merge with previous assign,
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
        m_mgOffset = static_cast<int64_t>(lindex) - static_cast<int64_t>(rindex);
        m_mgConstRp = rconstp;
        m_mgIndexLo = lindex;
        m_mgIndexHi = lindex;
        UINFO(9, "Start merge i=" << lindex << " o=" << m_mgOffset << nodep << endl);
    }
    //--------------------
    virtual void visit(AstVar*) override {}  // Accelerate
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ReloopVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ReloopVisitor() override {
        V3Stats::addStat("Optimizations, Reloops", m_statReloops);
        V3Stats::addStat("Optimizations, Reloop iterations", m_statReItems);
    }
};

//######################################################################
// Reloop class functions

void V3Reloop::reloopAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ReloopVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("reloop", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
