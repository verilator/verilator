// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Create a IACTIVE(initial), SACTIVE(combo)
//      ALWAYS: Remove any-edges from sense list
//          If no POS/NEG in senselist, Fold into SACTIVE(combo)
//          Else fold into SACTIVE(sequent).
//          OPTIMIZE: When support async clocks, fold into that active if possible
//      INITIAL: Move into IACTIVE
//      WIRE: Move into SACTIVE(combo)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Active.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"
#include "V3Const.h"
#include "V3SenTree.h"  // for SenTreeSet

#include <unordered_map>

//***** See below for main transformation engine

//######################################################################
// Collect existing active names

class ActiveBaseVisitor VL_NOT_FINAL : public AstNVisitor {
protected:
    VL_DEBUG_FUNC;  // Declare debug()
};

class ActiveNamer final : public ActiveBaseVisitor {
private:
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope to add statement to
    AstActive* m_iActivep = nullptr;  // For current scope, the IActive we're building
    AstActive* m_cActivep = nullptr;  // For current scope, the SActive(combo) we're building

    SenTreeSet m_activeSens;  // Sen lists for each active we've made
    typedef std::unordered_map<AstSenTree*, AstActive*> ActiveMap;
    ActiveMap m_activeMap;  // Map sentree to active, for folding.

    // METHODS
    void addActive(AstActive* nodep) {
        UASSERT_OBJ(m_scopep, nodep, "nullptr scope");
        m_scopep->addActivep(nodep);
    }
    // VISITORS
    virtual void visit(AstScope* nodep) override {
        m_scopep = nodep;
        m_iActivep = nullptr;
        m_cActivep = nullptr;
        m_activeSens.clear();
        m_activeMap.clear();
        iterateChildren(nodep);
        // Don't clear scopep, the namer persists beyond this visit
    }
    virtual void visit(AstSenTree* nodep) override {
        // Simplify sensitivity list
        VL_DO_DANGLING(V3Const::constifyExpensiveEdit(nodep), nodep);
    }
    //--------------------
    virtual void visit(AstNodeStmt*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // METHODS
    AstScope* scopep() { return m_scopep; }
    AstActive* getCActive(FileLine* fl) {
        if (!m_cActivep) {
            m_cActivep = new AstActive(
                fl, "combo", new AstSenTree(fl, new AstSenItem(fl, AstSenItem::Combo())));
            m_cActivep->sensesStorep(m_cActivep->sensesp());
            addActive(m_cActivep);
        }
        return m_cActivep;
    }
    AstActive* getIActive(FileLine* fl) {
        if (!m_iActivep) {
            m_iActivep = new AstActive(
                fl, "initial", new AstSenTree(fl, new AstSenItem(fl, AstSenItem::Initial())));
            m_iActivep->sensesStorep(m_iActivep->sensesp());
            addActive(m_iActivep);
        }
        return m_iActivep;
    }
    AstActive* getActive(FileLine* fl, AstSenTree* sensesp) {
        // Return a sentree in this scope that matches given sense list.

        AstActive* activep = nullptr;
        AstSenTree* activeSenp = m_activeSens.find(sensesp);
        if (activeSenp) {
            const auto it = m_activeMap.find(activeSenp);
            UASSERT(it != m_activeMap.end(), "Corrupt active map");
            activep = it->second;
        }

        // Not found, form a new one
        if (!activep) {
            AstSenTree* newsenp = sensesp->cloneTree(false);
            activep = new AstActive(fl, "sequent", newsenp);
            activep->sensesStorep(activep->sensesp());
            UINFO(8, "    New ACTIVE " << activep << endl);
            // Form the sensitivity list
            addActive(activep);
            m_activeMap[newsenp] = activep;
            m_activeSens.add(newsenp);
            // Note actives may have also been added above in the Active visitor
        }
        return activep;
    }

    // CONSTRUCTORS
    ActiveNamer() = default;
    virtual ~ActiveNamer() override = default;
    void main(AstScope* nodep) { iterate(nodep); }
};

//######################################################################
// Active AssignDly replacement functions

class ActiveDlyVisitor final : public ActiveBaseVisitor {
public:
    enum CheckType : uint8_t { CT_SEQ, CT_COMBO, CT_INITIAL, CT_LATCH };

private:
    CheckType m_check;  // Combo logic or other
    AstNode* m_alwaysp;  // Always we're under
    AstNode* m_assignp = nullptr;  // In assign
    // VISITORS
    virtual void visit(AstAssignDly* nodep) override {
        if (m_check != CT_SEQ) {
            // Convert to a non-delayed assignment
            UINFO(5, "    ASSIGNDLY " << nodep << endl);
            if (m_check == CT_INITIAL) {
                nodep->v3warn(INITIALDLY, "Delayed assignments (<=) in initial or final block\n"
                                              << nodep->warnMore()
                                              << "... Suggest blocking assignments (=)");
            } else if (m_check == CT_LATCH) {
                // Suppress. Shouldn't matter that the interior of the latch races
            } else {
                nodep->v3warn(COMBDLY, "Delayed assignments (<=) in non-clocked"
                                       " (non flop or latch) block\n"
                                           << nodep->warnMore()
                                           << "... Suggest blocking assignments (=)");
            }
            AstNode* newp = new AstAssign(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                          nodep->rhsp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    virtual void visit(AstAssign* nodep) override {
        if (m_check == CT_SEQ) {
            VL_RESTORER(m_assignp);
            m_assignp = nodep;
            iterateAndNextNull(nodep->lhsp());
        }
    }
    virtual void visit(AstVarRef* nodep) override {
        AstVar* varp = nodep->varp();
        if (m_check == CT_SEQ && m_assignp && !varp->isUsedLoopIdx()  // Ignore loop indices
            && !varp->isTemp()) {
            // Allow turning off warnings on the always, or the variable also
            if (!m_alwaysp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)
                && !m_assignp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)
                && !varp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ)) {
                m_assignp->v3warn(BLKSEQ,
                                  "Blocking assignments (=) in sequential (flop or latch) block\n"
                                      << m_assignp->warnMore()
                                      << "... Suggest delayed assignments (<=)");
                m_alwaysp->fileline()->modifyWarnOff(
                    V3ErrorCode::BLKSEQ, true);  // Complain just once for the entire always
                varp->fileline()->modifyWarnOff(V3ErrorCode::BLKSEQ, true);
            }
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    ActiveDlyVisitor(AstNode* nodep, CheckType check)
        : m_check{check}
        , m_alwaysp{nodep} {
        iterate(nodep);
    }
    virtual ~ActiveDlyVisitor() override = default;
};

//######################################################################
// Active class functions

class ActiveVisitor final : public ActiveBaseVisitor {
private:
    // NODE STATE
    //  Each call to V3Const::constify
    //   AstNode::user4()               Used by V3Const::constify, called below

    // STATE
    ActiveNamer m_namer;  // Tracking of active names
    AstCFunc* m_scopeFinalp = nullptr;  // Final function for this scope
    bool m_itemCombo = false;  // Found a SenItem combo
    bool m_itemSequent = false;  // Found a SenItem sequential

    // VISITORS
    virtual void visit(AstScope* nodep) override {
        // Create required actives and add to scope
        UINFO(4, " SCOPE   " << nodep << endl);
        // Clear last scope's names, and collect this scope's existing names
        m_namer.main(nodep);
        m_scopeFinalp = nullptr;
        iterateChildren(nodep);
    }
    virtual void visit(AstActive* nodep) override {
        // Actives are being formed, so we can ignore any already made
    }
    virtual void visit(AstInitial* nodep) override {
        // Relink to IACTIVE, unless already under it
        UINFO(4, "    INITIAL " << nodep << endl);
        ActiveDlyVisitor dlyvisitor(nodep, ActiveDlyVisitor::CT_INITIAL);
        AstActive* wantactivep = m_namer.getIActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignAlias* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    ASSIGNW " << nodep << endl);
        AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignW* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    ASSIGNW " << nodep << endl);
        AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstCoverToggle* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    COVERTOGGLE " << nodep << endl);
        AstActive* wantactivep = m_namer.getCActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstFinal* nodep) override {
        // Relink to CFUNC for the final
        UINFO(4, "    FINAL " << nodep << endl);
        if (!nodep->bodysp()) {  // Empty, Kill it.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        ActiveDlyVisitor dlyvisitor(nodep, ActiveDlyVisitor::CT_INITIAL);
        if (!m_scopeFinalp) {
            m_scopeFinalp = new AstCFunc(
                nodep->fileline(), "_final_" + m_namer.scopep()->nameDotless(), m_namer.scopep());
            m_scopeFinalp->argTypes(EmitCBaseVisitor::symClassVar());
            m_scopeFinalp->addInitsp(
                new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign() + "\n"));
            m_scopeFinalp->dontCombine(true);
            m_scopeFinalp->formCallTree(true);
            m_scopeFinalp->slow(true);
            m_namer.scopep()->addActivep(m_scopeFinalp);
        }
        nodep->unlinkFrBack();
        m_scopeFinalp->addStmtsp(nodep->bodysp()->unlinkFrBackWithNext());
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // METHODS
    void visitAlways(AstNode* nodep, AstSenTree* oldsensesp, VAlwaysKwd kwd) {
        // Move always to appropriate ACTIVE based on its sense list
        if (oldsensesp && oldsensesp->sensesp() && VN_IS(oldsensesp->sensesp(), SenItem)
            && VN_CAST(oldsensesp->sensesp(), SenItem)->isNever()) {
            // Never executing.  Kill it.
            UASSERT_OBJ(!oldsensesp->sensesp()->nextp(), nodep,
                        "Never senitem should be alone, else the never should be eliminated.");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }

        // Read sensitivities
        m_itemCombo = false;
        m_itemSequent = false;
        iterateAndNextNull(oldsensesp);
        bool combo = m_itemCombo;
        bool sequent = m_itemSequent;

        if (!combo && !sequent) combo = true;  // If no list, Verilog 2000: always @ (*)
        if (combo && sequent) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Mixed edge (pos/negedge) and activity "
                                         "(no edge) sensitive activity list");
            sequent = false;
        }

        AstActive* wantactivep = nullptr;
        if (combo && !sequent) {
            // Combo:  Relink to ACTIVE(combo)
            wantactivep = m_namer.getCActive(nodep->fileline());
        } else {
            // Sequential: Build a ACTIVE(name)
            // OPTIMIZE: We could substitute a constant for things in the sense list, for example
            // always (posedge RESET) { if (RESET).... }  we know RESET is true.
            // Summarize a long list of combo inputs as just "combo"
#ifndef __COVERITY__  // Else dead code on next line.
            if (combo) {
                oldsensesp->addSensesp(new AstSenItem(nodep->fileline(), AstSenItem::Combo()));
            }
#endif
            wantactivep = m_namer.getActive(nodep->fileline(), oldsensesp);
        }

        // Delete sensitivity list
        if (oldsensesp) {
            VL_DO_DANGLING(oldsensesp->unlinkFrBackWithNext()->deleteTree(), oldsensesp);
        }

        // Move node to new active
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);

        // Warn and/or convert any delayed assignments
        if (combo && !sequent) {
            if (kwd == VAlwaysKwd::ALWAYS_LATCH) {
                ActiveDlyVisitor dlyvisitor(nodep, ActiveDlyVisitor::CT_LATCH);
            } else {
                ActiveDlyVisitor dlyvisitor(nodep, ActiveDlyVisitor::CT_COMBO);
            }
        } else if (!combo && sequent) {
            ActiveDlyVisitor dlyvisitor(nodep, ActiveDlyVisitor::CT_SEQ);
        }
    }
    virtual void visit(AstAlways* nodep) override {
        // Move always to appropriate ACTIVE based on its sense list
        UINFO(4, "    ALW   " << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree(cout, "  Alw: ");

        if (!nodep->bodysp()) {
            // Empty always.  Kill it.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        visitAlways(nodep, nodep->sensesp(), nodep->keyword());
    }
    virtual void visit(AstAlwaysPostponed* nodep) override {
        UINFO(4, "    ALW   " << nodep << endl);
        if (!nodep->bodysp()) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        visitAlways(nodep, nullptr, VAlwaysKwd::ALWAYS);
    }
    virtual void visit(AstAlwaysPublic* nodep) override {
        // Move always to appropriate ACTIVE based on its sense list
        UINFO(4, "    ALWPub   " << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree(cout, "  Alw: ");
        visitAlways(nodep, nodep->sensesp(), VAlwaysKwd::ALWAYS);
    }
    virtual void visit(AstSenItem* nodep) override {
        if (nodep->varrefp()) {
            if (AstBasicDType* basicp = nodep->varrefp()->dtypep()->basicp()) {
                if (basicp->isEventValue()) {
                    // Events need to be treated as active high so we only activate on event being
                    // 1
                    UINFO(8, "Demote event to HIGHEDGE " << nodep << endl);
                    nodep->edgeType(VEdgeType::ET_HIGHEDGE);
                }
            }
        }
        if (nodep->edgeType() == VEdgeType::ET_ANYEDGE) {
            m_itemCombo = true;
            // Delete the sensitivity
            // We'll add it as a generic COMBO SenItem in a moment.
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else if (nodep->varrefp()) {
            // V3LinkResolve should have cleaned most of these up
            if (!nodep->varrefp()->width1()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Non-single bit wide signal pos/negedge sensitivity: "
                                  << nodep->varrefp()->prettyNameQ());
            }
            m_itemSequent = true;
            nodep->varrefp()->varp()->usedClock(true);
        }
    }

    //--------------------
    virtual void visit(AstNodeMath*) override {}  // Accelerate
    virtual void visit(AstVarScope*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ActiveVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ActiveVisitor() override = default;
};

//######################################################################
// Active class functions

void V3Active::activeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ActiveVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("active", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
