// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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

#include "V3Active.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Graph.h"

#include <unordered_map>

//***** See below for main transformation engine

//######################################################################

// Extend V3GraphVertex class for use in latch detection graph

class LatchDetectGraphVertex final : public V3GraphVertex {
public:
    enum VertexType : uint8_t { VT_BLOCK, VT_BRANCH, VT_OUTPUT };

private:
    const string m_name;  // Only used for .dot file generation
    const VertexType m_type;  // Vertex type (BLOCK/BRANCH/OUTPUT)

    string typestr() const {  //   "
        switch (m_type) {
        case VT_BLOCK: return "(||)";  // basic block node
        case VT_BRANCH: return "(&&)";  // if/else branch mode
        case VT_OUTPUT: return "(out)";  // var assignment
        default: return "??";  // unknown
        }
    }

public:
    LatchDetectGraphVertex(V3Graph* graphp, const string& name, VertexType type = VT_BLOCK)
        : V3GraphVertex{graphp}
        , m_name{name}
        , m_type{type} {}
    virtual string name() const override { return m_name + " " + typestr(); }
    virtual string dotColor() const override { return user() ? "green" : "black"; }
    virtual int type() const { return m_type; }
};

//######################################################################
// Extend V3Graph class for use as a latch detection graph

class LatchDetectGraph final : public V3Graph {
protected:
    LatchDetectGraphVertex* m_curVertexp = nullptr;  // Current latch detection graph vertex
    std::vector<AstVarRef*> m_outputs;  // Vector of lvalues encountered on this pass

    VL_DEBUG_FUNC;  // Declare debug()

    static LatchDetectGraphVertex* castVertexp(void* vertexp) {
        return reinterpret_cast<LatchDetectGraphVertex*>(vertexp);
    }

    // Recursively traverse the graph to determine whether every control 'BLOCK' has an assignment
    // to the output we are currently analysing (the output whose 'user() is set), if so return
    // true. Where a BLOCK contains a BRANCH, both the if and else sides of the branch must return
    // true for the BRANCH to evalute to true. A BLOCK however needs only a single one of its
    // siblings to evaluate true in order to evaluate true itself. On output vertex only evaluates
    // true if it is the vertex we are analyzing on this check

    bool latchCheckInternal(LatchDetectGraphVertex* vertexp) {
        bool result = false;
        switch (vertexp->type()) {
        case LatchDetectGraphVertex::VT_OUTPUT:  // Base case
            result = vertexp->user();
            break;
        case LatchDetectGraphVertex::VT_BLOCK:  // (OR of potentially many siblings)
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                if (latchCheckInternal(castVertexp(edgep->top()))) {
                    result = true;
                    break;
                }
            }
            break;
        case LatchDetectGraphVertex::VT_BRANCH:  // (AND of both sibling)
                                                 // A BRANCH vertex always has exactly 2 siblings
            LatchDetectGraphVertex* const ifp = castVertexp(vertexp->outBeginp()->top());
            LatchDetectGraphVertex* const elsp
                = castVertexp(vertexp->outBeginp()->outNextp()->top());
            result = latchCheckInternal(ifp) && latchCheckInternal(elsp);
            break;
        }
        vertexp->user(result);
        return result;
    }

public:
    LatchDetectGraph() { clear(); }
    virtual ~LatchDetectGraph() override { clear(); }
    // ACCESSORS
    LatchDetectGraphVertex* currentp() { return m_curVertexp; }
    void currentp(LatchDetectGraphVertex* vertex) { m_curVertexp = vertex; }
    // METHODS
    void begin() {
        // Start a new if/else tracking graph
        // See NODE STATE comment in ActiveLatchCheckVisitor
        AstNode::user1ClearTree();
        m_curVertexp = new LatchDetectGraphVertex(this, "ROOT");
    }
    // Clear out userp field of referenced outputs on destruction
    // (occurs at the end of each combinational always block)
    void clear() {
        m_outputs.clear();
        // Calling base class clear will unlink & delete all edges & vertices
        V3Graph::clear();
        m_curVertexp = nullptr;
    }
    // Add a new control path and connect it to its parent
    LatchDetectGraphVertex* addPathVertex(LatchDetectGraphVertex* parent, const string& name,
                                          bool branch = false) {
        m_curVertexp = new LatchDetectGraphVertex{this, name,
                                                  branch ? LatchDetectGraphVertex::VT_BRANCH
                                                         : LatchDetectGraphVertex::VT_BLOCK};
        new V3GraphEdge{this, parent, m_curVertexp, 1};
        return m_curVertexp;
    }
    // Add a new output variable vertex and store a pointer to it in the user1 field of the
    // variables AstNode
    LatchDetectGraphVertex* addOutputVertex(AstVarRef* nodep) {
        LatchDetectGraphVertex* const outVertexp
            = new LatchDetectGraphVertex{this, nodep->name(), LatchDetectGraphVertex::VT_OUTPUT};
        nodep->varp()->user1p(outVertexp);
        m_outputs.push_back(nodep);
        return outVertexp;
    }
    // Connect an output assignment to its parent control block
    void addAssignment(AstVarRef* nodep) {
        LatchDetectGraphVertex* outVertexp;
        if (!nodep->varp()->user1p()) {  // Not seen this output before
            outVertexp = addOutputVertex(nodep);
        } else {
            outVertexp = castVertexp(nodep->varp()->user1p());
        }
        new V3GraphEdge(this, m_curVertexp, outVertexp, 1);
    }
    // Run latchCheckInternal on each variable assigned by the always block to see if all control
    // paths make an assignment. Detected latches are flagged in the variables AstVar
    void latchCheck(AstNode* nodep, bool latch_expected) {
        bool latch_detected = false;
        for (const auto& vrp : m_outputs) {
            LatchDetectGraphVertex* const vertp = castVertexp(vrp->varp()->user1p());
            vertp->user(true);  // Identify the output vertex we are checking paths _to_
            if (!latchCheckInternal(castVertexp(verticesBeginp()))) latch_detected = true;
            if (latch_detected && !latch_expected) {
                nodep->v3warn(
                    LATCH,
                    "Latch inferred for signal "
                        << vrp->prettyNameQ()
                        << " (not all control paths of combinational always assign a value)\n"
                        << nodep->warnMore()
                        << "... Suggest use of always_latch for intentional latches");
                if (debug() >= 9) dumpDotFilePrefixed("latch_" + vrp->name());
            }
            vertp->user(false);  // Clear again (see above)
            vrp->varp()->isLatched(latch_detected);
        }
        // Should _all_ variables assigned in always_latch be latches? Probably, but this only
        // warns if none of them are
        if (latch_expected && !latch_detected)
            nodep->v3warn(NOLATCH, "No latches detected in always_latch block");
    }
};

//######################################################################
// Collect existing active names

class ActiveBaseVisitor VL_NOT_FINAL : public VNVisitor {
protected:
    VL_DEBUG_FUNC;  // Declare debug()
};

class ActiveNamer final : public ActiveBaseVisitor {
private:
    // STATE
    AstScope* m_scopep = nullptr;  // Current scope to add statement to
    AstActive* m_iActivep = nullptr;  // For current scope, the IActive we're building
    AstActive* m_cActivep = nullptr;  // For current scope, the SActive(combo) we're building

    // Map from AstSenTree (equivalence) to the corresponding AstActive created.
    std::unordered_map<VNRef<AstSenTree>, AstActive*> m_activeMap;

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

    // Return an AstActive that is sensitive to a SenTree equivalent to the given sentreep.
    AstActive* getActive(FileLine* fl, AstSenTree* sensesp) {

        auto it = m_activeMap.find(*sensesp);
        // If found matching AstActive, return it
        if (it != m_activeMap.end()) return it->second;

        // No such AstActive yet, creat it, and add to map.
        AstSenTree* const newsenp = sensesp->cloneTree(false);
        AstActive* const activep = new AstActive(fl, "sequent", newsenp);
        activep->sensesStorep(activep->sensesp());
        addActive(activep);
        m_activeMap.emplace(*newsenp, activep);
        return activep;
    }

    // CONSTRUCTORS
    ActiveNamer() = default;
    virtual ~ActiveNamer() override = default;
    void main(AstScope* nodep) { iterate(nodep); }
};

//######################################################################
// Latch checking visitor

class ActiveLatchCheckVisitor final : public ActiveBaseVisitor {
private:
    // NODE STATE
    // Input:
    //  AstVar::user1p // V2LatchGraphVertex* The vertex handling this node
    const VNUser1InUse m_inuser1;
    // STATE
    LatchDetectGraph m_graph;  // Graph used to detect latches in combo always
    // VISITORS
    virtual void visit(AstVarRef* nodep) override {
        const AstVar* const varp = nodep->varp();
        if (nodep->access().isWriteOrRW() && varp->isSignal() && !varp->isUsedLoopIdx()) {
            m_graph.addAssignment(nodep);
        }
    }
    virtual void visit(AstNodeIf* nodep) override {
        if (!nodep->isBoundsCheck()) {
            LatchDetectGraphVertex* const parentp = m_graph.currentp();
            LatchDetectGraphVertex* const branchp = m_graph.addPathVertex(parentp, "BRANCH", true);
            m_graph.addPathVertex(branchp, "IF");
            iterateAndNextNull(nodep->ifsp());
            m_graph.addPathVertex(branchp, "ELSE");
            iterateAndNextNull(nodep->elsesp());
            m_graph.currentp(parentp);
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    ActiveLatchCheckVisitor(AstNode* nodep, VAlwaysKwd kwd) {
        m_graph.begin();
        iterate(nodep);
        m_graph.latchCheck(nodep, kwd == VAlwaysKwd::ALWAYS_LATCH);
    }
    ~ActiveLatchCheckVisitor() override = default;
};

//######################################################################
// Replace unsupported non-blocking assignments with blocking assignments

class ActiveDlyVisitor final : public ActiveBaseVisitor {
public:
    enum CheckType : uint8_t { CT_SEQ, CT_COMB, CT_INITIAL };

private:
    // MEMBERS
    const CheckType m_check;  // Process type we are checking

    // VISITORS
    virtual void visit(AstAssignDly* nodep) override {
        // Non-blocking assignments are OK in sequential processes
        if (m_check == CT_SEQ) return;

        // Issue appropriate warning
        if (m_check == CT_INITIAL) {
            nodep->v3warn(INITIALDLY,
                          "Non-blocking assignment '<=' in initial/final block\n"
                              << nodep->warnMore()
                              << "... This will be executed as a blocking assignment '='!");
        } else {
            nodep->v3warn(COMBDLY,
                          "Non-blocking assignment '<=' in combinational logic process\n"
                              << nodep->warnMore()
                              << "... This will be executed as a blocking assignment '='!");
        }

        // Convert to blocking assignment
        nodep->replaceWith(new AstAssign{nodep->fileline(),  //
                                         nodep->lhsp()->unlinkFrBack(),  //
                                         nodep->rhsp()->unlinkFrBack()});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    virtual void visit(AstAssign* nodep) override {
        // Blocking assignments are always OK in combinational (and initial/final) processes
        if (m_check != CT_SEQ) return;

        const bool ignore = nodep->lhsp()->forall<AstVarRef>([&](const AstVarRef* refp) {
            // Ignore reads (e.g.: index expressions)
            if (refp->access().isReadOnly()) return true;
            const AstVar* const varp = refp->varp();
            // Ignore ...
            return varp->isUsedLoopIdx()  // ... loop indices
                   || varp->isTemp()  // ... temporaries
                   || varp->fileline()->warnIsOff(V3ErrorCode::BLKSEQ);  // ... user said so
        });

        if (ignore) return;

        nodep->v3warn(BLKSEQ,
                      "Blocking assignment '=' in sequential logic process\n"
                          << nodep->warnMore()  //
                          << "... Suggest using delayed assignment '<='");
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    ActiveDlyVisitor(AstNode* nodep, CheckType check)
        : m_check{check} {
        iterate(nodep);
    }
    ~ActiveDlyVisitor() override = default;
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
    virtual void visit(AstInitialStatic* nodep) override {
        // Relink to IACTIVE, unless already under it
        UINFO(4, "    INITIAL " << nodep << endl);
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_INITIAL};
        AstActive* const wantactivep = m_namer.getIActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstInitial* nodep) override {
        // Relink to IACTIVE, unless already under it
        UINFO(4, "    INITIAL " << nodep << endl);
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_INITIAL};
        AstActive* const wantactivep = m_namer.getIActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignAlias* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    ASSIGNW " << nodep << endl);
        AstActive* const wantactivep = m_namer.getCActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstAssignW* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    ASSIGNW " << nodep << endl);
        AstActive* const wantactivep = m_namer.getCActive(nodep->fileline());
        nodep->unlinkFrBack();
        wantactivep->addStmtsp(nodep);
    }
    virtual void visit(AstCoverToggle* nodep) override {
        // Relink to CACTIVE, unless already under it
        UINFO(4, "    COVERTOGGLE " << nodep << endl);
        AstActive* const wantactivep = m_namer.getCActive(nodep->fileline());
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
        const ActiveDlyVisitor dlyvisitor{nodep, ActiveDlyVisitor::CT_INITIAL};
        if (!m_scopeFinalp) {
            m_scopeFinalp = new AstCFunc(
                nodep->fileline(), "_final_" + m_namer.scopep()->nameDotless(), m_namer.scopep());
            m_scopeFinalp->dontCombine(true);
            m_scopeFinalp->isFinal(true);
            m_scopeFinalp->isStatic(false);
            m_scopeFinalp->isLoose(true);
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
        if (oldsensesp && oldsensesp->sensesp() && oldsensesp->sensesp()->isNever()) {
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
            { ActiveDlyVisitor{nodep, ActiveDlyVisitor::CT_COMB}; }
            const ActiveLatchCheckVisitor latchvisitor{nodep, kwd};
        } else if (!combo && sequent) {
            ActiveDlyVisitor{nodep, ActiveDlyVisitor::CT_SEQ};
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
            if (const AstBasicDType* const basicp = nodep->varrefp()->dtypep()->basicp()) {
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
    ~ActiveVisitor() override = default;
};

//######################################################################
// Active class functions

void V3Active::activeAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ActiveVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("active", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
