// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Deals with tristate logic
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Tristate's Transformations:
//
// Modify the design to expand tristate logic into its
// corresponding two state representation. At the lowest levels,
//
// In detail:
//
// Over each module, from child to parent:
//   Build a graph, connecting signals together so we can propagate tristates
//     Variable becomes tristate with
//       VAR->isInoutish
//       VAR->isPullup/isPulldown (converted to AstPullup/AstPulldown
//       BufIf0/1
//   All variables on the LHS need to become tristate when there is:
//       CONST-> with Z value on the RHS of an assignment
//       AstPin with lower connection a tristate
//       A tristate signal on the RHS
//       (this can't generally be determined until that signal is resolved)
//   When LHS becomes tristate, then mark all RHS nodes as tristate
//   so any tristate varrefs on the right will propagate.
//
// Walk graph's tristate indication on each logic block with tristates
// propagating downstream to every other logic block.
//
// Expressions that have Z in them are converted into two state
// drivers and corresponding output enable signals are generated.
// These enable signals get transformed and regenerated through any
// logic that they may go through until they hit the module level.  At
// the module level, all the output enable signals from what can be
// many tristate drivers are combined together to produce a single
// driver and output enable. If the signal propagates up into higher
// modules, then new ports are created with for the signal with
// suffixes __en and __out. The original port is turned from an inout
// to an input and the __out port carries the output driver signal and
// the __en port carried the output enable for that driver.
//
// Note 1800-2012 adds user defined resolution functions. This suggests
// long term this code should be scoped-based and resolve all nodes at once
// rather than hierarchically. If/when that is done, make sure to avoid
// duplicating vars and logic that is common between each instance of a
// module.
//
//
// Another thing done in this phase is signal strength handling.
// Currently they are only supported in assignments and gates parsed as assignments (see verilog.y)
// when any of the cases occurs:
// - it is possible to statically resolve all drivers,
// - all assignments that passed the static resolution have symmetric strengths (the same strength
// is related to both 0 and 1 values).
//
// It is possible to statically resolve all drivers when the strongest assignment has RHS marked as
// non-tristate. If the RHS is equal to z, that assignment has to be skipped. Since the value may
// be not known at Verilation time, cases with tristates on RHS can't be handled statically.
//
// Static resolution is split into 2 parts.
// First part can be done before tristate propagation. It is about removing assignments that are
// weaker or equally strong as the strongest assignment with constant on RHS that has all bits
// the same (equal to 0 or 1). It is done in the following way:
// - The assignment of value 0 (size may be greater than 1), that has greatest strength (the
// one corresponding to 0) of all other assignments of 0, has to be found.
// - The same is done for value '1 and strength corresponding to value 1.
// - The greater of these two strengths is chosen. If they are equal the one that corresponds
// to 1 is taken as the greatest.
// - All assignments, that have strengths weaker or equal to the one that was found before, are
// removed. They are the assignments with constants on the RHS and also all assignments that have
// both strengths non-greater that the one was found, because they are weaker no matter what is on
// RHS.
//
// Second part of static resolution is done after tristate propagation.
// At that moment it is known that some expressions can't be equal to z. The exact value is
// unknown (except the ones with constants that were handled before), so weaker of both strengths
// has to be taken into account. All weaker assignments can be safely removed. It is done in
// similar way to the first part:
// - The assignment with non-tristate RHS with the greatest weaker strength has to be found.
// - Then all not stronger assignments can be removed.
//
// All assignments that are stronger than the strongest with non-tristate RHS are then tried to be
// handled dynamically. Currently it is supported only on assignments with symmetric strengths.
// In this case, the exact value of the RHS doesn't matter. It only matters if it equals z or not.
// Such assignments are handled by changing the values to z of these bits that are overwritten by
// stronger assignments. Then all assignments can be aggregated as they would have equal strengths
// (by | on them and their __en expressions). To change the value to z, the RHS should be & with
// negation of __en expression of stronger assignments. Changing RHS's __en expression is not
// needed, because it will be then aggregated with __en expression of stronger assignments using |,
// so & with the negation can be safely skipped.
// So the values of overwritten bits are actually changed to 0, which doesn't affect stronger
// assignments, because | operation was used.
//
// Dynamic handling is implemented in the following way:
// - group the assignments by their strengths,
// - handle assignments of the same strength by aggregating values with |
// - assign results to var__strength and var__strength__en variables
// - aggregate the results:
// orp = orp | (var__strength & ~enp)
// enp = enp | var__strength__en,
// where orp is aggregated value and enp is aggregated __en value.
//
// There is a possible problem with equally strong assignments, because multiple assignments with
// the same strength, but different values should result in x value, but these values are
// unsupported.
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Tristate.h"

#include "V3Ast.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Inst.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class TristateBaseVisitor VL_NOT_FINAL : public VNVisitor {
public:
    // METHODS
};

//######################################################################
// Graph support classes

class TristateVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TristateVertex, V3GraphVertex)
    AstNode* const m_nodep;
    bool m_isTristate = false;  // Logic indicates a tristate
    bool m_feedsTri = false;  // Propagates to a tristate node (on RHS)
    bool m_processed = false;  // Tristating was cleaned up
public:
    TristateVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    ~TristateVertex() override = default;
    // ACCESSORS
    AstNode* nodep() const VL_MT_STABLE { return m_nodep; }
    const AstVar* varp() const { return VN_CAST(nodep(), Var); }
    string name() const override {
        return ((isTristate() ? "tri\\n"
                 : feedsTri() ? "feed\\n"
                              : "-\\n")
                + (nodep()->prettyTypeName() + " " + cvtToHex(nodep())));
    }
    string dotColor() const override {
        return (varp() ? (isTristate() ? "darkblue"
                          : feedsTri() ? "blue"
                                       : "lightblue")
                       : (isTristate() ? "darkgreen"
                          : feedsTri() ? "green"
                                       : "lightgreen"));
    }
    FileLine* fileline() const override { return nodep()->fileline(); }
    void isTristate(bool flag) { m_isTristate = flag; }
    bool isTristate() const VL_MT_SAFE { return m_isTristate; }
    void feedsTri(bool flag) { m_feedsTri = flag; }
    bool feedsTri() const VL_MT_SAFE { return m_feedsTri; }
    void processed(bool flag) { m_processed = flag; }
    bool processed() const { return m_processed; }
};

//######################################################################

class TristateGraph final {
    // NODE STATE
    //   AstVar::user5p         -> TristateVertex* for variable being built
    // VNUser5InUse     m_inuser5;   // In visitor below

    // TYPES
public:
    using VarVec = std::vector<AstVar*>;

private:
    // MEMBERS
    V3Graph m_graph;  // Logic graph

public:
    // CONSTRUCTORS
    TristateGraph() { clear(); }
    virtual ~TristateGraph() { clear(); }
    VL_UNCOPYABLE(TristateGraph);

private:
    // METHODS

    TristateVertex* makeVertex(AstNode* nodep) {
        TristateVertex* vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
        if (!vertexp) {
            UINFO(6, "         New vertex " << nodep << endl);
            vertexp = new TristateVertex{&m_graph, nodep};
            nodep->user5p(vertexp);
        }
        return vertexp;
    }

    // METHODS - Graph optimization
    void graphWalkRecurseFwd(TristateVertex* vtxp, int level) {
        // Propagate tristate forward to all sinks
        // For example if on a CONST, propagate through CONCATS to ASSIGN
        // to LHS VARREF of signal to tristate
        if (!vtxp->isTristate()) return;  // tristate involved
        if (vtxp->user() == 1) return;
        vtxp->user(1);  // Recursed
        UINFO(9, "  Mark tri " << level << "  " << vtxp << endl);
        if (!vtxp->varp()) {  // not a var where we stop the recursion
            for (V3GraphEdge* edgep = vtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                TristateVertex* const vvertexp = static_cast<TristateVertex*>(edgep->top());
                // Doesn't hurt to not check if already set, but by doing so when we
                // print out the debug messages, we'll see this node at level 0 instead.
                if (!vvertexp->isTristate()) {
                    vvertexp->isTristate(true);
                    graphWalkRecurseFwd(vvertexp, level + 1);
                }
            }
        } else {
            // A variable is tristated.  Find all of the LHS VARREFs that
            // drive this signal now need tristate drivers
            for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                TristateVertex* const vvertexp = static_cast<TristateVertex*>(edgep->fromp());
                if (const AstVarRef* const refp = VN_CAST(vvertexp->nodep(), VarRef)) {
                    if (refp->access().isWriteOrRW()
                        // Doesn't hurt to not check if already set, but by doing so when we
                        // print out the debug messages, we'll see this node at level 0 instead.
                        && !vvertexp->isTristate()) {
                        vvertexp->isTristate(true);
                        graphWalkRecurseFwd(vvertexp, level + 1);
                    }
                }
            }
        }
    }
    void graphWalkRecurseBack(TristateVertex* vtxp, int level) {
        // Called only on a tristate node; propagate a feedsTri attribute "backwards"
        // towards any driving nodes, i.e. from a LHS VARREF back to a driving RHS VARREF
        // This way if the RHS VARREF is also tristated we'll connect the
        // enables up to the LHS VARREF. Otherwise if not marked
        // feedsTri() we'll drop the LHS' enables, if any
        if (!(vtxp->isTristate() || vtxp->feedsTri())) return;  // tristate involved
        if (vtxp->user() == 3) return;
        vtxp->user(3);  // Recursed
        UINFO(9, "  Mark feedstri " << level << "  " << vtxp << endl);
        if (!vtxp->varp()) {  // not a var where we stop the recursion
            for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                TristateVertex* const vvertexp = static_cast<TristateVertex*>(edgep->fromp());
                // Doesn't hurt to not check if already set, but by doing so when we
                // print out the debug messages, we'll see this node at level 0 instead.
                if (!vvertexp->feedsTri()) {
                    vvertexp->feedsTri(true);
                    graphWalkRecurseBack(vvertexp, level + 1);
                }
            }
        }
    }

public:
    // METHODS
    bool empty() const { return m_graph.empty(); }
    void clear() {
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            const TristateVertex* const vvertexp = static_cast<TristateVertex*>(itp);
            if (vvertexp->isTristate() && !vvertexp->processed()) {
                // Not v3errorSrc as no reason to stop the world
                vvertexp->nodep()->v3error("Unsupported tristate construct"
                                           " (in graph; not converted): "
                                           << vvertexp->nodep()->prettyTypeName());
            }
        }
        m_graph.clear();
        AstNode::user5ClearTree();  // Wipe all node user5p's that point to vertexes
    }
    void graphWalk(AstNodeModule* nodep) {
        UINFO(9, " Walking " << nodep << endl);
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            graphWalkRecurseFwd(static_cast<TristateVertex*>(itp), 0);
        }
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            graphWalkRecurseBack(static_cast<TristateVertex*>(itp), 0);
        }
        if (dumpGraphLevel() >= 9) m_graph.dumpDotFilePrefixed("tri_pos__" + nodep->name());
    }
    void associate(AstNode* fromp, AstNode* top) {
        new V3GraphEdge{&m_graph, makeVertex(fromp), makeVertex(top), 1};
    }
    void deleteVerticesFromSubtreeRecurse(AstNode* nodep) {
        if (!nodep) return;
        // Skip vars, because they may be connected to more than one varref
        if (!VN_IS(nodep, Var)) {
            TristateVertex* const vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
            if (vertexp) vertexp->unlinkDelete(&m_graph);
        }
        deleteVerticesFromSubtreeRecurse(nodep->op1p());
        deleteVerticesFromSubtreeRecurse(nodep->op2p());
        deleteVerticesFromSubtreeRecurse(nodep->op3p());
        deleteVerticesFromSubtreeRecurse(nodep->op4p());
    }
    void setTristate(AstNode* nodep) { makeVertex(nodep)->isTristate(true); }
    bool isTristate(AstNode* nodep) {
        const TristateVertex* const vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
        return vertexp && vertexp->isTristate();
    }
    bool feedsTri(AstNode* nodep) {
        const TristateVertex* const vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
        return vertexp && vertexp->feedsTri();
    }
    void didProcess(AstNode* nodep) {
        TristateVertex* const vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
        if (!vertexp) {
            // Not v3errorSrc as no reason to stop the world
            nodep->v3error("Unsupported tristate construct (not in propagation graph): "
                           << nodep->prettyTypeName());
        } else {
            // We don't warn if no vertexp->isTristate() as the creation
            // process makes midling nodes that don't have it set
            vertexp->processed(true);
        }
    }
    // ITERATOR METHODS
    VarVec tristateVars() {
        // Return all tristate variables
        VarVec v;
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            const TristateVertex* const vvertexp = static_cast<TristateVertex*>(itp);
            if (vvertexp->isTristate()) {
                if (AstVar* const nodep = VN_CAST(vvertexp->nodep(), Var)) v.push_back(nodep);
            }
        }
        return v;
    }
};

//######################################################################
// Given a node, flip any VarRef from LValue to RValue (i.e. make it an input)
// See also V3LinkLValue::linkLValueSet

class TristatePinVisitor final : public TristateBaseVisitor {
    TristateGraph& m_tgraph;
    const bool m_lvalue;  // Flip to be an LVALUE
    // VISITORS
    void visit(AstVarRef* nodep) override {
        UASSERT_OBJ(!nodep->access().isRW(), nodep, "Tristate unexpected on R/W access flip");
        if (m_lvalue && !nodep->access().isWriteOrRW()) {
            UINFO(9, "  Flip-to-LValue " << nodep << endl);
            nodep->access(VAccess::WRITE);
        } else if (!m_lvalue && !nodep->access().isReadOnly()) {
            UINFO(9, "  Flip-to-RValue " << nodep << endl);
            nodep->access(VAccess::READ);
            // Mark the ex-output as tristated
            UINFO(9, "  setTristate-subpin " << nodep->varp() << endl);
            m_tgraph.setTristate(nodep->varp());
        }
    }
    void visit(AstArraySel* nodep) override {
        // Doesn't work because we'd set lvalue on the array index's var
        UASSERT_OBJ(!m_lvalue, nodep, "ArraySel conversion to output, under tristate node");
        iterateChildren(nodep);
    }
    void visit(AstSliceSel* nodep) override {
        // Doesn't work because we'd set lvalue on the array index's var
        UASSERT_OBJ(!m_lvalue, nodep, "SliceSel conversion to output, under tristate node");
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    TristatePinVisitor(AstNode* nodep, TristateGraph& tgraph, bool lvalue)
        : m_tgraph(tgraph)  // Need () or GCC 4.8 false warning
        , m_lvalue{lvalue} {
        iterate(nodep);
    }
    ~TristatePinVisitor() override = default;
};

//######################################################################

class TristateVisitor final : public TristateBaseVisitor {
    // NODE STATE
    //   *::user1p              -> pointer to output enable __en expressions
    //   *::user2               -> int - already visited, see U2_ enum
    //   AstVar::user3p         -> AstPull* pullup/pulldown direction (input Var's user3p)
    //   AstVar::user4p         -> AstVar* pointer to output __out var (input Var's user2p)
    // See TristateGraph:
    //   AstVar::user5p         -> TristateVertex* for variable being built
    //   AstStmt*::user5p       -> TristateVertex* for this statement
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;
    const VNUser4InUse m_inuser4;
    const VNUser5InUse m_inuser5;

    // TYPES
    struct RefStrength {
        AstVarRef* m_varrefp;
        VStrength m_strength;
        RefStrength(AstVarRef* varrefp, VStrength strength)
            : m_varrefp{varrefp}
            , m_strength{strength} {}
    };
    using RefStrengthVec = std::vector<RefStrength>;
    using VarMap = std::unordered_map<AstVar*, RefStrengthVec*>;
    using Assigns = std::vector<AstAssignW*>;
    using VarToAssignsMap = std::map<AstVar*, Assigns>;
    enum : uint8_t {
        U2_GRAPHING = 1,  // bit[0] if did m_graphing visit
        U2_NONGRAPH = 2,  // bit[1] if did !m_graphing visit
        U2_BOTH = 3
    };  // Both bits set

    // MEMBERS
    bool m_graphing = false;  // Major mode - creating graph
    //
    AstNodeModule* m_modp = nullptr;  // Current module
    AstCell* m_cellp = nullptr;  // current cell
    VarMap m_lhsmap;  // Tristate left-hand-side driver map
    VarToAssignsMap m_assigns;  // Assigns in current module
    int m_unique = 0;
    bool m_alhs = false;  // On LHS of assignment
    VStrength m_currentStrength = VStrength::STRONG;  // Current strength of assignment,
                                                      // Used only on LHS of assignment
    const AstNode* m_logicp = nullptr;  // Current logic being built
    TristateGraph m_tgraph;  // Logic graph

    // STATS
    VDouble0 m_statTriSigs;  // stat tracking

    // METHODS
    string dbgState() const {
        string o = (m_graphing ? " gr " : " ng ");
        if (m_alhs) o += "alhs ";
        return o;
    }
    void modAddStmtp(AstNode* nodep, AstNode* newp) {
        if (!m_modp) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Creating tristate signal not underneath a module: "
                              << nodep->prettyNameQ());
        } else {
            m_modp->addStmtsp(newp);
        }
    }
    void associateLogic(AstNode* fromp, AstNode* top) {
        if (m_logicp) m_tgraph.associate(fromp, top);
    }
    AstConst* newAllZerosOrOnes(AstNode* nodep, bool ones) {
        V3Number num{nodep, nodep->width()};
        if (ones) num.setAllBits1();
        AstConst* const newp = new AstConst{nodep->fileline(), num};
        return newp;
    }
    AstNodeExpr* getEnp(AstNode* nodep) {
        if (nodep->user1p()) {
            if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
                if (refp->varp()->isIO()) {
                    // When reading a tri-state port, we can always use the value
                    // because such port will have resolution logic in upper module.
                    return newAllZerosOrOnes(nodep, true);
                }
            }
        } else {
            // There's no select being built yet, so add what will become a
            // constant output enable driver of all 1's
            nodep->user1p(newAllZerosOrOnes(nodep, true));
        }
        // Otherwise return the previous output enable
        return VN_AS(nodep->user1p(), NodeExpr);
    }
    AstVar* getCreateEnVarp(AstVar* invarp) {
        // Return the master __en for the specified input variable
        if (!invarp->user1p()) {
            AstVar* const newp = new AstVar{invarp->fileline(), VVarType::MODULETEMP,
                                            invarp->name() + "__en", invarp};
            UINFO(9, "       newenv " << newp << endl);
            modAddStmtp(invarp, newp);
            invarp->user1p(newp);  // find envar given invarp
        }
        return VN_AS(invarp->user1p(), Var);
    }
    AstConst* getNonZConstp(AstConst* const constp) {
        FileLine* const fl = constp->fileline();
        V3Number numz{constp, constp->width()};
        numz.opBitsZ(constp->num());  // Z->1, else 0
        V3Number numz0{constp, constp->width()};
        numz0.opNot(numz);  // Z->0, else 1
        return new AstConst{fl, numz0};
    }
    AstNodeExpr* getEnExprBasedOnOriginalp(AstNodeExpr* const nodep) {
        if (AstVarRef* const varrefp = VN_CAST(nodep, VarRef)) {
            return new AstVarRef{varrefp->fileline(), getCreateEnVarp(varrefp->varp()),
                                 VAccess::READ};
        } else if (AstConst* const constp = VN_CAST(nodep, Const)) {
            return getNonZConstp(constp);
        } else if (AstExtend* const extendp = VN_CAST(nodep, Extend)) {
            // Extend inserts 0 at the beginning. 0 in __en variable means that this bit equals z,
            // so in order to preserve the value of the original AstExtend node we should insert 1
            // instead of 0. To extend __en expression we have to negate its lhsp() and then negate
            // whole extend.

            // Unlink lhsp before copying to save unnecessary copy of lhsp
            AstNodeExpr* const lhsp = extendp->lhsp()->unlinkFrBack();
            AstExtend* const enExtendp = extendp->cloneTreePure(false);
            extendp->lhsp(lhsp);
            AstNodeExpr* const enLhsp = getEnExprBasedOnOriginalp(lhsp);
            enExtendp->lhsp(new AstNot{enLhsp->fileline(), enLhsp});
            return new AstNot{enExtendp->fileline(), enExtendp};
        } else if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            AstNodeExpr* const fromp = selp->fromp()->unlinkFrBack();
            AstSel* const enSelp = selp->cloneTreePure(false);
            selp->fromp(fromp);
            AstNodeExpr* const enFromp = getEnExprBasedOnOriginalp(fromp);
            enSelp->fromp(enFromp);
            return enSelp;
        } else {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported tristate construct: " << nodep->prettyTypeName()
                                                             << " in function " << __func__);
            return nullptr;
        }
    }
    AstVar* getCreateOutVarp(AstVar* invarp) {
        // Return the master __out for the specified input variable
        if (!invarp->user4p()) {
            AstVar* const newp = new AstVar{invarp->fileline(), VVarType::MODULETEMP,
                                            invarp->name() + "__out", invarp};
            UINFO(9, "       newout " << newp << endl);
            modAddStmtp(invarp, newp);
            invarp->user4p(newp);  // find outvar given invarp
        }
        return VN_AS(invarp->user4p(), Var);
    }
    AstVar* getCreateUnconnVarp(AstNode* fromp, AstNodeDType* dtypep) {
        AstVar* const newp = new AstVar{fromp->fileline(), VVarType::MODULETEMP,
                                        "__Vtriunconn" + cvtToStr(m_unique++), dtypep};
        UINFO(9, "       newunc " << newp << endl);
        modAddStmtp(newp, newp);
        return newp;
    }

    void mapInsertLhsVarRef(AstVarRef* nodep) {
        AstVar* const key = nodep->varp();
        const auto it = m_lhsmap.find(key);
        UINFO(9, "    mapInsertLhsVarRef " << nodep << endl);
        if (it == m_lhsmap.end()) {  // Not found
            RefStrengthVec* const refsp = new RefStrengthVec;
            refsp->push_back(RefStrength{nodep, m_currentStrength});
            m_lhsmap.emplace(key, refsp);
        } else {
            it->second->push_back(RefStrength{nodep, m_currentStrength});
        }
    }

    AstNodeExpr* newEnableDeposit(AstSel* selp, AstNodeExpr* enp) {
        // Form a "deposit" instruction for given enable, using existing select as a template.
        // Would be nicer if we made this a new AST type
        AstNodeExpr* const newp = new AstShiftL{
            selp->fileline(), new AstExtend{selp->fileline(), enp, selp->fromp()->width()},
            selp->lsbp()->cloneTreePure(false), selp->fromp()->width()};
        return newp;
    }

    void setPullDirection(AstVar* varp, AstPull* pullp) {
        const AstPull* const oldpullp = static_cast<AstPull*>(varp->user3p());
        if (!oldpullp) {
            varp->user3p(pullp);  // save off to indicate the pull direction
        } else {
            if (oldpullp->direction() != pullp->direction()) {
                pullp->v3warn(E_UNSUPPORTED, "Unsupported: Conflicting pull directions.\n"
                                                 << pullp->warnContextPrimary() << '\n'
                                                 << oldpullp->warnOther()
                                                 << "... Location of conflicting pull.\n"
                                                 << oldpullp->warnContextSecondary());
            }
        }
    }

    void checkUnhandled(AstNode* nodep) {
        // Check for unsupported tristate constructs. This is not a 100% check.
        // The best way would be to visit the tree again and find any user1p()
        // pointers that did not get picked up and expanded.
        if (m_alhs && nodep->user1p()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
        }
        // Ignore Var's because they end up adjacent to statements
        if ((nodep->op1p() && nodep->op1p()->user1p() && !VN_IS(nodep->op1p(), Var))
            || (nodep->op2p() && nodep->op2p()->user1p() && !VN_IS(nodep->op2p(), Var))
            || (nodep->op3p() && nodep->op3p()->user1p() && !VN_IS(nodep->op3p(), Var))
            || (nodep->op4p() && nodep->op4p()->user1p() && !VN_IS(nodep->op4p(), Var))) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported tristate construct: " << nodep->prettyTypeName());
        }
    }

    void insertTristates(AstNodeModule* nodep) {
        // Go through all the vars and find any that are outputs without drivers
        // or inouts without high-Z logic and put a 1'bz driver on them and add
        // them to the lhs map so they get expanded correctly.
        const TristateGraph::VarVec vars = m_tgraph.tristateVars();
        for (auto varp : vars) {
            if (m_tgraph.isTristate(varp)) {
                const auto it = m_lhsmap.find(varp);
                if (it == m_lhsmap.end()) {
                    // This variable is floating, set output enable to
                    // always be off on this assign
                    UINFO(8, "  Adding driver to var " << varp << endl);
                    AstConst* const constp = newAllZerosOrOnes(varp, false);
                    AstVarRef* const varrefp
                        = new AstVarRef{varp->fileline(), varp, VAccess::WRITE};
                    AstNode* const newp = new AstAssignW{varp->fileline(), varrefp, constp};
                    UINFO(9, "       newoev " << newp << endl);
                    varrefp->user1p(newAllZerosOrOnes(varp, false));
                    nodep->addStmtsp(newp);
                    mapInsertLhsVarRef(varrefp);  // insertTristates will convert
                    //                               // to a varref to the __out# variable
                }
            }
        }

        // Now go through the lhs driver map and generate the output
        // enable logic for any tristates.
        // Note there might not be any drivers.
        for (VarMap::iterator nextit, it = m_lhsmap.begin(); it != m_lhsmap.end(); it = nextit) {
            nextit = it;
            ++nextit;
            AstVar* const invarp = it->first;
            RefStrengthVec* refsp = it->second;
            // Figure out if this var needs tristate expanded.
            if (m_tgraph.isTristate(invarp)) {
                insertTristatesSignal(nodep, invarp, refsp);
            } else {
                UINFO(8, "  NO TRISTATE ON:" << invarp << endl);
            }
            // Delete the map and vector list now that we have expanded it.
            m_lhsmap.erase(invarp);
            VL_DO_DANGLING(delete refsp, refsp);
        }
    }

    void aggregateTriSameStrength(AstNodeModule* nodep, AstVar* const varp, AstVar* const envarp,
                                  RefStrengthVec::iterator beginStrength,
                                  RefStrengthVec::iterator endStrength) {
        // For each driver separate variables (normal and __en) are created and initialized with
        // values. In case of normal variable, the original expression is reused. Their values are
        // aggregated using | to form one expression, which are assigned to varp end envarp.
        AstNodeExpr* orp = nullptr;
        AstNodeExpr* enp = nullptr;

        for (auto it = beginStrength; it != endStrength; it++) {
            AstVarRef* refp = it->m_varrefp;
            const int w = varp->width();

            // create the new lhs driver for this var
            AstVar* const newLhsp = new AstVar{varp->fileline(), VVarType::MODULETEMP,
                                               varp->name() + "__out" + cvtToStr(m_unique),
                                               VFlagBitPacked{}, w};  // 2-state ok; sep enable
            UINFO(9, "       newout " << newLhsp << endl);
            nodep->addStmtsp(newLhsp);
            refp->varp(newLhsp);

            // create a new var for this drivers enable signal
            AstVar* const newEnLhsp = new AstVar{varp->fileline(), VVarType::MODULETEMP,
                                                 varp->name() + "__en" + cvtToStr(m_unique++),
                                                 VFlagBitPacked{}, w};  // 2-state ok
            UINFO(9, "       newenlhsp " << newEnLhsp << endl);
            nodep->addStmtsp(newEnLhsp);

            AstNode* const enLhspAssignp = new AstAssignW{
                refp->fileline(), new AstVarRef{refp->fileline(), newEnLhsp, VAccess::WRITE},
                getEnp(refp)};
            UINFO(9, "       newenlhspAssignp " << enLhspAssignp << endl);
            nodep->addStmtsp(enLhspAssignp);

            // now append this driver to the driver logic.
            AstNodeExpr* const ref1p = new AstVarRef{refp->fileline(), newLhsp, VAccess::READ};
            AstNodeExpr* const ref2p = new AstVarRef{refp->fileline(), newEnLhsp, VAccess::READ};
            AstNodeExpr* const andp = new AstAnd{refp->fileline(), ref1p, ref2p};

            // or this to the others
            orp = (!orp) ? andp : new AstOr{refp->fileline(), orp, andp};

            AstNodeExpr* const ref3p = new AstVarRef{refp->fileline(), newEnLhsp, VAccess::READ};
            enp = (!enp) ? ref3p : new AstOr{ref3p->fileline(), enp, ref3p};
        }
        AstNode* const assp = new AstAssignW{
            varp->fileline(), new AstVarRef{varp->fileline(), varp, VAccess::WRITE}, orp};
        UINFO(9, "       newassp " << assp << endl);
        nodep->addStmtsp(assp);

        AstNode* const enAssp = new AstAssignW{
            envarp->fileline(), new AstVarRef{envarp->fileline(), envarp, VAccess::WRITE}, enp};
        UINFO(9, "       newenassp " << enAssp << endl);
        nodep->addStmtsp(enAssp);
    }

    void insertTristatesSignal(AstNodeModule* nodep, AstVar* const invarp, RefStrengthVec* refsp) {
        UINFO(8, "  TRISTATE EXPANDING:" << invarp << endl);
        ++m_statTriSigs;
        m_tgraph.didProcess(invarp);

        // If the lhs var is a port, then we need to create ports for
        // the output (__out) and output enable (__en) signals. The
        // original port gets converted to an input. Don't tristate expand
        // if this is the top level so that we can force the final
        // tristate resolution at the top.
        AstVar* envarp = nullptr;
        AstVar* outvarp = nullptr;  // __out
        AstVar* lhsp = invarp;  // Variable to assign drive-value to (<in> or __out)
        if (!nodep->isTop() && invarp->isIO()) {
            // This var becomes an input
            invarp->varType2In();  // convert existing port to type input
            // Create an output port (__out)
            outvarp = getCreateOutVarp(invarp);
            outvarp->varType2Out();
            lhsp = outvarp;  // Must assign to __out, not to normal input signal
            UINFO(9, "     TRISTATE propagates up with " << lhsp << endl);
            // Create an output enable port (__en)
            // May already be created if have foo === 1'bz somewhere
            envarp = getCreateEnVarp(invarp);  // direction will be sen in visit(AstPin*)
            //
            outvarp->user1p(envarp);
            outvarp->user3p(invarp->user3p());  // AstPull* propagation
            if (invarp->user3p()) UINFO(9, "propagate pull to " << outvarp << endl);
        } else if (invarp->user1p()) {
            envarp = VN_AS(invarp->user1p(), Var);  // From CASEEQ, foo === 1'bz
        }

        AstNodeExpr* orp = nullptr;
        AstNodeExpr* enp = nullptr;
        const int w = lhsp->width();

        std::sort(refsp->begin(), refsp->end(),
                  [](RefStrength a, RefStrength b) { return a.m_strength > b.m_strength; });

        auto beginStrength = refsp->begin();
        while (beginStrength != refsp->end()) {
            auto endStrength = beginStrength + 1;
            while (endStrength != refsp->end()
                   && endStrength->m_strength == beginStrength->m_strength)
                endStrength++;

            FileLine* const fl = beginStrength->m_varrefp->fileline();
            const string strengthVarName = lhsp->name() + "__" + beginStrength->m_strength.ascii();

            // var__strength variable
            AstVar* varStrengthp = new AstVar{fl, VVarType::MODULETEMP, strengthVarName,
                                              VFlagBitPacked{}, w};  // 2-state ok; sep enable;
            UINFO(9, "       newstrength " << varStrengthp << endl);
            nodep->addStmtsp(varStrengthp);

            // var__strength__en variable
            AstVar* enVarStrengthp = new AstVar{fl, VVarType::MODULETEMP, strengthVarName + "__en",
                                                VFlagBitPacked{}, w};  // 2-state ok;
            UINFO(9, "       newenstrength " << enVarStrengthp << endl);
            nodep->addStmtsp(enVarStrengthp);

            aggregateTriSameStrength(nodep, varStrengthp, enVarStrengthp, beginStrength,
                                     endStrength);

            AstNodeExpr* exprCurrentStrengthp;
            if (enp) {
                // If weaker driver should be overwritten by a stronger, replace its value with z
                exprCurrentStrengthp
                    = new AstAnd{fl, new AstVarRef{fl, varStrengthp, VAccess::READ},
                                 new AstNot{fl, enp->cloneTreePure(false)}};
            } else {
                exprCurrentStrengthp = new AstVarRef{fl, varStrengthp, VAccess::READ};
            }
            orp = (!orp) ? exprCurrentStrengthp : new AstOr{fl, orp, exprCurrentStrengthp};

            AstNodeExpr* enVarStrengthRefp = new AstVarRef{fl, enVarStrengthp, VAccess::READ};

            enp = (!enp) ? enVarStrengthRefp : new AstOr{fl, enp, enVarStrengthRefp};

            beginStrength = endStrength;
        }

        if (!outvarp) {
            // This is the final pre-forced resolution of the tristate, so we apply
            // the pull direction to any undriven pins.
            const AstPull* const pullp = static_cast<AstPull*>(lhsp->user3p());
            bool pull1 = pullp && pullp->direction() == 1;  // Else default is down

            AstNodeExpr* undrivenp;
            if (envarp) {
                undrivenp = new AstNot{envarp->fileline(),
                                       new AstVarRef{envarp->fileline(), envarp, VAccess::READ}};
            } else {
                if (enp) {
                    undrivenp = new AstNot{enp->fileline(), enp};
                } else {
                    undrivenp = newAllZerosOrOnes(invarp, true);
                }
            }

            undrivenp
                = new AstAnd{invarp->fileline(), undrivenp, newAllZerosOrOnes(invarp, pull1)};
            orp = new AstOr{invarp->fileline(), orp, undrivenp};
        }

        if (envarp) {
            AstAssignW* const enAssp = new AstAssignW{
                enp->fileline(), new AstVarRef{envarp->fileline(), envarp, VAccess::WRITE}, enp};
            if (debug() >= 9) enAssp->dumpTree("-  enAssp: ");
            nodep->addStmtsp(enAssp);
        }

        // __out (child) or <in> (parent) = drive-value expression
        AstNode* const assp = new AstAssignW{
            lhsp->fileline(), new AstVarRef{lhsp->fileline(), lhsp, VAccess::WRITE}, orp};
        assp->user2(U2_BOTH);  // Don't process further; already resolved
        if (debug() >= 9) assp->dumpTree("-  lhsp-eqn: ");
        nodep->addStmtsp(assp);
    }

    bool isOnlyAssignmentIsToLhsVar(AstAssignW* const nodep) {
        if (AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            auto foundIt = m_assigns.find(varRefp->varp());
            if (foundIt != m_assigns.end()) {
                auto const& assignsToVar = foundIt->second;
                if (assignsToVar.size() == 1 && assignsToVar[0] == nodep) return true;
            }
        }
        return false;
    }

    void addToAssignmentList(AstAssignW* nodep) {
        if (AstVarRef* const varRefp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (varRefp->varp()->isNet()) {
                m_assigns[varRefp->varp()].push_back(nodep);
            } else if (nodep->strengthSpecp()) {
                if (!varRefp->varp()->isNet())
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: Signal strengths are unsupported "
                                                 "on the following variable type: "
                                                     << varRefp->varp()->varType());

                nodep->strengthSpecp()->unlinkFrBack()->deleteTree();
            }
        } else if (nodep->strengthSpecp()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Assignments with signal strength with LHS of type: "
                              << nodep->lhsp()->prettyTypeName());
        }
    }

    uint8_t getStrength(AstAssignW* const nodep, bool value) {
        if (AstStrengthSpec* const strengthSpec = nodep->strengthSpecp()) {
            return value ? strengthSpec->strength1() : strengthSpec->strength0();
        }
        return VStrength::STRONG;  // default strength is strong
    }

    bool assignmentOfValueOnAllBits(AstAssignW* const nodep, bool value) {
        if (AstConst* const constp = VN_CAST(nodep->rhsp(), Const)) {
            const V3Number num = constp->num();
            return value ? num.isEqAllOnes() : num.isEqZero();
        }
        return false;
    }

    AstAssignW* getStrongestAssignmentOfValue(const Assigns& assigns, bool value) {
        auto maxIt = std::max_element(
            assigns.begin(), assigns.end(), [&](AstAssignW* ap, AstAssignW* bp) {
                bool valuesOnRhsA = assignmentOfValueOnAllBits(ap, value);
                bool valuesOnRhsB = assignmentOfValueOnAllBits(bp, value);
                if (!valuesOnRhsA) return valuesOnRhsB;
                if (!valuesOnRhsB) return false;
                return getStrength(ap, value) < getStrength(bp, value);
            });
        // If not all assignments have const with all bits equal to value on the RHS,
        // std::max_element will return one of them anyway, so it has to be checked before
        // returning
        return assignmentOfValueOnAllBits(*maxIt, value) ? *maxIt : nullptr;
    }

    bool isAssignmentNotStrongerThanStrength(AstAssignW* assignp, uint8_t strength) {
        // If the value of the RHS is known and has all bits equal, only strength corresponding to
        // its value is taken into account. In opposite case, both strengths are compared.
        const uint8_t strength0 = getStrength(assignp, 0);
        const uint8_t strength1 = getStrength(assignp, 1);
        return (strength0 <= strength && strength1 <= strength)
               || (strength0 <= strength && assignmentOfValueOnAllBits(assignp, 0))
               || (strength1 <= strength && assignmentOfValueOnAllBits(assignp, 1));
    }

    void removeNotStrongerAssignments(Assigns& assigns, AstAssignW* strongestp,
                                      uint8_t greatestKnownStrength) {
        // Weaker assignments are these assignments that can't change the final value of the net.
        // They can be safely removed. Assignments of the same strength are also removed, because
        // duplicates aren't needed. One problem is with 2 assignments of different values and
        // equal strengths. It should result in assignment of x value, but these values aren't
        // supported now.
        auto removedIt = std::remove_if(assigns.begin(), assigns.end(), [&](AstAssignW* assignp) {
            if (assignp == strongestp) return false;
            if (isAssignmentNotStrongerThanStrength(assignp, greatestKnownStrength)) {
                // Vertices corresponding to nodes from removed assignment's subtree have to be
                // removed.
                m_tgraph.deleteVerticesFromSubtreeRecurse(assignp);
                VL_DO_DANGLING(pushDeletep(assignp->unlinkFrBack()), assignp);
                return true;
            }
            return false;
        });
        assigns.erase(removedIt, assigns.end());
    }

    void removeAssignmentsNotStrongerThanUniformConstant() {
        // If a stronger assignment of a constant with all bits equal to the same
        // value (0 or 1), is found, all weaker assignments can be safely removed.
        for (auto& varpAssigns : m_assigns) {
            Assigns& assigns = varpAssigns.second;
            if (assigns.size() > 1) {
                AstAssignW* const strongest0p = getStrongestAssignmentOfValue(assigns, 0);
                AstAssignW* const strongest1p = getStrongestAssignmentOfValue(assigns, 1);
                AstAssignW* strongestp = nullptr;
                uint8_t greatestKnownStrength = 0;
                const auto getIfStrongest
                    = [&](AstAssignW* const strongestCandidatep, bool value) {
                          if (!strongestCandidatep) return;
                          uint8_t strength = getStrength(strongestCandidatep, value);
                          if (strength >= greatestKnownStrength) {
                              greatestKnownStrength = strength;
                              strongestp = strongestCandidatep;
                          }
                      };
                getIfStrongest(strongest0p, 0);
                getIfStrongest(strongest1p, 1);

                if (strongestp) {
                    removeNotStrongerAssignments(assigns, strongestp, greatestKnownStrength);
                }
            }
        }
    }

    void removeAssignmentsNotStrongerThanNonTristate() {
        // Similar function as removeAssignmentsNotStrongerThanUniformConstant, but here the
        // assignments that have strength not stronger than the strongest assignment with
        // non-tristate RHS are removed. Strengths are compared according to their smaller values,
        // because the values of RHSs are unknown. (Assignments not stronger than strongest
        // constant are already removed.)
        for (auto& varpAssigns : m_assigns) {
            Assigns& assigns = varpAssigns.second;
            if (assigns.size() > 1) {
                auto maxIt = std::max_element(
                    assigns.begin(), assigns.end(), [&](AstAssignW* ap, AstAssignW* bp) {
                        if (m_tgraph.isTristate(ap)) return !m_tgraph.isTristate(bp);
                        if (m_tgraph.isTristate(bp)) return false;
                        const uint8_t minStrengthA
                            = std::min(getStrength(ap, 0), getStrength(ap, 1));
                        const uint8_t minStrengthB
                            = std::min(getStrength(bp, 0), getStrength(bp, 1));
                        return minStrengthA < minStrengthB;
                    });
                // If RHSs of all assignments are tristate, 1st element is returned, so it is
                // needed to check if it is non-tristate.
                AstAssignW* const strongestp = m_tgraph.isTristate(*maxIt) ? nullptr : *maxIt;
                if (strongestp) {
                    uint8_t greatestKnownStrength
                        = std::min(getStrength(strongestp, 0), getStrength(strongestp, 1));
                    removeNotStrongerAssignments(assigns, strongestp, greatestKnownStrength);
                }
            }
        }
    }

    // VISITORS
    void visit(AstConst* nodep) override {
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            if (!m_alhs && nodep->num().hasZ()) m_tgraph.setTristate(nodep);
        } else {
            // Detect any Z consts and convert them to 0's with an enable that is also 0.
            if (m_alhs && nodep->user1p()) {
                // A pin with 1'b0 or similar connection results in an assign with constant on LHS
                // due to the pinReconnectSimple call in visit AstPin.
                // We can ignore the output override by making a temporary
                AstVar* const varp = getCreateUnconnVarp(nodep, nodep->dtypep());
                AstNode* const newp = new AstVarRef{nodep->fileline(), varp, VAccess::WRITE};
                UINFO(9, " const->" << newp << endl);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (m_tgraph.isTristate(nodep)) {
                m_tgraph.didProcess(nodep);
                FileLine* const fl = nodep->fileline();
                AstConst* const enp = getNonZConstp(nodep);
                V3Number num1{nodep, nodep->width()};
                num1.opAnd(nodep->num(), enp->num());  // 01X->01X, Z->0
                AstConst* const newconstp = new AstConst{fl, num1};
                nodep->replaceWith(newconstp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                newconstp->user1p(enp);  // Propagate up constant with non-Z bits as 1
            }
        }
    }

    void visit(AstCond* nodep) override {
        if (m_graphing) {
            iterateChildren(nodep);
            if (m_alhs) {
                associateLogic(nodep, nodep->thenp());
                associateLogic(nodep, nodep->elsep());
            } else {
                associateLogic(nodep->thenp(), nodep);
                associateLogic(nodep->elsep(), nodep);
            }
        } else {
            if (m_alhs && nodep->user1p()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
                return;
            }
            iterateChildren(nodep);
            UINFO(9, dbgState() << nodep << endl);
            // Generate the new output enable signal for this cond if either
            // expression 1 or 2 have an output enable '__en' signal. If the
            // condition has an enable, not sure what to do, so generate an
            // error.
            AstNodeExpr* const condp = nodep->condp();
            if (condp->user1p()) {
                condp->v3warn(E_UNSUPPORTED, "Unsupported: don't know how to deal with "
                                             "tristate logic in the conditional expression");
            }
            AstNodeExpr* const thenp = nodep->thenp();
            AstNodeExpr* const elsep = nodep->elsep();
            if (thenp->user1p() || elsep->user1p()) {  // else no tristates
                m_tgraph.didProcess(nodep);
                AstNodeExpr* const en1p = getEnp(thenp);
                AstNodeExpr* const en2p = getEnp(elsep);
                // The output enable of a cond is a cond of the output enable of the
                // two expressions with the same conditional.
                AstNodeExpr* const enp
                    = new AstCond{nodep->fileline(), condp->cloneTree(false), en1p, en2p};
                UINFO(9, "       newcond " << enp << endl);
                nodep->user1p(enp);  // propagate up COND(lhsp->enable, rhsp->enable)
                thenp->user1p(nullptr);
                elsep->user1p(nullptr);
            }
        }
    }

    void visit(AstSel* nodep) override {
        if (m_graphing) {
            iterateChildren(nodep);
            if (m_alhs) {
                associateLogic(nodep, nodep->fromp());
            } else {
                associateLogic(nodep->fromp(), nodep);
            }
        } else {
            if (m_alhs) {
                UINFO(9, dbgState() << nodep << endl);
                if (nodep->user1p()) {
                    // Form a "deposit" instruction.  Would be nicer if we made this a new AST type
                    AstNodeExpr* const newp
                        = newEnableDeposit(nodep, VN_AS(nodep->user1p(), NodeExpr));
                    nodep->fromp()->user1p(newp);  // Push to varref (etc)
                    if (debug() >= 9) newp->dumpTree("-  assign-sel: ");
                    m_tgraph.didProcess(nodep);
                }
                iterateChildren(nodep);
            } else {
                iterateChildren(nodep);
                UINFO(9, dbgState() << nodep << endl);
                if (nodep->lsbp()->user1p()) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported RHS tristate construct: "
                                                     << nodep->prettyTypeName());
                }
                if (nodep->fromp()->user1p()) {  // SEL(VARREF, lsb)
                    AstNodeExpr* const en1p = getEnp(nodep->fromp());
                    AstNodeExpr* const enp
                        = new AstSel{nodep->fileline(), en1p, nodep->lsbp()->cloneTreePure(true),
                                     nodep->widthp()->cloneTree(true)};
                    UINFO(9, "       newsel " << enp << endl);
                    nodep->user1p(enp);  // propagate up SEL(fromp->enable, value)
                    m_tgraph.didProcess(nodep);
                }
            }
        }
    }

    void visit(AstConcat* nodep) override {
        if (m_graphing) {
            iterateChildren(nodep);
            if (m_alhs) {
                associateLogic(nodep, nodep->lhsp());
                associateLogic(nodep, nodep->rhsp());
            } else {
                associateLogic(nodep->lhsp(), nodep);
                associateLogic(nodep->rhsp(), nodep);
            }
        } else {
            if (m_alhs) {
                UINFO(9, dbgState() << nodep << endl);
                if (nodep->user1p()) {
                    // Each half of the concat gets a select of the enable expression
                    AstNodeExpr* const enp = VN_AS(nodep->user1p(), NodeExpr);
                    nodep->user1p(nullptr);
                    nodep->lhsp()->user1p(new AstSel{nodep->fileline(), enp->cloneTreePure(true),
                                                     nodep->rhsp()->width(),
                                                     nodep->lhsp()->width()});
                    nodep->rhsp()->user1p(
                        new AstSel{nodep->fileline(), enp, 0, nodep->rhsp()->width()});
                    m_tgraph.didProcess(nodep);
                }
                iterateChildren(nodep);
            } else {
                iterateChildren(nodep);
                UINFO(9, dbgState() << nodep << endl);
                // Generate the new output enable signal, just as a concat
                // identical to the data concat
                AstNodeExpr* const expr1p = nodep->lhsp();
                AstNodeExpr* const expr2p = nodep->rhsp();
                if (expr1p->user1p() || expr2p->user1p()) {  // else no tristates
                    m_tgraph.didProcess(nodep);
                    AstNodeExpr* const en1p = getEnp(expr1p);
                    AstNodeExpr* const en2p = getEnp(expr2p);
                    AstNodeExpr* const enp = new AstConcat{nodep->fileline(), en1p, en2p};
                    UINFO(9, "       newconc " << enp << endl);
                    nodep->user1p(enp);  // propagate up CONCAT(lhsp->enable, rhsp->enable)
                    expr1p->user1p(nullptr);
                    expr2p->user1p(nullptr);
                }
            }
        }
    }

    void visit(AstBufIf1* nodep) override {
        // For BufIf1, the enable is the LHS expression
        iterateChildren(nodep);
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            associateLogic(nodep->rhsp(), nodep);
            m_tgraph.setTristate(nodep);
        } else {
            if (debug() >= 9) nodep->backp()->dumpTree("-  bufif: ");
            if (m_alhs) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
                return;
            }
            m_tgraph.didProcess(nodep);
            AstNodeExpr* const expr1p = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const expr2p = nodep->rhsp()->unlinkFrBack();
            AstNodeExpr* enp;
            if (AstNodeExpr* const en2p = VN_AS(expr2p->user1p(), NodeExpr)) {
                enp = new AstAnd{nodep->fileline(), expr1p, en2p};
            } else {
                enp = expr1p;
            }
            expr1p->user1p(nullptr);
            expr2p->user1p(enp);  // Becomes new node
            // Don't need the BufIf any more, can just have the data direct
            nodep->replaceWith(expr2p);
            UINFO(9, "   bufif  datap=" << expr2p << endl);
            UINFO(9, "   bufif  enp=" << enp << endl);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    void visitAndOr(AstNodeBiop* nodep, bool isAnd) {
        iterateChildren(nodep);
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            associateLogic(nodep->lhsp(), nodep);
            associateLogic(nodep->rhsp(), nodep);
        } else {
            if (m_alhs && nodep->user1p()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
                return;
            }
            // ANDs and Z's have issues. Earlier optimizations convert
            // expressions like "(COND) ? 1'bz : 1'b0" to "COND & 1'bz". So we
            // have to define what is means to AND 1'bz with other
            // expressions. I don't think this is spec, but here I take the
            // approach that when one expression is 1, that the Z passes. This
            // makes the COND's work. It is probably better to not perform the
            // conditional optimization if the bits are Z.
            //
            // ORs have the same issues as ANDs. Earlier optimizations convert
            // expressions like "(COND) ? 1'bz : 1'b1" to "COND | 1'bz". So we
            // have to define what is means to OR 1'bz with other
            // expressions. Here I take the approach that when one expression
            // is 0, that is passes the other.
            AstNodeExpr* const expr1p = nodep->lhsp();
            AstNodeExpr* const expr2p = nodep->rhsp();
            if (!expr1p->user1p() && !expr2p->user1p()) {
                return;  // no tristates in either expression, so nothing to do
            }
            m_tgraph.didProcess(nodep);
            AstNodeExpr* const en1p = getEnp(expr1p);
            AstNodeExpr* const en2p = getEnp(expr2p);
            AstNodeExpr* subexpr1p = expr1p->cloneTreePure(false);
            AstNodeExpr* subexpr2p = expr2p->cloneTreePure(false);
            if (isAnd) {
                subexpr1p = new AstNot{nodep->fileline(), subexpr1p};
                subexpr2p = new AstNot{nodep->fileline(), subexpr2p};
            }
            // calc new output enable
            AstNodeExpr* const enp = new AstOr{
                nodep->fileline(), new AstAnd{nodep->fileline(), en1p, en2p},
                new AstOr{nodep->fileline(),
                          new AstAnd{nodep->fileline(), en1p->cloneTree(false), subexpr1p},
                          new AstAnd{nodep->fileline(), en2p->cloneTree(false), subexpr2p}}};
            UINFO(9, "       neweqn " << enp << endl);
            nodep->user1p(enp);
            expr1p->user1p(nullptr);
            expr2p->user1p(nullptr);
        }
    }
    void visit(AstAnd* nodep) override { visitAndOr(nodep, true); }
    void visit(AstOr* nodep) override { visitAndOr(nodep, false); }

    void visitAssign(AstNodeAssign* nodep) {
        VL_RESTORER(m_alhs);
        VL_RESTORER(m_currentStrength);
        if (m_graphing) {
            if (AstAssignW* assignWp = VN_CAST(nodep, AssignW)) addToAssignmentList(assignWp);

            if (nodep->user2() & U2_GRAPHING) return;
            VL_RESTORER(m_logicp);
            m_logicp = nodep;
            nodep->user2(U2_GRAPHING);
            iterateAndNextNull(nodep->rhsp());
            m_alhs = true;
            iterateAndNextNull(nodep->lhsp());
            m_alhs = false;
            associateLogic(nodep->rhsp(), nodep);
            associateLogic(nodep, nodep->lhsp());
        } else {
            if (nodep->user2() & U2_NONGRAPH) {
                return;  // Iterated here, or created assignment to ignore
            }
            nodep->user2(U2_NONGRAPH);
            iterateAndNextNull(nodep->rhsp());
            UINFO(9, dbgState() << nodep << endl);
            if (debug() >= 9) nodep->dumpTree("-  assign: ");
            // if the rhsp of this assign statement has an output enable driver,
            // then propagate the corresponding output enable assign statement.
            // down the lvalue tree by recursion for eventual attachment to
            // the appropriate output signal's VarRef.
            if (nodep->rhsp()->user1p()) {
                nodep->lhsp()->user1p(nodep->rhsp()->user1p());
                nodep->rhsp()->user1p(nullptr);
                UINFO(9, "   enp<-rhs " << nodep->lhsp()->user1p() << endl);
                m_tgraph.didProcess(nodep);
            }
            m_alhs = true;  // And user1p() will indicate tristate equation, if any
            if (AstAssignW* const assignWp = VN_CAST(nodep, AssignW)) {
                if (AstStrengthSpec* const specp = assignWp->strengthSpecp()) {
                    if (specp->strength0() != specp->strength1()) {
                        // Unequal strengths are not a problem if the assignment is the only
                        // assignment to its variable. Unfortunately, m_assigns map stores only
                        // assignments to var. Selects are not inserted, so they may be handled
                        // improperly
                        if (!isOnlyAssignmentIsToLhsVar(assignWp)) {
                            assignWp->v3warn(
                                E_UNSUPPORTED,
                                "Unsupported: Unable to resolve unequal strength specifier");
                        }
                    } else {
                        m_currentStrength = specp->strength0();
                    }
                }
            }
            iterateAndNextNull(nodep->lhsp());
        }
    }
    void visit(AstAssignW* nodep) override { visitAssign(nodep); }
    void visit(AstAssign* nodep) override { visitAssign(nodep); }

    void visitCaseEq(AstNodeBiop* nodep, bool neq) {
        if (m_graphing) {
            iterateChildren(nodep);
        } else {
            checkUnhandled(nodep);
            // Unsupported: A === 3'b000 should compare with the enables, but we don't do
            // so at present, we only compare if there is a z in the equation.
            // Otherwise we'd need to attach an enable to every signal, then optimize them
            // away later when we determine the signal has no tristate
            iterateChildren(nodep);
            UINFO(9, dbgState() << nodep << endl);
            // Constification always moves const to LHS
            AstConst* const constp = VN_CAST(nodep->lhsp(), Const);
            if (constp && constp->user1p()) {
                // 3'b1z0 -> ((3'b101 == in__en) && (3'b100 == in))
                AstNodeExpr* const rhsp = nodep->rhsp();
                rhsp->unlinkFrBack();
                FileLine* const fl = nodep->fileline();
                AstNodeExpr* enRhsp;
                if (rhsp->user1p()) {
                    enRhsp = VN_AS(rhsp->user1p(), NodeExpr);
                    rhsp->user1p(nullptr);
                } else {
                    enRhsp = getEnExprBasedOnOriginalp(rhsp);
                }
                const V3Number oneIfEn
                    = VN_AS(constp->user1p(), Const)
                          ->num();  // visit(AstConst) already split into en/ones
                const V3Number& oneIfEnOne = constp->num();
                AstNodeExpr* newp
                    = new AstLogAnd{fl, new AstEq{fl, new AstConst{fl, oneIfEn}, enRhsp},
                                    // Keep the caseeq if there are X's present
                                    new AstEqCase{fl, new AstConst{fl, oneIfEnOne}, rhsp}};
                if (neq) newp = new AstLogNot{fl, newp};
                UINFO(9, "       newceq " << newp << endl);
                if (debug() >= 9) nodep->dumpTree("-  caseeq-old: ");
                if (debug() >= 9) newp->dumpTree("-  caseeq-new: ");
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (constp && nodep->rhsp()->user1p()) {
                FileLine* const fl = nodep->fileline();
                constp->unlinkFrBack();
                AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
                AstNodeExpr* newp = new AstLogAnd{fl,
                                                  new AstEq{fl, newAllZerosOrOnes(constp, false),
                                                            VN_AS(rhsp->user1p(), NodeExpr)},
                                                  // Keep the caseeq if there are X's present
                                                  new AstEqCase{fl, constp, rhsp}};
                if (neq) newp = new AstLogNot{fl, newp};
                rhsp->user1p(nullptr);
                UINFO(9, "       newceq " << newp << endl);
                if (debug() >= 9) nodep->dumpTree("-  caseeq-old: ");
                if (debug() >= 9) newp->dumpTree("-  caseeq-new: ");
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else {
                checkUnhandled(nodep);
            }
        }
    }
    void visitEqNeqWild(AstNodeBiop* nodep) {
        if (!VN_IS(nodep->rhsp(), Const)) {
            nodep->v3warn(E_UNSUPPORTED,  // Says spac.
                          "Unsupported: RHS of ==? or !=? must be constant to be synthesizable");
            // rhs we want to keep X/Z intact, so otherwise ignore
        }
        iterateAndNextNull(nodep->lhsp());
        if (nodep->lhsp()->user1p()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
            return;
        }
    }
    void visit(AstEqCase* nodep) override { visitCaseEq(nodep, false); }
    void visit(AstNeqCase* nodep) override { visitCaseEq(nodep, true); }
    void visit(AstEqWild* nodep) override { visitEqNeqWild(nodep); }
    void visit(AstNeqWild* nodep) override { visitEqNeqWild(nodep); }

    void visit(AstCountBits* nodep) override {
        std::array<bool, 3> dropop;
        dropop[0] = VN_IS(nodep->rhsp(), Const) && VN_AS(nodep->rhsp(), Const)->num().isAnyZ();
        dropop[1] = VN_IS(nodep->thsp(), Const) && VN_AS(nodep->thsp(), Const)->num().isAnyZ();
        dropop[2] = VN_IS(nodep->fhsp(), Const) && VN_AS(nodep->fhsp(), Const)->num().isAnyZ();
        UINFO(4, " COUNTBITS(" << dropop[0] << dropop[1] << dropop[2] << " " << nodep << endl);
        const AstVarRef* const varrefp = VN_AS(nodep->lhsp(), VarRef);  // Input variable
        if (m_graphing) {
            iterateAndNextNull(nodep->lhsp());
            if (!dropop[0]) iterateAndNextNull(nodep->rhsp());
            if (!dropop[1]) iterateAndNextNull(nodep->thsp());
            if (!dropop[2]) iterateAndNextNull(nodep->fhsp());
        } else {
            AstNodeExpr* nonXp = nullptr;
            if (!dropop[0]) {
                nonXp = nodep->rhsp();
            } else if (!dropop[1]) {
                nonXp = nodep->thsp();
            } else if (!dropop[2]) {
                nonXp = nodep->fhsp();
            }
            // Replace 'z with non-Z
            if (dropop[0] || dropop[1] || dropop[2]) {
                // Unsupported: A $countones('0) should compare with the enables, but we don't
                // do so at present, we only compare if there is a z in the equation. Otherwise
                // we'd need to attach an enable to every signal, then optimize them away later
                // when we determine the signal has no tristate
                if (!VN_IS(nodep->lhsp(), VarRef)) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported LHS tristate construct: "
                                                     << nodep->prettyTypeName());
                    return;
                }
                AstVar* const envarp = getCreateEnVarp(varrefp->varp());
                // If any drops, we need to add in the count of Zs (from __en)
                UINFO(4, " COUNTBITS('z)-> " << nodep << endl);
                VNRelinker relinkHandle;
                nodep->unlinkFrBack(&relinkHandle);
                AstNodeExpr* newp = new AstCountOnes{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), envarp, VAccess::READ}};
                if (nonXp) {  // Need to still count '0 or '1 or 'x's
                    if (dropop[0]) {
                        nodep->rhsp()->unlinkFrBack()->deleteTree();
                        nodep->rhsp(nonXp->cloneTreePure(true));
                    }
                    if (dropop[1]) {
                        nodep->thsp()->unlinkFrBack()->deleteTree();
                        nodep->thsp(nonXp->cloneTreePure(true));
                    }
                    if (dropop[2]) {
                        nodep->fhsp()->unlinkFrBack()->deleteTree();
                        nodep->fhsp(nonXp->cloneTreePure(true));
                    }
                    newp = new AstAdd{nodep->fileline(), nodep, newp};
                }
                if (debug() >= 9) newp->dumpTree("-  countout: ");
                relinkHandle.relink(newp);
            }
            iterateChildren(nodep);
        }
    }
    void visit(AstPull* nodep) override {
        UINFO(9, dbgState() << nodep << endl);
        AstVarRef* varrefp = nullptr;
        if (VN_IS(nodep->lhsp(), VarRef)) {
            varrefp = VN_AS(nodep->lhsp(), VarRef);
        } else if (VN_IS(nodep->lhsp(), Sel)
                   && VN_IS(VN_AS(nodep->lhsp(), Sel)->fromp(), VarRef)) {
            varrefp = VN_AS(VN_AS(nodep->lhsp(), Sel)->fromp(), VarRef);
        }
        if (!varrefp) {
            if (debug() >= 4) nodep->dumpTree("-  ");
            nodep->v3warn(E_UNSUPPORTED, "Unsupported pullup/down (weak driver) construct.");
        } else {
            if (m_graphing) {
                VL_RESTORER(m_logicp);
                m_logicp = nodep;
                varrefp->access(VAccess::WRITE);
                m_tgraph.setTristate(nodep);
                associateLogic(nodep, varrefp->varp());
            } else {
                // Replace any pullup/pulldowns with assignw logic and set the
                // direction of the pull in the user3() data on the var.  Given
                // the complexity of merging tristate drivers at any level, the
                // current limitation of this implementation is that a pullup/down
                // gets applied to all bits of a bus and a bus cannot have drivers
                // in opposite directions on individual pins.
                varrefp->access(VAccess::WRITE);
                m_tgraph.didProcess(nodep);
                m_tgraph.didProcess(varrefp->varp());
                setPullDirection(varrefp->varp(), nodep);
            }
        }
        if (!m_graphing) {
            nodep->unlinkFrBack();
            VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Node must persist as user3p points to it
        }
    }

    void iteratePinGuts(AstPin* nodep) {
        if (m_graphing) {
            VL_RESTORER(m_logicp);
            m_logicp = nodep;
            if (nodep->exprp()) {
                associateLogic(nodep->exprp(), nodep);
                associateLogic(nodep, nodep->exprp());
            }
            iterateChildren(nodep);
        } else {
            // All heavy lifting completed in graph visitor.
            if (nodep->exprp()) m_tgraph.didProcess(nodep);
            iterateChildren(nodep);
        }
    }

    // .tri(SEL(trisig,x)) becomes
    //   INPUT:   -> (VARREF(trisig__pinin)),
    //               trisig__pinin = SEL(trisig,x)       // via pinReconnectSimple
    //   OUTPUT:  -> (VARREF(trisig__pinout))
    //               SEL(trisig,x) = trisig__pinout
    //                                  ^-- ->user1p() == trisig__pinen
    //   ENABLE:  -> (VARREF(trisig__pinen)
    // Added complication is the signal may be an output/inout or just
    // input with tie off (or not) up top
    //     PIN  PORT    NEW PORTS AND CONNECTIONS
    //     N/C  input   in(from-resolver), __en(to-resolver-only), __out(to-resolver-only)
    //     N/C  inout   Spec says illegal
    //     N/C  output  Unsupported; Illegal?
    //     wire input   in(from-resolver-with-wire-value), __en(from-resolver-wire),
    //                     __out(to-resolver-only)
    //     wire inout   in, __en, __out
    //     wire output  in, __en, __out
    //     const input  in(from-resolver-with-const-value), __en(from-resolver-const),
    //                     __out(to-resolver-only)
    //     const inout  Spec says illegal
    //     const output Unsupported; Illegal?
    void visit(AstPin* nodep) override {
        if (m_graphing) {
            if (nodep->user2() & U2_GRAPHING) return;  // This pin is already expanded
            nodep->user2(U2_GRAPHING);
            // Find child module's new variables.
            AstVar* const enModVarp = static_cast<AstVar*>(nodep->modVarp()->user1p());
            if (!enModVarp) {
                // May have an output only that later connects to a tristate, so simplify now.
                V3Inst::pinReconnectSimple(nodep, m_cellp, false);
                iteratePinGuts(nodep);
                return;  // No __en signals on this pin
            }
            // Tristate exists:
            UINFO(9, dbgState() << nodep << endl);
            if (debug() >= 9) nodep->dumpTree("-  pin-pre: ");

            // Empty/in-only; need Z to propagate
            const bool inDeclProcessing = (nodep->exprp()
                                           && nodep->modVarp()->direction() == VDirection::INPUT
                                           // Need to consider the original state
                                           // instead of current state as we converted
                                           // tristates to inputs, which do not want
                                           // to have this.
                                           && !nodep->modVarp()->declDirection().isWritable());
            if (!nodep->exprp()) {  // No-connect; covert to empty connection
                UINFO(5, "Unconnected pin terminate " << nodep << endl);
                AstVar* const ucVarp = getCreateUnconnVarp(nodep, nodep->modVarp()->dtypep());
                nodep->exprp(new AstVarRef{nodep->fileline(), ucVarp,
                                           // We converted, so use declaration output state
                                           nodep->modVarp()->declDirection().isWritable()
                                               ? VAccess::WRITE
                                               : VAccess::READ});
                m_tgraph.setTristate(ucVarp);
                // We don't need a driver on the wire; the lack of one will default to tristate
            } else if (inDeclProcessing) {  // Not an input that was a converted tristate
                // Input only may have driver in underneath module which would stomp
                // the input value.  So make a temporary connection.
                const AstAssignW* const reAssignp
                    = V3Inst::pinReconnectSimple(nodep, m_cellp, true, true);
                UINFO(5, "Input pin buffering: " << reAssignp << endl);
                m_tgraph.setTristate(reAssignp->lhsp());
            }

            // pinReconnectSimple needs to presume input or output behavior; we need both
            // Therefore, create the enable, output and separate input pin,
            // then pinReconnectSimple all
            // Create the output enable pin, connect to new signal
            AstNodeExpr* enrefp;
            {
                AstVar* const enVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP,
                                                  nodep->name() + "__en" + cvtToStr(m_unique++),
                                                  VFlagBitPacked{}, enModVarp->width()};
                if (inDeclProcessing) {  // __en(from-resolver-const) or __en(from-resolver-wire)
                    enModVarp->varType2In();
                } else {
                    enModVarp->varType2Out();
                }
                UINFO(9, "       newenv " << enVarp << endl);
                AstPin* const enpinp
                    = new AstPin{nodep->fileline(), nodep->pinNum(),
                                 enModVarp->name(),  // should be {var}"__en"
                                 new AstVarRef{nodep->fileline(), enVarp, VAccess::WRITE}};
                enpinp->modVarp(enModVarp);
                UINFO(9, "       newpin " << enpinp << endl);
                enpinp->user2(U2_BOTH);  // don't iterate the pin later
                nodep->addNextHere(enpinp);
                m_modp->addStmtsp(enVarp);
                enrefp = new AstVarRef{nodep->fileline(), enVarp, VAccess::READ};
                UINFO(9, "       newvrf " << enrefp << endl);
                if (debug() >= 9) enpinp->dumpTree("-  pin-ena: ");
            }
            // Create new output pin
            const AstAssignW* outAssignp = nullptr;  // If reconnected, the related assignment
            AstPin* outpinp = nullptr;
            AstVar* const outModVarp = static_cast<AstVar*>(nodep->modVarp()->user4p());
            if (!outModVarp) {
                // At top, no need for __out as might be input only. Otherwise resolvable.
                if (!m_modp->isTop()) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: tristate in top-level IO: "
                                                     << nodep->prettyNameQ());
                }
            } else {
                AstNodeExpr* const outexprp = VN_AS(nodep->exprp(), NodeExpr)
                                                  ->cloneTreePure(false);  // Note has lvalue() set
                outpinp = new AstPin{nodep->fileline(), nodep->pinNum(),
                                     outModVarp->name(),  // should be {var}"__out"
                                     outexprp};
                outpinp->modVarp(outModVarp);
                UINFO(9, "       newpin " << outpinp << endl);
                outpinp->user2(U2_BOTH);  // don't iterate the pin later
                nodep->addNextHere(outpinp);
                // Simplify
                if (inDeclProcessing) {  // Not an input that was a converted tristate
                    // The pin is an input, but we need an output
                    // The if() above is needed because the Visitor is
                    // simple, it will flip ArraySel's and such, but if the
                    // pin is an input the earlier reconnectSimple made it
                    // a VarRef without any ArraySel, etc
                    TristatePinVisitor{outexprp, m_tgraph, true};
                }
                if (debug() >= 9) outpinp->dumpTree("-  pin-opr: ");
                outAssignp = V3Inst::pinReconnectSimple(outpinp, m_cellp,
                                                        true);  // Note may change outpinp->exprp()
                if (debug() >= 9) outpinp->dumpTree("-  pin-out: ");
                if (debug() >= 9 && outAssignp) outAssignp->dumpTree("-  pin-out: ");
                // Must still iterate the outAssignp, as need to build output equation
            }

            // Existing pin becomes an input, and we mark each resulting signal as tristate
            const TristatePinVisitor visitor{nodep->exprp(), m_tgraph, false};
            const AstNode* const inAssignp = V3Inst::pinReconnectSimple(
                nodep, m_cellp, true);  // Note may change nodep->exprp()
            if (debug() >= 9) nodep->dumpTree("-  pin-in:: ");
            if (debug() >= 9 && inAssignp) inAssignp->dumpTree("-  pin-as:: ");

            // Connect enable to output signal
            AstVarRef* exprrefp;  // Tristate variable that the Pin's expression refers to
            if (!outAssignp) {
                if (!outpinp) {
                    exprrefp = nullptr;  // Primary input only
                } else {
                    // pinReconnect should have converted this
                    exprrefp = VN_CAST(outpinp->exprp(), VarRef);
                    if (!exprrefp) {
                        nodep->v3warn(E_UNSUPPORTED, "Unsupported tristate port expression: "
                                                         << nodep->exprp()->prettyTypeName());
                    }
                }
            } else {
                // pinReconnect should have converted this
                exprrefp = VN_CAST(outAssignp->rhsp(),
                                   VarRef);  // This should be the same var as the output pin
                if (!exprrefp) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported tristate port expression: "
                                                     << nodep->exprp()->prettyTypeName());
                }
            }
            if (exprrefp) {
                UINFO(9, "outref " << exprrefp << endl);
                // Mark as now tristated; iteration will pick it up from there
                exprrefp->user1p(enrefp);
                if (!outAssignp) {
                    mapInsertLhsVarRef(exprrefp);  // insertTristates will convert
                    //                     // to a varref to the __out# variable
                }  // else the assignment deals with the connection
            }

            // Propagate any pullups/pulldowns upwards if necessary
            if (exprrefp) {
                if (AstPull* const pullp = static_cast<AstPull*>(nodep->modVarp()->user3p())) {
                    UINFO(9, "propagate pull on " << exprrefp << endl);
                    setPullDirection(exprrefp->varp(), pullp);
                }
            }
            // Don't need to visit the created assigns, as it was added at
            // the end of the next links and normal iterateChild recursion
            // will come back to them eventually.
            // Mark the original signal as tristated
            iteratePinGuts(nodep);
        }
        // Not graph building
        else {
            if (nodep->user2() & U2_NONGRAPH) return;  // This pin is already expanded
            nodep->user2(U2_NONGRAPH);
            UINFO(9, " " << nodep << endl);
            iteratePinGuts(nodep);
        }
    }

    void visit(AstVarRef* nodep) override {
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            if (nodep->access().isWriteOrRW()) associateLogic(nodep, nodep->varp());
            if (nodep->access().isReadOrRW()) associateLogic(nodep->varp(), nodep);
        } else {
            if (nodep->user2() & U2_NONGRAPH) return;  // Processed
            nodep->user2(U2_NONGRAPH);
            // Detect all var lhs drivers and adds them to the
            // VarMap so that after the walk through the module we can expand
            // any tristate logic on the driver.
            if (nodep->access().isWriteOrRW() && m_tgraph.isTristate(nodep->varp())) {
                UINFO(9, "     Ref-to-lvalue " << nodep << endl);
                UASSERT_OBJ(!nodep->access().isRW(), nodep, "Tristate unexpected on R/W access");
                m_tgraph.didProcess(nodep);
                mapInsertLhsVarRef(nodep);
            } else if (nodep->access().isReadOnly()
                       // Not already processed, nor varref from visit(AstPin) creation
                       && !nodep->user1p()
                       // Reference to another tristate variable
                       && m_tgraph.isTristate(nodep->varp())
                       // and in a position where it feeds upstream to another tristate
                       && m_tgraph.feedsTri(nodep)) {
                // Then propagate the enable from the original variable
                UINFO(9, "     Ref-to-tri " << nodep << endl);
                AstVar* const enVarp = getCreateEnVarp(nodep->varp());
                nodep->user1p(new AstVarRef{nodep->fileline(), enVarp, VAccess::READ});
            }
            if (m_alhs) {}  // NOP; user1() already passed down from assignment
        }
    }

    void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            // If tri0/1 force a pullup
            if (nodep->user2() & U2_GRAPHING) return;  // Already processed
            nodep->user2(U2_GRAPHING);
            if (nodep->isPulldown() || nodep->isPullup()) {
                AstNode* const newp = new AstPull{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), nodep, VAccess::WRITE},
                    nodep->isPullup()};
                UINFO(9, "       newpul " << newp << endl);
                nodep->addNextHere(newp);
                // We'll iterate on the new AstPull later
            }
            if (nodep->isInoutish()
                //|| varp->isOutput()
                // Note unconnected output only changes behavior vs. previous
                // versions and causes outputs that don't come from anywhere to
                // possibly create connection errors.
                // One example of problems is this:  "output z;  task t; z <= {something}; endtask"
            ) {
                UINFO(9, "  setTristate-inout " << nodep << endl);
                m_tgraph.setTristate(nodep);
            }
        } else {  // !graphing
            if (m_tgraph.isTristate(nodep)) {
                // nodep->isPulldown() || nodep->isPullup() handled in TristateGraphVisitor
                m_tgraph.didProcess(nodep);
            }
        }
    }

    void visit(AstNodeModule* nodep) override {
        UINFO(8, nodep << endl);
        VL_RESTORER(m_modp);
        VL_RESTORER(m_graphing);
        VL_RESTORER(m_unique);
        VL_RESTORER(m_lhsmap);
        VL_RESTORER(m_assigns);
        // Not preserved, needs pointer instead: TristateGraph origTgraph = m_tgraph;
        UASSERT_OBJ(m_tgraph.empty(), nodep, "Unsupported: NodeModule under NodeModule");
        {
            // Clear state
            m_graphing = false;
            m_tgraph.clear();
            m_unique = 0;
            m_logicp = nullptr;
            m_lhsmap.clear();
            m_assigns.clear();
            m_modp = nodep;
            // Walk the graph, finding all variables and tristate constructs
            {
                m_graphing = true;
                iterateChildren(nodep);
                m_graphing = false;
            }
            // Remove all assignments not stronger than the strongest uniform constant
            removeAssignmentsNotStrongerThanUniformConstant();
            // Use graph to find tristate signals
            m_tgraph.graphWalk(nodep);

            // Remove all assignments not stronger than the strongest non-tristate RHS
            removeAssignmentsNotStrongerThanNonTristate();

            // Build the LHS drivers map for this module
            iterateChildren(nodep);
            // Insert new logic for all tristates
            insertTristates(nodep);
        }
        m_tgraph.clear();  // Recursion not supported
    }

    void visit(AstClass* nodep) override {
        // don't deal with classes
    }
    void visit(AstNodeFTask* nodep) override {
        // don't deal with functions
    }

    void visit(AstCaseItem* nodep) override {
        // don't deal with casez compare '???? values
        iterateAndNextNull(nodep->stmtsp());
    }

    void visit(AstCell* nodep) override {
        VL_RESTORER(m_cellp);
        m_cellp = nodep;
        m_alhs = false;
        iterateChildren(nodep);
    }

    void visit(AstNetlist* nodep) override { iterateChildrenBackwardsConst(nodep); }

    // Default: Just iterate
    void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        checkUnhandled(nodep);
    }

public:
    // CONSTRUCTORS
    explicit TristateVisitor(AstNode* nodep) {
        m_tgraph.clear();
        iterate(nodep);
    }
    ~TristateVisitor() override {
        V3Stats::addStat("Tristate, Tristate resolved nets", m_statTriSigs);
    }
};

//######################################################################
// Tristate class functions

void V3Tristate::tristateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TristateVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tristate", 0, dumpTreeLevel() >= 3);
}
