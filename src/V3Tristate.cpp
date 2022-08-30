// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Deals with tristate logic
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
//*************************************************************************

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

//######################################################################

class TristateBaseVisitor VL_NOT_FINAL : public VNVisitor {
public:
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Graph support classes

class TristateVertex final : public V3GraphVertex {
    AstNode* const m_nodep;
    bool m_isTristate = false;  // Logic indicates a tristate
    bool m_feedsTri = false;  // Propagates to a tristate node (on RHS)
    bool m_processed = false;  // Tristating was cleaned up
public:
    TristateVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    virtual ~TristateVertex() override = default;
    // ACCESSORS
    AstNode* nodep() const { return m_nodep; }
    const AstVar* varp() const { return VN_CAST(nodep(), Var); }
    virtual string name() const override {
        return ((isTristate() ? "tri\\n"
                 : feedsTri() ? "feed\\n"
                              : "-\\n")
                + (nodep()->prettyTypeName() + " " + cvtToHex(nodep())));
    }
    virtual string dotColor() const override {
        return (varp() ? (isTristate() ? "darkblue"
                          : feedsTri() ? "blue"
                                       : "lightblue")
                       : (isTristate() ? "darkgreen"
                          : feedsTri() ? "green"
                                       : "lightgreen"));
    }
    virtual FileLine* fileline() const override { return nodep()->fileline(); }
    void isTristate(bool flag) { m_isTristate = flag; }
    bool isTristate() const { return m_isTristate; }
    void feedsTri(bool flag) { m_feedsTri = flag; }
    bool feedsTri() const { return m_feedsTri; }
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
    VL_DEBUG_FUNC;  // Declare debug()

    TristateVertex* makeVertex(AstNode* nodep) {
        TristateVertex* vertexp = reinterpret_cast<TristateVertex*>(nodep->user5p());
        if (!vertexp) {
            UINFO(6, "         New vertex " << nodep << endl);
            vertexp = new TristateVertex(&m_graph, nodep);
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
                TristateVertex* const vvertexp = dynamic_cast<TristateVertex*>(edgep->top());
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
                TristateVertex* const vvertexp = dynamic_cast<TristateVertex*>(edgep->fromp());
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
                TristateVertex* const vvertexp = dynamic_cast<TristateVertex*>(edgep->fromp());
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
        // if (debug() >= 9) m_graph.dumpDotFilePrefixed("tri_pre__" + nodep->name());
        UINFO(9, " Walking " << nodep << endl);
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            graphWalkRecurseFwd(static_cast<TristateVertex*>(itp), 0);
        }
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            graphWalkRecurseBack(static_cast<TristateVertex*>(itp), 0);
        }
        if (debug() >= 9) m_graph.dumpDotFilePrefixed("tri_pos__" + nodep->name());
    }
    void associate(AstNode* fromp, AstNode* top) {
        new V3GraphEdge(&m_graph, makeVertex(fromp), makeVertex(top), 1);
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
    virtual void visit(AstVarRef* nodep) override {
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
    virtual void visit(AstArraySel* nodep) override {
        // Doesn't work because we'd set lvalue on the array index's var
        UASSERT_OBJ(!m_lvalue, nodep, "ArraySel conversion to output, under tristate node");
        iterateChildren(nodep);
    }
    virtual void visit(AstSliceSel* nodep) override {
        // Doesn't work because we'd set lvalue on the array index's var
        UASSERT_OBJ(!m_lvalue, nodep, "SliceSel conversion to output, under tristate node");
        iterateChildren(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    TristatePinVisitor(AstNode* nodep, TristateGraph& tgraph, bool lvalue)
        : m_tgraph(tgraph)  // Need () or GCC 4.8 false warning
        , m_lvalue{lvalue} {
        iterate(nodep);
    }
    virtual ~TristatePinVisitor() override = default;
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
    using RefVec = std::vector<AstVarRef*>;
    using VarMap = std::unordered_map<AstVar*, RefVec*>;
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
    int m_unique = 0;
    bool m_alhs = false;  // On LHS of assignment
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
            m_modp->addStmtp(newp);
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
    AstNode* getEnp(AstNode* nodep) {
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
        return nodep->user1p();
    }
    AstVar* getCreateEnVarp(AstVar* invarp) {
        // Return the master __en for the specified input variable
        if (!invarp->user1p()) {
            AstVar* const newp = new AstVar(invarp->fileline(), VVarType::MODULETEMP,
                                            invarp->name() + "__en", invarp);
            UINFO(9, "       newenv " << newp << endl);
            modAddStmtp(invarp, newp);
            invarp->user1p(newp);  // find envar given invarp
        }
        return VN_AS(invarp->user1p(), Var);
    }
    AstVar* getCreateOutVarp(AstVar* invarp) {
        // Return the master __out for the specified input variable
        if (!invarp->user4p()) {
            AstVar* const newp = new AstVar(invarp->fileline(), VVarType::MODULETEMP,
                                            invarp->name() + "__out", invarp);
            UINFO(9, "       newout " << newp << endl);
            modAddStmtp(invarp, newp);
            invarp->user4p(newp);  // find outvar given invarp
        }
        return VN_AS(invarp->user4p(), Var);
    }
    AstVar* getCreateUnconnVarp(AstNode* fromp, AstNodeDType* dtypep) {
        AstVar* const newp = new AstVar(fromp->fileline(), VVarType::MODULETEMP,
                                        "__Vtriunconn" + cvtToStr(m_unique++), dtypep);
        UINFO(9, "       newunc " << newp << endl);
        modAddStmtp(newp, newp);
        return newp;
    }

    void mapInsertLhsVarRef(AstVarRef* nodep) {
        AstVar* const key = nodep->varp();
        const auto it = m_lhsmap.find(key);
        UINFO(9, "    mapInsertLhsVarRef " << nodep << endl);
        if (it == m_lhsmap.end()) {  // Not found
            RefVec* const refsp = new RefVec;
            refsp->push_back(nodep);
            m_lhsmap.emplace(key, refsp);
        } else {
            it->second->push_back(nodep);
        }
    }

    AstNode* newEnableDeposit(AstSel* selp, AstNode* enp) {
        // Form a "deposit" instruction for given enable, using existing select as a template.
        // Would be nicer if we made this a new AST type
        AstNode* const newp = new AstShiftL(
            selp->fileline(), new AstExtend(selp->fileline(), enp, selp->fromp()->width()),
            selp->lsbp()->cloneTree(false), selp->fromp()->width());
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
            || (nodep->op2p() && nodep->op2p()->user1p() && !VN_IS(nodep->op1p(), Var))
            || (nodep->op3p() && nodep->op3p()->user1p() && !VN_IS(nodep->op1p(), Var))
            || (nodep->op4p() && nodep->op4p()->user1p() && !VN_IS(nodep->op1p(), Var))) {
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
                        = new AstVarRef(varp->fileline(), varp, VAccess::WRITE);
                    AstNode* const newp = new AstAssignW(varp->fileline(), varrefp, constp);
                    UINFO(9, "       newoev " << newp << endl);
                    varrefp->user1p(newAllZerosOrOnes(varp, false));
                    nodep->addStmtp(newp);
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
            const RefVec* const refsp = it->second;
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

    void insertTristatesSignal(AstNodeModule* nodep, AstVar* const invarp,
                               const RefVec* const refsp) {
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

        AstNode* orp = nullptr;
        AstNode* enp = nullptr;
        AstNode* undrivenp = nullptr;

        // loop through the lhs drivers to build the driver resolution logic
        for (auto refp : *refsp) {
            const int w = lhsp->width();

            // create the new lhs driver for this var
            AstVar* const newlhsp = new AstVar(lhsp->fileline(), VVarType::MODULETEMP,
                                               lhsp->name() + "__out" + cvtToStr(m_unique),
                                               VFlagBitPacked(), w);  // 2-state ok; sep enable
            UINFO(9, "       newout " << newlhsp << endl);
            nodep->addStmtp(newlhsp);
            refp->varp(newlhsp);  // assign the new var to the varref
            refp->name(newlhsp->name());

            // create a new var for this drivers enable signal
            AstVar* const newenp = new AstVar(lhsp->fileline(), VVarType::MODULETEMP,
                                              lhsp->name() + "__en" + cvtToStr(m_unique++),
                                              VFlagBitPacked(), w);  // 2-state ok
            UINFO(9, "       newenp " << newenp << endl);
            nodep->addStmtp(newenp);

            AstNode* const enassp = new AstAssignW(
                refp->fileline(), new AstVarRef(refp->fileline(), newenp, VAccess::WRITE),
                getEnp(refp));
            UINFO(9, "       newass " << enassp << endl);
            nodep->addStmtp(enassp);

            // now append this driver to the driver logic.
            AstNode* const ref1p = new AstVarRef(refp->fileline(), newlhsp, VAccess::READ);
            AstNode* const ref2p = new AstVarRef(refp->fileline(), newenp, VAccess::READ);
            AstNode* const andp = new AstAnd(refp->fileline(), ref1p, ref2p);

            // or this to the others
            orp = (!orp) ? andp : new AstOr(refp->fileline(), orp, andp);

            if (envarp) {
                AstNode* const ref3p = new AstVarRef(refp->fileline(), newenp, VAccess::READ);
                enp = (!enp) ? ref3p : new AstOr(ref3p->fileline(), enp, ref3p);
            }
            AstNode* const tmp = new AstNot(
                newenp->fileline(), new AstVarRef(newenp->fileline(), newenp, VAccess::READ));
            undrivenp = ((!undrivenp) ? tmp : new AstAnd(refp->fileline(), tmp, undrivenp));
        }
        if (!undrivenp) {  // No drivers on the bus
            undrivenp = newAllZerosOrOnes(invarp, true);
        }
        if (!outvarp) {
            // This is the final pre-forced resolution of the tristate, so we apply
            // the pull direction to any undriven pins.
            const AstPull* const pullp = static_cast<AstPull*>(lhsp->user3p());
            bool pull1 = pullp && pullp->direction() == 1;  // Else default is down
            undrivenp
                = new AstAnd{invarp->fileline(), undrivenp, newAllZerosOrOnes(invarp, pull1)};
            orp = new AstOr(invarp->fileline(), orp, undrivenp);
        } else {
            VL_DO_DANGLING(undrivenp->deleteTree(), undrivenp);
        }
        if (envarp) {
            nodep->addStmtp(new AstAssignW(
                enp->fileline(), new AstVarRef(envarp->fileline(), envarp, VAccess::WRITE), enp));
        }
        // __out (child) or <in> (parent) = drive-value expression
        AstNode* const assp = new AstAssignW(
            lhsp->fileline(), new AstVarRef(lhsp->fileline(), lhsp, VAccess::WRITE), orp);
        assp->user2(U2_BOTH);  // Don't process further; already resolved
        if (debug() >= 9) assp->dumpTree(cout, "-lhsp-eqn: ");
        nodep->addStmtp(assp);
    }

    // VISITORS
    virtual void visit(AstConst* nodep) override {
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
                AstNode* const newp = new AstVarRef(nodep->fileline(), varp, VAccess::WRITE);
                UINFO(9, " const->" << newp << endl);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (m_tgraph.isTristate(nodep)) {
                m_tgraph.didProcess(nodep);
                FileLine* const fl = nodep->fileline();
                V3Number numz(nodep, nodep->width());
                numz.opBitsZ(nodep->num());  // Z->1, else 0
                V3Number numz0(nodep, nodep->width());
                numz0.opNot(numz);  // Z->0, else 1
                V3Number num1(nodep, nodep->width());
                num1.opAnd(nodep->num(), numz0);  // 01X->01X, Z->0
                AstConst* const newconstp = new AstConst(fl, num1);
                AstConst* const enp = new AstConst(fl, numz0);
                nodep->replaceWith(newconstp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                newconstp->user1p(enp);  // Propagate up constant with non-Z bits as 1
            }
        }
    }

    virtual void visit(AstCond* nodep) override {
        if (m_graphing) {
            iterateChildren(nodep);
            if (m_alhs) {
                associateLogic(nodep, nodep->expr1p());
                associateLogic(nodep, nodep->expr2p());
            } else {
                associateLogic(nodep->expr1p(), nodep);
                associateLogic(nodep->expr2p(), nodep);
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
            AstNode* const condp = nodep->condp();
            if (condp->user1p()) {
                condp->v3warn(E_UNSUPPORTED, "Unsupported: don't know how to deal with "
                                             "tristate logic in the conditional expression");
            }
            AstNode* const expr1p = nodep->expr1p();
            AstNode* const expr2p = nodep->expr2p();
            if (expr1p->user1p() || expr2p->user1p()) {  // else no tristates
                m_tgraph.didProcess(nodep);
                AstNode* const en1p = getEnp(expr1p);
                AstNode* const en2p = getEnp(expr2p);
                // The output enable of a cond is a cond of the output enable of the
                // two expressions with the same conditional.
                AstNode* const enp
                    = new AstCond(nodep->fileline(), condp->cloneTree(false), en1p, en2p);
                UINFO(9, "       newcond " << enp << endl);
                nodep->user1p(enp);  // propagate up COND(lhsp->enable, rhsp->enable)
                expr1p->user1p(nullptr);
                expr2p->user1p(nullptr);
            }
        }
    }

    virtual void visit(AstSel* nodep) override {
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
                    AstNode* const newp = newEnableDeposit(nodep, nodep->user1p());
                    nodep->fromp()->user1p(newp);  // Push to varref (etc)
                    if (debug() >= 9) newp->dumpTree(cout, "-assign-sel; ");
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
                    AstNode* const en1p = getEnp(nodep->fromp());
                    AstNode* const enp
                        = new AstSel(nodep->fileline(), en1p, nodep->lsbp()->cloneTree(true),
                                     nodep->widthp()->cloneTree(true));
                    UINFO(9, "       newsel " << enp << endl);
                    nodep->user1p(enp);  // propagate up SEL(fromp->enable, value)
                    m_tgraph.didProcess(nodep);
                }
            }
        }
    }

    virtual void visit(AstConcat* nodep) override {
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
                    AstNode* const enp = nodep->user1p();
                    nodep->user1p(nullptr);
                    nodep->lhsp()->user1p(new AstSel(nodep->fileline(), enp->cloneTree(true),
                                                     nodep->rhsp()->width(),
                                                     nodep->lhsp()->width()));
                    nodep->rhsp()->user1p(
                        new AstSel(nodep->fileline(), enp, 0, nodep->rhsp()->width()));
                    m_tgraph.didProcess(nodep);
                }
                iterateChildren(nodep);
            } else {
                iterateChildren(nodep);
                UINFO(9, dbgState() << nodep << endl);
                // Generate the new output enable signal, just as a concat
                // identical to the data concat
                AstNode* const expr1p = nodep->lhsp();
                AstNode* const expr2p = nodep->rhsp();
                if (expr1p->user1p() || expr2p->user1p()) {  // else no tristates
                    m_tgraph.didProcess(nodep);
                    AstNode* const en1p = getEnp(expr1p);
                    AstNode* const en2p = getEnp(expr2p);
                    AstNode* const enp = new AstConcat(nodep->fileline(), en1p, en2p);
                    UINFO(9, "       newconc " << enp << endl);
                    nodep->user1p(enp);  // propagate up CONCAT(lhsp->enable, rhsp->enable)
                    expr1p->user1p(nullptr);
                    expr2p->user1p(nullptr);
                }
            }
        }
    }

    virtual void visit(AstBufIf1* nodep) override {
        // For BufIf1, the enable is the LHS expression
        iterateChildren(nodep);
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            associateLogic(nodep->rhsp(), nodep);
            m_tgraph.setTristate(nodep);
        } else {
            if (debug() >= 9) nodep->backp()->dumpTree(cout, "-bufif: ");
            if (m_alhs) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported LHS tristate construct: " << nodep->prettyTypeName());
                return;
            }
            m_tgraph.didProcess(nodep);
            AstNode* const expr1p = nodep->lhsp()->unlinkFrBack();
            AstNode* const expr2p = nodep->rhsp()->unlinkFrBack();
            AstNode* enp;
            if (AstNode* const en2p = expr2p->user1p()) {
                enp = new AstAnd(nodep->fileline(), expr1p, en2p);
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
            AstNode* const expr1p = nodep->lhsp();
            AstNode* const expr2p = nodep->rhsp();
            if (!expr1p->user1p() && !expr2p->user1p()) {
                return;  // no tristates in either expression, so nothing to do
            }
            m_tgraph.didProcess(nodep);
            AstNode* const en1p = getEnp(expr1p);
            AstNode* const en2p = getEnp(expr2p);
            AstNode* subexpr1p = expr1p->cloneTree(false);
            AstNode* subexpr2p = expr2p->cloneTree(false);
            if (isAnd) {
                subexpr1p = new AstNot(nodep->fileline(), subexpr1p);
                subexpr2p = new AstNot(nodep->fileline(), subexpr2p);
            }
            // calc new output enable
            AstNode* const enp = new AstOr(
                nodep->fileline(), new AstAnd(nodep->fileline(), en1p, en2p),
                new AstOr(nodep->fileline(),
                          new AstAnd(nodep->fileline(), en1p->cloneTree(false), subexpr1p),
                          new AstAnd(nodep->fileline(), en2p->cloneTree(false), subexpr2p)));
            UINFO(9, "       neweqn " << enp << endl);
            nodep->user1p(enp);
            expr1p->user1p(nullptr);
            expr2p->user1p(nullptr);
        }
    }
    virtual void visit(AstAnd* nodep) override { visitAndOr(nodep, true); }
    virtual void visit(AstOr* nodep) override { visitAndOr(nodep, false); }

    void visitAssign(AstNodeAssign* nodep) {
        if (m_graphing) {
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
            if (debug() >= 9) nodep->dumpTree(cout, "-assign: ");
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
            iterateAndNextNull(nodep->lhsp());
            m_alhs = false;
        }
    }
    virtual void visit(AstAssignW* nodep) override { visitAssign(nodep); }
    virtual void visit(AstAssign* nodep) override { visitAssign(nodep); }

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
            AstVarRef* const varrefp = VN_CAST(nodep->rhsp(), VarRef);  // Input variable
            if (constp && constp->user1p() && varrefp) {
                // 3'b1z0 -> ((3'b101 == in__en) && (3'b100 == in))
                varrefp->unlinkFrBack();
                FileLine* const fl = nodep->fileline();
                const V3Number oneIfEn
                    = VN_AS(constp->user1p(), Const)
                          ->num();  // visit(AstConst) already split into en/ones
                const V3Number& oneIfEnOne = constp->num();
                AstVar* const envarp = getCreateEnVarp(varrefp->varp());
                AstNode* newp
                    = new AstLogAnd(fl,
                                    new AstEq(fl, new AstConst(fl, oneIfEn),
                                              new AstVarRef(fl, envarp, VAccess::READ)),
                                    // Keep the caseeq if there are X's present
                                    new AstEqCase(fl, new AstConst(fl, oneIfEnOne), varrefp));
                if (neq) newp = new AstLogNot(fl, newp);
                UINFO(9, "       newceq " << newp << endl);
                if (debug() >= 9) nodep->dumpTree(cout, "-caseeq-old: ");
                if (debug() >= 9) newp->dumpTree(cout, "-caseeq-new: ");
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (constp && nodep->rhsp()->user1p()) {
                FileLine* const fl = nodep->fileline();
                constp->unlinkFrBack();
                AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
                AstNode* newp = new AstLogAnd{
                    fl, new AstEq{fl, newAllZerosOrOnes(constp, false), rhsp->user1p()},
                    // Keep the caseeq if there are X's present
                    new AstEqCase{fl, constp, rhsp}};
                if (neq) newp = new AstLogNot{fl, newp};
                rhsp->user1p(nullptr);
                UINFO(9, "       newceq " << newp << endl);
                if (debug() >= 9) nodep->dumpTree(cout, "-caseeq-old: ");
                if (debug() >= 9) newp->dumpTree(cout, "-caseeq-new: ");
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
    virtual void visit(AstEqCase* nodep) override { visitCaseEq(nodep, false); }
    virtual void visit(AstNeqCase* nodep) override { visitCaseEq(nodep, true); }
    virtual void visit(AstEqWild* nodep) override { visitEqNeqWild(nodep); }
    virtual void visit(AstNeqWild* nodep) override { visitEqNeqWild(nodep); }

    virtual void visit(AstCountBits* nodep) override {
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
            AstNode* nonXp = nullptr;
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
                AstNode* newp = new AstCountOnes(
                    nodep->fileline(), new AstVarRef(nodep->fileline(), envarp, VAccess::READ));
                if (nonXp) {  // Need to still count '0 or '1 or 'x's
                    if (dropop[0]) {
                        nodep->rhsp()->unlinkFrBack()->deleteTree();
                        nodep->rhsp(nonXp->cloneTree(true));
                    }
                    if (dropop[1]) {
                        nodep->thsp()->unlinkFrBack()->deleteTree();
                        nodep->thsp(nonXp->cloneTree(true));
                    }
                    if (dropop[2]) {
                        nodep->fhsp()->unlinkFrBack()->deleteTree();
                        nodep->fhsp(nonXp->cloneTree(true));
                    }
                    newp = new AstAdd(nodep->fileline(), nodep, newp);
                }
                if (debug() >= 9) newp->dumpTree(cout, "-countout: ");
                relinkHandle.relink(newp);
            }
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstPull* nodep) override {
        UINFO(9, dbgState() << nodep << endl);
        AstVarRef* varrefp = nullptr;
        if (VN_IS(nodep->lhsp(), VarRef)) {
            varrefp = VN_AS(nodep->lhsp(), VarRef);
        } else if (VN_IS(nodep->lhsp(), Sel)
                   && VN_IS(VN_AS(nodep->lhsp(), Sel)->fromp(), VarRef)) {
            varrefp = VN_AS(VN_AS(nodep->lhsp(), Sel)->fromp(), VarRef);
        }
        if (!varrefp) {
            if (debug() >= 4) nodep->dumpTree(cout, "- ");
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
    virtual void visit(AstPin* nodep) override {
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
            if (debug() >= 9) nodep->dumpTree(cout, "-pin-pre: ");

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
                nodep->exprp(new AstVarRef(nodep->fileline(), ucVarp,
                                           // We converted, so use declaration output state
                                           nodep->modVarp()->declDirection().isWritable()
                                               ? VAccess::WRITE
                                               : VAccess::READ));
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
            AstNode* enrefp;
            {
                AstVar* const enVarp = new AstVar(nodep->fileline(), VVarType::MODULETEMP,
                                                  nodep->name() + "__en" + cvtToStr(m_unique++),
                                                  VFlagBitPacked(), enModVarp->width());
                if (inDeclProcessing) {  // __en(from-resolver-const) or __en(from-resolver-wire)
                    enModVarp->varType2In();
                } else {
                    enModVarp->varType2Out();
                }
                UINFO(9, "       newenv " << enVarp << endl);
                AstPin* const enpinp
                    = new AstPin(nodep->fileline(), nodep->pinNum(),
                                 enModVarp->name(),  // should be {var}"__en"
                                 new AstVarRef(nodep->fileline(), enVarp, VAccess::WRITE));
                enpinp->modVarp(enModVarp);
                UINFO(9, "       newpin " << enpinp << endl);
                enpinp->user2(U2_BOTH);  // don't iterate the pin later
                nodep->addNextHere(enpinp);
                m_modp->addStmtp(enVarp);
                enrefp = new AstVarRef(nodep->fileline(), enVarp, VAccess::READ);
                UINFO(9, "       newvrf " << enrefp << endl);
                if (debug() >= 9) enpinp->dumpTree(cout, "-pin-ena: ");
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
                AstNode* const outexprp
                    = nodep->exprp()->cloneTree(false);  // Note has lvalue() set
                outpinp = new AstPin(nodep->fileline(), nodep->pinNum(),
                                     outModVarp->name(),  // should be {var}"__out"
                                     outexprp);
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
                if (debug() >= 9) outpinp->dumpTree(cout, "-pin-opr: ");
                outAssignp = V3Inst::pinReconnectSimple(outpinp, m_cellp,
                                                        true);  // Note may change outpinp->exprp()
                if (debug() >= 9) outpinp->dumpTree(cout, "-pin-out: ");
                if (debug() >= 9 && outAssignp) outAssignp->dumpTree(cout, "-pin-out: ");
                // Must still iterate the outAssignp, as need to build output equation
            }

            // Existing pin becomes an input, and we mark each resulting signal as tristate
            const TristatePinVisitor visitor{nodep->exprp(), m_tgraph, false};
            const AstNode* const inAssignp = V3Inst::pinReconnectSimple(
                nodep, m_cellp, true);  // Note may change nodep->exprp()
            if (debug() >= 9) nodep->dumpTree(cout, "-pin-in:  ");
            if (debug() >= 9 && inAssignp) inAssignp->dumpTree(cout, "-pin-as:  ");

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

    virtual void visit(AstVarRef* nodep) override {
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
                nodep->user1p(new AstVarRef(nodep->fileline(), enVarp, VAccess::READ));
            }
            if (m_alhs) {}  // NOP; user1() already passed down from assignment
        }
    }

    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        UINFO(9, dbgState() << nodep << endl);
        if (m_graphing) {
            // If tri0/1 force a pullup
            if (nodep->user2() & U2_GRAPHING) return;  // Already processed
            nodep->user2(U2_GRAPHING);
            if (nodep->isPulldown() || nodep->isPullup()) {
                AstNode* const newp = new AstPull(
                    nodep->fileline(), new AstVarRef(nodep->fileline(), nodep, VAccess::WRITE),
                    nodep->isPullup());
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

    virtual void visit(AstNodeModule* nodep) override {
        UINFO(8, nodep << endl);
        VL_RESTORER(m_modp);
        VL_RESTORER(m_graphing);
        VL_RESTORER(m_unique);
        VL_RESTORER(m_lhsmap);
        // Not preserved, needs pointer instead: TristateGraph origTgraph = m_tgraph;
        UASSERT_OBJ(m_tgraph.empty(), nodep, "Unsupported: NodeModule under NodeModule");
        {
            // Clear state
            m_graphing = false;
            m_tgraph.clear();
            m_unique = 0;
            m_logicp = nullptr;
            m_lhsmap.clear();
            m_modp = nodep;
            // Walk the graph, finding all variables and tristate constructs
            {
                m_graphing = true;
                iterateChildren(nodep);
                m_graphing = false;
            }
            // Use graph to find tristate signals
            m_tgraph.graphWalk(nodep);
            // Build the LHS drivers map for this module
            iterateChildren(nodep);
            // Insert new logic for all tristates
            insertTristates(nodep);
        }
        m_tgraph.clear();  // Recursion not supported
    }

    virtual void visit(AstClass* nodep) override {
        // don't deal with classes
    }
    virtual void visit(AstNodeFTask* nodep) override {
        // don't deal with functions
    }

    virtual void visit(AstCaseItem* nodep) override {
        // don't deal with casez compare '???? values
        iterateAndNextNull(nodep->bodysp());
    }

    virtual void visit(AstCell* nodep) override {
        VL_RESTORER(m_cellp);
        m_cellp = nodep;
        m_alhs = false;
        iterateChildren(nodep);
    }

    virtual void visit(AstNetlist* nodep) override { iterateChildrenBackwards(nodep); }

    // Default: Just iterate
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        checkUnhandled(nodep);
    }

public:
    // CONSTRUCTORS
    explicit TristateVisitor(AstNode* nodep) {
        m_tgraph.clear();
        iterate(nodep);
    }
    virtual ~TristateVisitor() override {
        V3Stats::addStat("Tristate, Tristate resolved nets", m_statTriSigs);
    }
};

//######################################################################
// Tristate class functions

void V3Tristate::tristateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TristateVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("tristate", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
