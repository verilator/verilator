// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
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
// V3Trace's Transformations:
//
//  Examine whole design and build a graph describing which function call
//  may result in a write to a traced variable. This is done in 2 passes:
//
//  Pass 1:
//      Add vertices for TraceDecl, CFunc, CCall and VarRef nodes, add
//      edges from CCall -> CFunc, VarRef -> TraceDecl, also add edges
//      for public entry points to CFuncs (these are like a spontaneous
//      call)
//
//  Pass 2:
//      Add edges from CFunc -> VarRef being written
//
//  Finally:
//      Process graph to determine when traced variables can change, allocate
//      activity flags, insert nodes to set activity flags, allocate signal
//      numbers (codes), and construct the full and incremental trace
//      functions, together with all other trace support functions.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Trace.h"

#include "V3DupFinder.h"
#include "V3EmitCBase.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <limits>
#include <map>
#include <set>

//######################################################################
// Graph vertexes

class TraceActivityVertex final : public V3GraphVertex {
    AstNode* const m_insertp;
    int32_t m_activityCode;
    bool m_slow;  // If always slow, we can use the same code
public:
    enum { ACTIVITY_NEVER = ((1UL << 31) - 1) };
    enum { ACTIVITY_ALWAYS = ((1UL << 31) - 2) };
    enum { ACTIVITY_SLOW = 0 };
    TraceActivityVertex(V3Graph* graphp, AstNode* nodep, bool slow)
        : V3GraphVertex{graphp}
        , m_insertp{nodep} {
        m_activityCode = 0;
        m_slow = slow;
    }
    TraceActivityVertex(V3Graph* graphp, int32_t code)
        : V3GraphVertex{graphp}
        , m_insertp{nullptr} {
        m_activityCode = code;
        m_slow = false;
    }
    virtual ~TraceActivityVertex() override = default;
    // ACCESSORS
    AstNode* insertp() const {
        if (!m_insertp) v3fatalSrc("Null insertp; probably called on a special always/slow.");
        return m_insertp;
    }
    virtual string name() const override {
        if (activityAlways()) {
            return "*ALWAYS*";
        } else {
            return std::string{slow() ? "*SLOW* " : ""} + insertp()->name();
        }
    }
    virtual string dotColor() const override { return slow() ? "yellowGreen" : "green"; }
    int32_t activityCode() const { return m_activityCode; }
    bool activityAlways() const { return activityCode() == ACTIVITY_ALWAYS; }
    bool activitySlow() const { return activityCode() == ACTIVITY_SLOW; }
    void activityCode(int32_t code) { m_activityCode = code; }
    bool slow() const { return m_slow; }
    void slow(bool flag) {
        if (!flag) m_slow = false;
    }
};

class TraceCFuncVertex final : public V3GraphVertex {
    AstCFunc* const m_nodep;

public:
    TraceCFuncVertex(V3Graph* graphp, AstCFunc* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    virtual ~TraceCFuncVertex() override = default;
    // ACCESSORS
    AstCFunc* nodep() const { return m_nodep; }
    virtual string name() const override { return nodep()->name(); }
    virtual string dotColor() const override { return "yellow"; }
    virtual FileLine* fileline() const override { return nodep()->fileline(); }
};

class TraceTraceVertex final : public V3GraphVertex {
    AstTraceDecl* const m_nodep;  // TRACEINC this represents
    // nullptr, or other vertex with the real code() that duplicates this one
    TraceTraceVertex* m_duplicatep = nullptr;

public:
    TraceTraceVertex(V3Graph* graphp, AstTraceDecl* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    virtual ~TraceTraceVertex() override = default;
    // ACCESSORS
    AstTraceDecl* nodep() const { return m_nodep; }
    virtual string name() const override { return nodep()->name(); }
    virtual string dotColor() const override { return "red"; }
    virtual FileLine* fileline() const override { return nodep()->fileline(); }
    TraceTraceVertex* duplicatep() const { return m_duplicatep; }
    void duplicatep(TraceTraceVertex* dupp) {
        UASSERT_OBJ(!duplicatep(), nodep(), "Assigning duplicatep() to already duplicated node");
        m_duplicatep = dupp;
    }
};

class TraceVarVertex final : public V3GraphVertex {
    AstVarScope* const m_nodep;

public:
    TraceVarVertex(V3Graph* graphp, AstVarScope* nodep)
        : V3GraphVertex{graphp}
        , m_nodep{nodep} {}
    virtual ~TraceVarVertex() override = default;
    // ACCESSORS
    AstVarScope* nodep() const { return m_nodep; }
    virtual string name() const override { return nodep()->name(); }
    virtual string dotColor() const override { return "skyblue"; }
    virtual FileLine* fileline() const override { return nodep()->fileline(); }
};

//######################################################################
// Trace state, as a visitor of each AstNode

class TraceVisitor final : public EmitCBaseVisitor {
private:
    // NODE STATE
    // V3Hasher in V3DupFinder
    //  Ast*::user4()                   // V3Hasher calculation
    // Cleared entire netlist
    //  AstCFunc::user1()               // V3GraphVertex* for this node
    //  AstTraceDecl::user1()           // V3GraphVertex* for this node
    //  AstVarScope::user1()            // V3GraphVertex* for this node
    //  AstCCall::user2()               // bool; walked next list for other ccalls
    //  Ast*::user3()                   // TraceActivityVertex* for this node
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;
    // VNUser4InUse     In V3Hasher via V3DupFinder

    // STATE
    AstNodeModule* m_topModp = nullptr;  // Module to add variables to
    AstScope* const m_topScopep = v3Global.rootp()->topScopep()->scopep();  // The top AstScope
    AstCFunc* m_cfuncp = nullptr;  // C function adding to graph
    AstCFunc* m_regFuncp = nullptr;  // Trace registration function
    AstTraceDecl* m_tracep = nullptr;  // Trace function adding to graph
    AstVarScope* m_activityVscp = nullptr;  // Activity variable
    uint32_t m_activityNumber = 0;  // Count of fields in activity variable
    uint32_t m_code = 0;  // Trace ident code# being assigned
    V3Graph m_graph;  // Var/CFunc tracking
    TraceActivityVertex* const m_alwaysVtxp;  // "Always trace" vertex
    bool m_finding = false;  // Pass one of algorithm?

    // Trace parallelism. Only VCD tracing can be parallelized at this time.
    const uint32_t m_parallelism
        = v3Global.opt.useTraceParallel() ? static_cast<uint32_t>(v3Global.opt.threads()) : 1;

    VDouble0 m_statUniqSigs;  // Statistic tracking
    VDouble0 m_statUniqCodes;  // Statistic tracking

    // All activity numbers applying to a given trace
    using ActCodeSet = std::set<uint32_t>;
    // For activity set, what traces apply
    using TraceVec = std::multimap<ActCodeSet, TraceTraceVertex*>;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void detectDuplicates() {
        UINFO(9, "Finding duplicates\n");
        // Note uses user4
        V3DupFinder dupFinder;  // Duplicate code detection
        // Hash all of the values the traceIncs need
        for (const V3GraphVertex* itp = m_graph.verticesBeginp(); itp;
             itp = itp->verticesNextp()) {
            if (const TraceTraceVertex* const vvertexp
                = dynamic_cast<const TraceTraceVertex*>(itp)) {
                const AstTraceDecl* const nodep = vvertexp->nodep();
                if (nodep->valuep()) {
                    UASSERT_OBJ(nodep->valuep()->backp() == nodep, nodep,
                                "Trace duplicate back needs consistency,"
                                " so we can map duplicates back to TRACEINCs");
                    // Just keep one node in the map and point all duplicates to this node
                    if (dupFinder.findDuplicate(nodep->valuep()) == dupFinder.end()) {
                        dupFinder.insert(nodep->valuep());
                    }
                }
            }
        }
        // Find if there are any duplicates
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (TraceTraceVertex* const vvertexp = dynamic_cast<TraceTraceVertex*>(itp)) {
                const AstTraceDecl* const nodep = vvertexp->nodep();
                if (nodep->valuep() && !vvertexp->duplicatep()) {
                    const auto dupit = dupFinder.findDuplicate(nodep->valuep());
                    if (dupit != dupFinder.end()) {
                        const AstTraceDecl* const dupDeclp
                            = VN_AS(dupit->second->backp(), TraceDecl);
                        UASSERT_OBJ(dupDeclp, nodep, "Trace duplicate of wrong type");
                        TraceTraceVertex* const dupvertexp
                            = dynamic_cast<TraceTraceVertex*>(dupDeclp->user1u().toGraphVertex());
                        UINFO(8, "  Orig " << nodep << endl);
                        UINFO(8, "   dup " << dupDeclp << endl);
                        // Mark the hashed node as the original and our
                        // iterating node as duplicated
                        vvertexp->duplicatep(dupvertexp);
                    }
                }
            }
        }
    }

    void graphSimplify(bool initial) {
        if (initial) {
            // Remove all variable nodes
            for (V3GraphVertex *nextp, *itp = m_graph.verticesBeginp(); itp; itp = nextp) {
                nextp = itp->verticesNextp();
                if (TraceVarVertex* const vvertexp = dynamic_cast<TraceVarVertex*>(itp)) {
                    vvertexp->rerouteEdges(&m_graph);
                    vvertexp->unlinkDelete(&m_graph);
                }
            }
            // Remove multiple variables connecting funcs to traces
            // We do this twice, as then we have fewer edges to multiply out in the below
            // expansion.
            m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
            // Remove all Cfunc nodes
            for (V3GraphVertex *nextp, *itp = m_graph.verticesBeginp(); itp; itp = nextp) {
                nextp = itp->verticesNextp();
                if (TraceCFuncVertex* const vvertexp = dynamic_cast<TraceCFuncVertex*>(itp)) {
                    vvertexp->rerouteEdges(&m_graph);
                    vvertexp->unlinkDelete(&m_graph);
                }
            }
        }

        // Remove multiple variables connecting funcs to traces
        m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

        // If there are any edges from a always, keep only the always
        for (const V3GraphVertex* itp = m_graph.verticesBeginp(); itp;
             itp = itp->verticesNextp()) {
            if (const TraceTraceVertex* const vvertexp
                = dynamic_cast<const TraceTraceVertex*>(itp)) {
                // Search for the incoming always edge
                const V3GraphEdge* alwaysEdgep = nullptr;
                for (const V3GraphEdge* edgep = vvertexp->inBeginp(); edgep;
                     edgep = edgep->inNextp()) {
                    const TraceActivityVertex* const actVtxp
                        = dynamic_cast<const TraceActivityVertex*>(edgep->fromp());
                    UASSERT_OBJ(actVtxp, vvertexp->nodep(),
                                "Tracing a node with FROM non activity");
                    if (actVtxp->activityAlways()) {
                        alwaysEdgep = edgep;
                        break;
                    }
                }
                // If always edge exists, remove all other edges
                if (alwaysEdgep) {
                    for (V3GraphEdge *nextp, *edgep = vvertexp->inBeginp(); edgep; edgep = nextp) {
                        nextp = edgep->inNextp();
                        if (edgep != alwaysEdgep) edgep->unlinkDelete();
                    }
                }
            }
        }

        // Activity points with no outputs can be removed
        for (V3GraphVertex *nextp, *itp = m_graph.verticesBeginp(); itp; itp = nextp) {
            nextp = itp->verticesNextp();
            if (TraceActivityVertex* const vtxp = dynamic_cast<TraceActivityVertex*>(itp)) {
                // Leave in the always vertex for later use.
                if (vtxp != m_alwaysVtxp && !vtxp->outBeginp()) vtxp->unlinkDelete(&m_graph);
            }
        }
    }

    uint32_t assignactivityNumbers() {
        uint32_t activityNumber = 1;  // Note 0 indicates "slow" only
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (TraceActivityVertex* const vvertexp = dynamic_cast<TraceActivityVertex*>(itp)) {
                if (vvertexp != m_alwaysVtxp) {
                    if (vvertexp->slow()) {
                        vvertexp->activityCode(TraceActivityVertex::ACTIVITY_SLOW);
                    } else {
                        vvertexp->activityCode(activityNumber++);
                    }
                }
            }
        }
        return activityNumber;
    }

    void sortTraces(TraceVec& traces, uint32_t& nFullCodes, uint32_t& nChgCodes) {
        // Populate sort structure
        traces.clear();
        nFullCodes = 0;
        nChgCodes = 0;
        for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (TraceTraceVertex* const vtxp = dynamic_cast<TraceTraceVertex*>(itp)) {
                ActCodeSet actSet;
                UINFO(9, "  Add to sort: " << vtxp << endl);
                if (debug() >= 9) vtxp->nodep()->dumpTree(cout, "-   trnode: ");
                for (const V3GraphEdge* edgep = vtxp->inBeginp(); edgep;
                     edgep = edgep->inNextp()) {
                    const TraceActivityVertex* const cfvertexp
                        = dynamic_cast<const TraceActivityVertex*>(edgep->fromp());
                    UASSERT_OBJ(cfvertexp, vtxp->nodep(),
                                "Should have been function pointing to this trace");
                    UINFO(9, "   Activity: " << cfvertexp << endl);
                    if (cfvertexp->activityAlways()) {
                        // If code 0, we always trace; ignore other codes
                        actSet.insert(TraceActivityVertex::ACTIVITY_ALWAYS);
                    } else {
                        actSet.insert(cfvertexp->activityCode());
                    }
                }
                UASSERT_OBJ(actSet.count(TraceActivityVertex::ACTIVITY_ALWAYS) == 0
                                || actSet.size() == 1,
                            vtxp->nodep(), "Always active trace has further triggers");
                // Count nodes
                if (!vtxp->duplicatep()) {
                    const uint32_t inc = vtxp->nodep()->codeInc();
                    nFullCodes += inc;
                    if (!actSet.empty()) nChgCodes += inc;
                }
                if (actSet.empty()) {
                    // If a trace doesn't have activity, it's constant, and we
                    // don't need to track changes on it.
                    actSet.insert(TraceActivityVertex::ACTIVITY_NEVER);
                } else if (actSet.count(TraceActivityVertex::ACTIVITY_SLOW) && actSet.size() > 1) {
                    // If a trace depends on the slow flag as well as other
                    // flags, remove the dependency on the slow flag. We will
                    // make slow routines set all activity flags.
                    actSet.erase(TraceActivityVertex::ACTIVITY_SLOW);
                }
                traces.emplace(actSet, vtxp);
            }
        }
    }

    void graphOptimize() {
        // Assign initial activity numbers to activity vertices
        assignactivityNumbers();

        // Sort the traces by activity sets
        TraceVec traces;
        uint32_t unused1;
        uint32_t unused2;
        sortTraces(traces, unused1, unused2);

        // For each activity set with only a small number of signals, make those
        // signals always traced, as it's cheaper to check a few value changes
        // than to test a lot of activity flags
        auto it = traces.begin();
        const auto end = traces.end();
        while (it != end) {
            auto head = it;
            // Approximate the complexity of the value change check
            uint32_t complexity = 0;
            const ActCodeSet& actSet = it->first;
            for (; it != end && it->first == actSet; ++it) {
                if (!it->second->duplicatep()) {
                    uint32_t cost = 0;
                    const AstTraceDecl* const declp = it->second->nodep();
                    // The number of comparisons required by bufp->chg*
                    cost += declp->isWide() ? declp->codeInc() : 1;
                    // Arrays are traced by element
                    cost *= declp->arrayRange().ranged() ? declp->arrayRange().elements() : 1;
                    // Note: Experiments factoring in the size of declp->valuep()
                    // showed no benefit in tracing speed, even for large trees,
                    // so we will leve those out for now.
                    complexity += cost;
                }
            }
            // Leave alone always changing, never changing and signals only set in slow code
            if (actSet.count(TraceActivityVertex::ACTIVITY_ALWAYS)) continue;
            if (actSet.count(TraceActivityVertex::ACTIVITY_NEVER)) continue;
            if (actSet.count(TraceActivityVertex::ACTIVITY_SLOW)) continue;
            // If the value comparisons are cheaper to perform than checking the
            // activity flags make the signals always traced. Note this cost
            // equation is heuristic.
            if (complexity <= actSet.size() * 2) {
                for (; head != it; ++head) {
                    new V3GraphEdge(&m_graph, m_alwaysVtxp, head->second, 1);
                }
            }
        }

        graphSimplify(false);
    }

    AstNode* selectActivity(FileLine* flp, uint32_t acode, const VAccess& access) {
        return new AstArraySel(flp, new AstVarRef(flp, m_activityVscp, access), acode);
    }

    void addActivitySetter(AstNode* insertp, uint32_t code) {
        FileLine* const fl = insertp->fileline();
        AstAssign* const setterp = new AstAssign(fl, selectActivity(fl, code, VAccess::WRITE),
                                                 new AstConst(fl, AstConst::BitTrue()));
        if (AstCCall* const callp = VN_CAST(insertp, CCall)) {
            callp->addNextHere(setterp);
        } else if (AstCFunc* const funcp = VN_CAST(insertp, CFunc)) {
            funcp->addStmtsp(setterp);
        } else {
            insertp->v3fatalSrc("Bad trace activity vertex");
        }
    }

    void createActivityFlags() {
        // Assign final activity numbers
        m_activityNumber = assignactivityNumbers();

        // Create an array of bytes, not a bit vector, as they can be set
        // atomically by mtasks, and are cheaper to set (no need for
        // read-modify-write on the C type), and the speed of the tracing code
        // is the same on largish designs.
        FileLine* const flp = m_topScopep->fileline();
        AstNodeDType* const newScalarDtp = new AstBasicDType(flp, VFlagLogicPacked(), 1);
        v3Global.rootp()->typeTablep()->addTypesp(newScalarDtp);
        AstRange* const newArange
            = new AstRange{flp, VNumRange{static_cast<int>(m_activityNumber) - 1, 0}};
        AstNodeDType* const newArrDtp = new AstUnpackArrayDType(flp, newScalarDtp, newArange);
        v3Global.rootp()->typeTablep()->addTypesp(newArrDtp);
        AstVar* const newvarp
            = new AstVar(flp, VVarType::MODULETEMP, "__Vm_traceActivity", newArrDtp);
        m_topModp->addStmtp(newvarp);
        AstVarScope* const newvscp = new AstVarScope(flp, m_topScopep, newvarp);
        m_topScopep->addVarp(newvscp);
        m_activityVscp = newvscp;

        // Insert activity setters
        for (const V3GraphVertex* itp = m_graph.verticesBeginp(); itp;
             itp = itp->verticesNextp()) {
            if (const TraceActivityVertex* const vtxp
                = dynamic_cast<const TraceActivityVertex*>(itp)) {
                if (vtxp->activitySlow()) {
                    // Just set all flags in slow code as it should be rare.
                    // This will be rolled up into a loop by V3Reloop.
                    for (uint32_t code = 0; code < m_activityNumber; ++code) {
                        addActivitySetter(vtxp->insertp(), code);
                    }
                } else if (!vtxp->activityAlways()) {
                    addActivitySetter(vtxp->insertp(), vtxp->activityCode());
                }
            }
        }
    }

    AstCFunc* newCFunc(bool full, AstCFunc* topFuncp, int& funcNump, uint32_t baseCode = 0) {
        // Create new function
        const bool isTopFunc = topFuncp == nullptr;
        const string baseName = full && isTopFunc ? "trace_full_top_"
                                : full            ? "trace_full_sub_"
                                : isTopFunc       ? "trace_chg_top_"
                                                  : "trace_chg_sub_";

        FileLine* const flp = m_topScopep->fileline();
        AstCFunc* const funcp = new AstCFunc(flp, baseName + cvtToStr(funcNump++), m_topScopep);
        funcp->isTrace(true);
        funcp->dontCombine(true);
        funcp->isLoose(true);
        funcp->slow(full);
        funcp->isStatic(isTopFunc);
        // Add it to top scope
        m_topScopep->addActivep(funcp);
        const auto addInitStr = [funcp, flp](const string& str) -> void {
            funcp->addInitsp(new AstCStmt(flp, str));
        };
        if (isTopFunc) {
            // Top functions
            funcp->argTypes("void* voidSelf, " + v3Global.opt.traceClassBase()
                            + "::" + (v3Global.opt.useTraceOffload() ? "OffloadBuffer" : "Buffer")
                            + "* bufp");
            addInitStr(voidSelfAssign(m_topModp));
            addInitStr(symClassAssign());
            // Add global activity check to change dump functions
            if (!full) {  //
                addInitStr("if (VL_UNLIKELY(!vlSymsp->__Vm_activity)) return;\n");
            }
            // Register function
            if (full) {
                m_regFuncp->addStmtsp(new AstText(flp, "tracep->addFullCb(", true));
            } else {
                m_regFuncp->addStmtsp(new AstText(flp, "tracep->addChgCb(", true));
            }
            m_regFuncp->addStmtsp(new AstAddrOfCFunc(flp, funcp));
            m_regFuncp->addStmtsp(new AstText(flp, ", vlSelf", true));
            m_regFuncp->addStmtsp(new AstText(flp, ");\n", true));
        } else {
            // Sub functions
            funcp->argTypes(v3Global.opt.traceClassBase()
                            + "::" + +(v3Global.opt.useTraceOffload() ? "OffloadBuffer" : "Buffer")
                            + "* bufp");
            // Setup base references. Note in rare occasions we can end up with an empty trace
            // sub function, hence the VL_ATTR_UNUSED attributes.
            if (full) {
                // Full dump sub function
                addInitStr("uint32_t* const oldp VL_ATTR_UNUSED = "
                           "bufp->oldp(vlSymsp->__Vm_baseCode);\n");
            } else {
                // Change dump sub function
                if (v3Global.opt.useTraceOffload()) {
                    addInitStr("const uint32_t base VL_ATTR_UNUSED = "
                               "vlSymsp->__Vm_baseCode + "
                               + cvtToStr(baseCode) + ";\n");
                    addInitStr("if (false && bufp) {}  // Prevent unused\n");
                } else {
                    addInitStr("uint32_t* const oldp VL_ATTR_UNUSED = "
                               "bufp->oldp(vlSymsp->__Vm_baseCode + "
                               + cvtToStr(baseCode) + ");\n");
                }
            }
            // Add call to top function
            AstCCall* const callp = new AstCCall(funcp->fileline(), funcp);
            callp->argTypes("bufp");
            topFuncp->addStmtsp(callp);
        }
        // Done
        UINFO(5, "  newCFunc " << funcp << endl);
        return funcp;
    }

    void createFullTraceFunction(const TraceVec& traces, uint32_t nAllCodes,
                                 uint32_t parallelism) {
        const int splitLimit = v3Global.opt.outputSplitCTrace() ? v3Global.opt.outputSplitCTrace()
                                                                : std::numeric_limits<int>::max();

        int topFuncNum = 0;
        int subFuncNum = 0;
        auto it = traces.cbegin();
        while (it != traces.cend()) {
            AstCFunc* topFuncp = nullptr;
            AstCFunc* subFuncp = nullptr;
            int subStmts = 0;
            const uint32_t maxCodes = (nAllCodes + parallelism - 1) / parallelism;
            uint32_t nCodes = 0;
            for (; nCodes < maxCodes && it != traces.end(); ++it) {
                const TraceTraceVertex* const vtxp = it->second;
                AstTraceDecl* const declp = vtxp->nodep();
                if (const TraceTraceVertex* const canonVtxp = vtxp->duplicatep()) {
                    // This is a duplicate trace node. We will assign the signal
                    // number to the canonical node, and emit this as an alias, so
                    // no need to create a TraceInc node.
                    const AstTraceDecl* const canonDeclp = canonVtxp->nodep();
                    UASSERT_OBJ(!canonVtxp->duplicatep(), canonDeclp,
                                "Canonical node is a duplicate");
                    UASSERT_OBJ(canonDeclp->code() != 0, canonDeclp,
                                "Canonical node should have code assigned already");
                    declp->code(canonDeclp->code());
                } else {
                    // This is a canonical trace node. Assign signal number and
                    // add a TraceInc node to the full dump function.
                    UASSERT_OBJ(declp->code() == 0, declp,
                                "Canonical node should not have code assigned yet");
                    declp->code(m_code);
                    m_code += declp->codeInc();
                    m_statUniqCodes += declp->codeInc();
                    ++m_statUniqSigs;

                    // Create top function if not yet created
                    if (!topFuncp) { topFuncp = newCFunc(/* full: */ true, nullptr, topFuncNum); }

                    // Crate new sub function if required
                    if (!subFuncp || subStmts > splitLimit) {
                        subStmts = 0;
                        subFuncp = newCFunc(/* full: */ true, topFuncp, subFuncNum);
                    }

                    // Add TraceInc node
                    AstTraceInc* const incp
                        = new AstTraceInc(declp->fileline(), declp, /* full: */ true);
                    subFuncp->addStmtsp(incp);
                    subStmts += incp->nodeCount();

                    // Track partitioning
                    nCodes += declp->codeInc();
                }
            }
            if (topFuncp) {  // might be nullptr if all trailing entries were duplicates
                UINFO(5, "trace_full_top" << topFuncNum - 1 << " codes: " << nCodes << "/"
                                          << maxCodes << endl);
            }
        }
    }

    void createChgTraceFunctions(const TraceVec& traces, uint32_t nAllCodes,
                                 uint32_t parallelism) {
        const int splitLimit = v3Global.opt.outputSplitCTrace() ? v3Global.opt.outputSplitCTrace()
                                                                : std::numeric_limits<int>::max();
        int topFuncNum = 0;
        int subFuncNum = 0;
        TraceVec::const_iterator it = traces.begin();
        while (it != traces.end()) {
            AstCFunc* topFuncp = nullptr;
            AstCFunc* subFuncp = nullptr;
            int subStmts = 0;
            uint32_t maxCodes = (nAllCodes + parallelism - 1) / parallelism;
            if (maxCodes < 1) maxCodes = 1;
            uint32_t nCodes = 0;
            const ActCodeSet* prevActSet = nullptr;
            AstIf* ifp = nullptr;
            uint32_t baseCode = 0;
            for (; nCodes < maxCodes && it != traces.end(); ++it) {
                const TraceTraceVertex* const vtxp = it->second;
                // This is a duplicate decl, no need to add it to incremental dump
                if (vtxp->duplicatep()) continue;
                const ActCodeSet& actSet = it->first;
                // Traced value never changes, no need to add it to incremental dump
                if (actSet.count(TraceActivityVertex::ACTIVITY_NEVER)) continue;

                AstTraceDecl* const declp = vtxp->nodep();

                // Create top function if not yet created
                if (!topFuncp) { topFuncp = newCFunc(/* full: */ false, nullptr, topFuncNum); }

                // Create new sub function if required
                if (!subFuncp || subStmts > splitLimit) {
                    baseCode = declp->code();
                    subStmts = 0;
                    subFuncp = newCFunc(/* full: */ false, topFuncp, subFuncNum, baseCode);
                    prevActSet = nullptr;
                    ifp = nullptr;
                }

                // If required, create the conditional node checking the activity flags
                if (!prevActSet || actSet != *prevActSet) {
                    FileLine* const flp = m_topScopep->fileline();
                    const bool always = actSet.count(TraceActivityVertex::ACTIVITY_ALWAYS) != 0;
                    AstNode* condp = nullptr;
                    if (always) {
                        condp = new AstConst(flp, 1);  // Always true, will be folded later
                    } else {
                        for (const uint32_t actCode : actSet) {
                            AstNode* const selp = selectActivity(flp, actCode, VAccess::READ);
                            condp = condp ? new AstOr(flp, condp, selp) : selp;
                        }
                    }
                    ifp = new AstIf(flp, condp);
                    if (!always) ifp->branchPred(VBranchPred::BP_UNLIKELY);
                    subFuncp->addStmtsp(ifp);
                    subStmts += ifp->nodeCount();
                    prevActSet = &actSet;
                }

                // Add TraceInc node
                AstTraceInc* const incp
                    = new AstTraceInc(declp->fileline(), declp, /* full: */ false, baseCode);
                ifp->addIfsp(incp);
                subStmts += incp->nodeCount();

                // Track partitioning
                nCodes += declp->codeInc();
            }
            if (topFuncp) {  // might be nullptr if all trailing entries were duplicates/constants
                UINFO(5, "trace_chg_top" << topFuncNum - 1 << " codes: " << nCodes << "/"
                                         << maxCodes << endl);
            }
        }
    }

    void createCleanupFunction() {
        FileLine* const fl = m_topScopep->fileline();
        AstCFunc* const cleanupFuncp = new AstCFunc(fl, "trace_cleanup", m_topScopep);
        cleanupFuncp->argTypes("void* voidSelf, " + v3Global.opt.traceClassBase()
                               + "* /*unused*/");
        cleanupFuncp->isTrace(true);
        cleanupFuncp->slow(false);
        cleanupFuncp->isStatic(true);
        cleanupFuncp->isLoose(true);
        m_topScopep->addActivep(cleanupFuncp);
        cleanupFuncp->addInitsp(new AstCStmt(fl, voidSelfAssign(m_topModp)));
        cleanupFuncp->addInitsp(new AstCStmt(fl, symClassAssign()));

        // Register it
        m_regFuncp->addStmtsp(new AstText(fl, "tracep->addCleanupCb(", true));
        m_regFuncp->addStmtsp(new AstAddrOfCFunc(fl, cleanupFuncp));
        m_regFuncp->addStmtsp(new AstText(fl, ", vlSelf);\n", true));

        // Clear global activity flag
        cleanupFuncp->addStmtsp(
            new AstCStmt(m_topScopep->fileline(), string("vlSymsp->__Vm_activity = false;\n")));

        // Clear fine grained activity flags
        for (uint32_t i = 0; i < m_activityNumber; ++i) {
            AstNode* const clrp = new AstAssign(fl, selectActivity(fl, i, VAccess::WRITE),
                                                new AstConst(fl, AstConst::BitFalse()));
            cleanupFuncp->addStmtsp(clrp);
        }
    }

    void createTraceFunctions() {
        // Detect and remove duplicate values
        detectDuplicates();

        // Simplify & optimize the graph
        if (debug() >= 6) m_graph.dumpDotFilePrefixed("trace_pre");
        graphSimplify(true);
        if (debug() >= 6) m_graph.dumpDotFilePrefixed("trace_simplified");
        graphOptimize();
        if (debug() >= 6) m_graph.dumpDotFilePrefixed("trace_optimized");

        // Create the fine grained activity flags
        createActivityFlags();

        // Form a sorted list of the traces we are interested in
        TraceVec traces;  // The sorted traces
        // We will split functions such that each have to dump roughly the same amount of data
        // for this we need to keep tack of the number of codes used by the trace functions.
        uint32_t nFullCodes = 0;  // Number of non-duplicate codes (need to go into full* dump)
        uint32_t nChgCodes = 0;  // Number of non-constant codes (need to go in to chg* dump)
        sortTraces(traces, nFullCodes, nChgCodes);

        UINFO(5, "nFullCodes: " << nFullCodes << " nChgCodes: " << nChgCodes << endl);

        // Our keys are now sorted to have same activity number adjacent, then
        // by trace order. (Better would be execution order for cache
        // efficiency....) Last are constants and non-changers, as then the
        // last value vector is more compact

        // Create the trace registration function
        m_regFuncp = new AstCFunc(m_topScopep->fileline(), "trace_register", m_topScopep);
        m_regFuncp->argTypes(v3Global.opt.traceClassBase() + "* tracep");
        m_regFuncp->isTrace(true);
        m_regFuncp->slow(true);
        m_regFuncp->isStatic(false);
        m_regFuncp->isLoose(true);
        m_topScopep->addActivep(m_regFuncp);

        // Create the full dump functions, also allocates signal numbers
        createFullTraceFunction(traces, nFullCodes, m_parallelism);

        // Create the incremental dump functions
        createChgTraceFunctions(traces, nChgCodes, m_parallelism);

        // Remove refs to traced values from TraceDecl nodes, these have now moved under
        // TraceInc
        for (const auto& i : traces) {
            AstNode* const valuep = i.second->nodep()->valuep();
            valuep->unlinkFrBack();
            valuep->deleteTree();
        }

        // Create the trace cleanup function clearing the activity flags
        createCleanupFunction();
    }

    TraceCFuncVertex* getCFuncVertexp(AstCFunc* nodep) {
        TraceCFuncVertex* vertexp
            = dynamic_cast<TraceCFuncVertex*>(nodep->user1u().toGraphVertex());
        if (!vertexp) {
            vertexp = new TraceCFuncVertex(&m_graph, nodep);
            nodep->user1p(vertexp);
        }
        return vertexp;
    }
    TraceActivityVertex* getActivityVertexp(AstNode* nodep, bool slow) {
        TraceActivityVertex* vertexp
            = dynamic_cast<TraceActivityVertex*>(nodep->user3u().toGraphVertex());
        if (!vertexp) {
            vertexp = new TraceActivityVertex(&m_graph, nodep, slow);
            nodep->user3p(vertexp);
        }
        vertexp->slow(slow);
        return vertexp;
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        m_code = 1;  // Multiple TopScopes will require fixing how code#s
        // are assigned as duplicate varscopes must result in the same tracing code#.

        // Add vertexes for all TraceDecl, and edges from VARs each trace looks at
        m_finding = false;
        iterateChildren(nodep);

        // Add vertexes for all CFUNCs, and edges to VARs the func sets
        m_finding = true;
        iterateChildren(nodep);

        // Create the trace functions and insert them into the tree
        createTraceFunctions();
    }
    virtual void visit(AstNodeModule* nodep) override {
        if (nodep->isTop()) m_topModp = nodep;
        iterateChildren(nodep);
    }
    virtual void visit(AstCCall* nodep) override {
        UINFO(8, "   CCALL " << nodep << endl);
        if (!m_finding && !nodep->user2()) {
            // See if there are other calls in same statement list;
            // If so, all funcs might share the same activity code
            TraceActivityVertex* const activityVtxp
                = getActivityVertexp(nodep, nodep->funcp()->slow());
            for (AstNode* nextp = nodep; nextp; nextp = nextp->nextp()) {
                if (AstCCall* const ccallp = VN_CAST(nextp, CCall)) {
                    ccallp->user2(true);  // Processed
                    UINFO(8, "     SubCCALL " << ccallp << endl);
                    V3GraphVertex* const ccallFuncVtxp = getCFuncVertexp(ccallp->funcp());
                    activityVtxp->slow(ccallp->funcp()->slow());
                    new V3GraphEdge(&m_graph, activityVtxp, ccallFuncVtxp, 1);
                }
            }
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) override {
        UINFO(8, "   CFUNC " << nodep << endl);
        V3GraphVertex* const funcVtxp = getCFuncVertexp(nodep);
        if (!m_finding) {  // If public, we need a unique activity code to allow for sets
                           // directly in this func
            if (nodep->funcPublic() || nodep->dpiExportImpl()
                || nodep == v3Global.rootp()->evalp()) {
                V3GraphVertex* const activityVtxp = getActivityVertexp(nodep, nodep->slow());
                new V3GraphEdge(&m_graph, activityVtxp, funcVtxp, 1);
            }
        }
        VL_RESTORER(m_cfuncp);
        {
            m_cfuncp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstTraceDecl* nodep) override {
        UINFO(8, "   TRACE " << nodep << endl);
        if (!m_finding) {
            V3GraphVertex* const vertexp = new TraceTraceVertex(&m_graph, nodep);
            nodep->user1p(vertexp);

            UASSERT_OBJ(m_cfuncp, nodep, "Trace not under func");
            m_tracep = nodep;
            iterateChildren(nodep);
            m_tracep = nullptr;
        }
    }
    virtual void visit(AstVarRef* nodep) override {
        if (m_tracep) {
            UASSERT_OBJ(nodep->varScopep(), nodep, "No var scope?");
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Lvalue in trace?  Should be const.");
            V3GraphVertex* varVtxp = nodep->varScopep()->user1u().toGraphVertex();
            if (!varVtxp) {
                varVtxp = new TraceVarVertex(&m_graph, nodep->varScopep());
                nodep->varScopep()->user1p(varVtxp);
            }
            V3GraphVertex* const traceVtxp = m_tracep->user1u().toGraphVertex();
            new V3GraphEdge(&m_graph, varVtxp, traceVtxp, 1);
            if (nodep->varp()->isPrimaryInish()  // Always need to trace primary inputs
                || nodep->varp()->isSigPublic()) {  // Or ones user can change
                new V3GraphEdge(&m_graph, m_alwaysVtxp, traceVtxp, 1);
            }
        } else if (m_cfuncp && m_finding && nodep->access().isWriteOrRW()) {
            UASSERT_OBJ(nodep->varScopep(), nodep, "No var scope?");
            V3GraphVertex* const funcVtxp = getCFuncVertexp(m_cfuncp);
            V3GraphVertex* const varVtxp = nodep->varScopep()->user1u().toGraphVertex();
            if (varVtxp) {  // else we're not tracing this signal
                new V3GraphEdge(&m_graph, funcVtxp, varVtxp, 1);
            }
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceVisitor(AstNetlist* nodep)
        : m_alwaysVtxp{new TraceActivityVertex{&m_graph, TraceActivityVertex::ACTIVITY_ALWAYS}} {
        iterate(nodep);
    }
    virtual ~TraceVisitor() override {
        V3Stats::addStat("Tracing, Unique traced signals", m_statUniqSigs);
        V3Stats::addStat("Tracing, Unique trace codes", m_statUniqCodes);
    }
};

//######################################################################
// Trace class functions

void V3Trace::traceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { TraceVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("trace", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
