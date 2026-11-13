// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Trace activity analysis
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Trace's Transformations:
//
//  Works out which code can change each signal described by the run time
//  model descriptors, so the tracing runtime only reads a signal when
//  something that might have written it has run since the last dump.
//
//  This is tracked with activity flags (__Vactivity), set by statements
//  inserted where code that may write described variables is entered. Each
//  AstRtmdVar gets an activity set: the flags that cover all its writers.
//  The runtime reads a signal only if a flag in its set is set, and the
//  model clears all flags at its first eval after a dump. EVAL_FLAG is set
//  on every eval, SLOW_FLAG by slow code (which sets all flags), and each
//  other flag by one activity point.
//
//  Algorithm:
//      - Build a graph of flag vertices (activity points), CFunc vertices, and
//        variable vertices (variables read by described signals). Edges go
//        from each activity point to the CFuncs it enters, and from each CFunc
//        to the variables it writes.
//      - Remove the CFunc vertices, so each flag vertex connects directly to
//        the variables it may change.
//      - Allocate a flag to each flag vertex, and insert its setter.
//      - Give each signal the set of flags reaching its variable. The distinct
//        sets are recorded in AstNetlist::actSets().
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Trace.h"

#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Stats.h"
#include "V3VNUserAllocator.h"

#include <algorithm>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Graph vertexes

class TraceFlagVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceFlagVertex, V3GraphVertex)
    AstNode* const m_insertp;  // Where to insert the setter (StmtExpr, or CFunc)
    uint32_t m_activityCode = 0;  // Activity flag set by this vertex
    const bool m_slow;  // All code entered is slow, so can use SLOW_FLAG
public:
    TraceFlagVertex(V3Graph* graphp, AstNode* nodep, bool slow)
        : V3GraphVertex{graphp}
        , m_insertp{nodep}
        , m_slow{slow} {}
    ~TraceFlagVertex() override = default;
    // ACCESSORS
    AstNode* insertp() const { return m_insertp; }
    uint32_t activityCode() const { return m_activityCode; }
    void activityCode(uint32_t code) { m_activityCode = code; }
    bool slow() const { return m_slow; }

    // For Graphviz dump only
    std::string name() const override { return m_insertp->name(); }
    std::string dotColor() const override { return slow() ? "yellowGreen" : "green"; }
};

class TraceCFuncVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceCFuncVertex, V3GraphVertex)
    AstCFunc* const m_cfuncp;  // Function this vertex represents

public:
    TraceCFuncVertex(V3Graph* graphp, AstCFunc* nodep)
        : V3GraphVertex{graphp}
        , m_cfuncp{nodep} {}
    ~TraceCFuncVertex() override = default;

    // For Graphviz dump only
    std::string name() const override { return m_cfuncp->name(); }
    std::string dotColor() const override { return "yellow"; }
};

class TraceVarVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(TraceVarVertex, V3GraphVertex)
    AstVarScope* const m_vscp;  // Variable scope this vertex represents
    const bool m_always;  // Can change without any function running, so always active
    uint32_t m_actSetIdx = 0;  // Index of the activity set of this variable in AstNetlist

public:
    TraceVarVertex(V3Graph* graphp, AstVarScope* nodep, bool always)
        : V3GraphVertex{graphp}
        , m_vscp{nodep}
        , m_always{always} {}
    ~TraceVarVertex() override = default;
    // ACCESSORS
    bool always() const { return m_always; }
    uint32_t actSetIdx() const { return m_actSetIdx; }
    void actSetIdx(uint32_t idx) { m_actSetIdx = idx; }

    // For Graphviz dump only
    std::string name() const override { return m_vscp->name(); }
    std::string dotColor() const override { return "skyblue"; }
};

//######################################################################
// Trace state, as a visitor of each AstNode

class TraceVisitor final : public VNVisitor {
    // CONSTANTS
    // The activity flag set on every eval - This must be index 0, as V3EmitCModel sets that
    static constexpr uint32_t EVAL_FLAG = 0;
    // The activity flag shared by all slow code
    static constexpr uint32_t SLOW_FLAG = 1;

    // NODE STATE
    // Cleared entire netlist
    //  AstCFunc::user1p()              // V3GraphVertex* for this node
    //  AstVarScope::user1p()           // V3GraphVertex* for this node
    //  AstVar::user1p()                // Via m_ifaceMemberVscps
    //  AstStmtExpr::user2()            // bool; already part of a gathered run of calls
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstCFunc* m_cfuncp = nullptr;  // C function adding to graph
    V3Graph m_graph;  // Var/CFunc tracking

    // Statistics tracking
    VDouble0 m_statSettersFast;  // Number of activity flag setters inserted in fast code
    VDouble0 m_statSettersSlow;  // Number of activity flag setters inserted in slow code
    VDouble0 m_statSignals;  // Number of traced signals

    // Map from interface member Var to its VarScopes referenced by an AstRtmdVar
    VNUser1Allocator<AstVar, std::vector<AstVarScope*>> m_ifaceMemberVscps;

    // METHODS

    // Vertex of the given variable, or nullptr if no AstRtmdVar reads it
    static TraceVarVertex* getVarVertexp(AstVarScope* nodep) {
        return nodep->user1u().to<TraceVarVertex*>();
    }

    // Lazy constructs a vertex for the given CFunc, if not already done
    TraceCFuncVertex* getCFuncVertexp(AstCFunc* nodep) {
        TraceCFuncVertex* vtxp = nodep->user1u().to<TraceCFuncVertex*>();
        if (!vtxp) {
            vtxp = new TraceCFuncVertex{&m_graph, nodep};
            nodep->user1p(vtxp);
        }
        return vtxp;
    }

    // Create a vertex for each variable read by an AstRtmdVar
    void createVarVertices(AstNetlist* netlistp) {
        netlistp->topScopep()->rtmdp()->foreach([this](AstRtmdVar* sigp) {
            if (!sigp->traced()) return;
            ++m_statSignals;
            AstVarScope* const vscp = sigp->vscp();
            // Several signals might reference the same variable
            if (getVarVertexp(vscp)) return;

            // Create the TraceVarVertex for this variable
            AstVar* const varp = vscp->varp();
            const bool always = varp->isPrimaryInish()  // Always need to trace primary inputs
                                || (varp->isSigPublic() && !varp->isParam());  // Or user set
            TraceVarVertex* const varVtxp = new TraceVarVertex{&m_graph, vscp, always};
            vscp->user1p(varVtxp);

            // Gather the interface members, so writes through a virtual interface can be recorded
            if (varp->sensIfacep()) m_ifaceMemberVscps(varp).push_back(vscp);
        });
    }

    // Record that the current CFunc writes the given variable
    void addWriteEdge(AstVarScope* vscp) {
        TraceVarVertex* const varVtxp = getVarVertexp(vscp);
        // Only variables of described signals have a vertex
        if (!varVtxp) return;
        // Always active variables need no writers
        if (varVtxp->always()) return;
        new V3GraphEdge{&m_graph, getCFuncVertexp(m_cfuncp), varVtxp, 1};
    }

    void graphSimplify() {
        // Remove duplicate edges. We do this twice, as then we have fewer edges
        // to multiply out in the below expansion.
        m_graph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

        // Remove all CFunc vertices, they only serve as connectors
        for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
            if (TraceCFuncVertex* const fVtxp = vtxp->cast<TraceCFuncVertex>()) {
                fVtxp->rerouteEdges(&m_graph);
                fVtxp->unlinkDelete(&m_graph);
            }
        }

        // Remove duplicate edges
        m_graph.removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

        // Flag vertices that reach no variable can be removed
        for (V3GraphVertex* const vtxp : m_graph.vertices().unlinkable()) {
            if (TraceFlagVertex* const fVtxp = vtxp->cast<TraceFlagVertex>()) {
                if (fVtxp->outEmpty()) VL_DO_DANGLING(fVtxp->unlinkDelete(&m_graph), fVtxp);
            }
        }
    }

    void createActivityFlags(AstNetlist* netlistp) {
        // Assign final activity numbers
        uint32_t nFlags = SLOW_FLAG + 1;
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            TraceFlagVertex* const vtxp = vtx.cast<TraceFlagVertex>();
            if (!vtxp) continue;
            vtxp->activityCode(vtxp->slow() ? SLOW_FLAG : nFlags++);
        }
        V3Stats::addStat("Tracing, Activity flags", nFlags);

        // Create the activity flags array in the root scope
        AstVarScope* const vscp = [&]() {
            AstTopScope* const topScopep = netlistp->topScopep();
            FileLine* const flp = topScopep->fileline();
            AstNodeDType* const elemDtp = netlistp->findBitDType();
            AstRange* const rangep = new AstRange{flp, VNumRange{static_cast<int>(nFlags) - 1, 0}};
            AstNodeDType* const arrDtp = new AstUnpackArrayDType{flp, elemDtp, rangep};
            netlistp->typeTablep()->addTypesp(arrDtp);
            AstVarScope* const vscp = topScopep->createTemp("__Vactivity", arrDtp);
            netlistp->activityp(vscp->varp());
            return vscp;
        }();

        // Insert activity setters into the code
        for (const V3GraphVertex& vtx : m_graph.vertices()) {
            const TraceFlagVertex* const vtxp = vtx.cast<const TraceFlagVertex>();
            if (!vtxp) continue;

            // The insertion point
            AstNode* const insertp = vtxp->insertp();

            // The setter to insert
            AstNodeStmt* const setterp = [&]() -> AstNodeStmt* {
                FileLine* const flp = insertp->fileline();
                const uint32_t code = vtxp->activityCode();

                AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::WRITE};
                AstConst* const onep = new AstConst{flp, AstConst::BitTrue{}};

                if (code == SLOW_FLAG) {
                    // Just set all flags in slow code as it should be rare
                    ++m_statSettersSlow;
                    AstCMethodHard* const callp
                        = new AstCMethodHard{flp, refp, VCMethod::UNPACKED_FILL, onep};
                    callp->dtypeSetVoid();
                    return callp->makeStmt();
                }

                // Set this activity flag
                ++m_statSettersFast;
                AstNodeExpr* const lhsp = new AstArraySel{flp, refp, static_cast<int>(code)};
                return new AstAssign{flp, lhsp, onep};
            }();

            // Insert the setter into the code
            if (AstStmtExpr* const stmtp = VN_CAST(insertp, StmtExpr)) {
                stmtp->addHereThisAsNext(setterp);
            } else if (AstCFunc* const funcp = VN_CAST(insertp, CFunc)) {
                // The function writes a variable, so should have statements that do so ...
                UASSERT_OBJ(funcp->stmtsp(), funcp, "Empty function with activity flag");
                // Insert at the start, so an early return does not skip it
                funcp->stmtsp()->addHereThisAsNext(setterp);
                // If there are awaits, insert the setter after each await
                if (funcp->isCoroutine()) {
                    funcp->stmtsp()->foreachAndNext([setterp](AstCAwait* awaitp) {
                        awaitp->addNextHere(setterp->cloneTree(false));
                    });
                }
            } else {
                insertp->v3fatalSrc("Bad trace flag vertex");
            }
        }
    }

    // Assign the activity set of each signal. An empty set means the signal never changes.
    void createActivitySets(AstNetlist* netlistp) {
        // Index of each distinct activity set in the netlist
        std::map<std::vector<uint32_t>, uint32_t> actSetIdxs;
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            TraceVarVertex* const vtxp = vtx.cast<TraceVarVertex>();
            if (!vtxp) continue;

            // Activity set of this variable
            std::vector<uint32_t> actSet = [&]() -> std::vector<uint32_t> {
                if (vtxp->always()) return {EVAL_FLAG};
                // Flags of the fast flag vertices reaching the variable. These are distinct,
                // as there is at most one edge from each flag vertex.
                std::vector<uint32_t> flags;
                bool anySlow = false;
                for (const V3GraphEdge& edge : vtxp->inEdges()) {
                    const TraceFlagVertex* const flagVtxp = edge.fromp()->as<TraceFlagVertex>();
                    if (flagVtxp->activityCode() == SLOW_FLAG) {
                        anySlow = true;
                    } else {
                        flags.push_back(flagVtxp->activityCode());
                    }
                }
                // Slow code sets all flags, so the slow flag is only needed if there are no fast
                // writers
                if (flags.empty() && anySlow) return {SLOW_FLAG};
                // Use the computed flags - might be empty, means never changes (constant)
                std::sort(flags.begin(), flags.end());
                return flags;
            }();

            // Record the set if new
            const auto pair = actSetIdxs.emplace(actSet, 0);
            if (pair.second) pair.first->second = netlistp->addActSet(std::move(actSet));
            // Assign the index to the variable
            vtxp->actSetIdx(pair.first->second);
        }

        // Each signal takes the activity set of the variable it reads
        netlistp->topScopep()->rtmdp()->foreach([&](AstRtmdVar* sigp) {
            if (!sigp->traced()) return;
            sigp->actSetIdx(getVarVertexp(sigp->vscp())->actSetIdx());
        });
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Create the variable vertices, only for variables referenced by an AstRtmdVar
        createVarVertices(nodep);

        // Build the rest of the graph
        iterateChildren(nodep);

        // Simplify the graph
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("trace_built");
        graphSimplify();
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixed("trace_simplified");

        // Create the fine grained activity flags
        createActivityFlags(nodep);

        // Assign activity sets to signals
        createActivitySets(nodep);
    }

    void visit(AstRtmdHier*) override {}  // Walked separately in createVarVertices

    void visit(AstStmtExpr* nodep) override {
        iterateChildren(nodep);

        // Already processed as part of preceding StmtExpr
        if (nodep->user2()) return;

        // Process the CCall
        if (!VN_IS(nodep->exprp(), CCall)) return;

        // Gather the run of consecutive CCall statements. They all share the same activity
        // code, which is slow if all calls are.
        std::vector<TraceCFuncVertex*> funcVtxps;
        bool slow = true;
        for (AstNode* const currp : VNList<AstNode>{nodep}) {
            AstStmtExpr* const stmtp = VN_CAST(currp, StmtExpr);
            if (!stmtp) break;
            AstCCall* const ccallp = VN_CAST(stmtp->exprp(), CCall);
            if (!ccallp) break;
            stmtp->user2(true);  // Processed here, skip when visiting
            funcVtxps.push_back(getCFuncVertexp(ccallp->funcp()));
            slow &= ccallp->funcp()->slow();
        }

        // Create the flag vertex for this run of calls
        TraceFlagVertex* const flagVtxp = new TraceFlagVertex{&m_graph, nodep, slow};
        for (TraceCFuncVertex* const funcVtxp : funcVtxps) {
            new V3GraphEdge{&m_graph, flagVtxp, funcVtxp, 1};
        }
    }

    void visit(AstCFunc* nodep) override {
        V3GraphVertex* const funcVtxp = getCFuncVertexp(nodep);
        // If it can be entered from outside the model (public, DPI export, entry point or
        // coroutine), it needs its own activity point for the writes directly in this func
        if (nodep->funcPublic() || nodep->dpiExportImpl() || nodep->entryPoint()
            || nodep->isCoroutine()) {
            // Cannot treat a coroutine as slow, it may be resumed later
            const bool slow = nodep->slow() && !nodep->isCoroutine();
            TraceFlagVertex* const flagVtxp = new TraceFlagVertex{&m_graph, nodep, slow};
            new V3GraphEdge{&m_graph, flagVtxp, funcVtxp, 1};
        }
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstVarRef* nodep) override {
        if (!m_cfuncp || !nodep->access().isWriteOrRW()) return;
        // Record writes
        addWriteEdge(nodep->varScopep());
    }

    void visit(AstMemberRef* nodep) override {
        iterateChildren(nodep);

        // Record writes through virtual interface handles
        if (!m_cfuncp || !nodep->access().isWriteOrRW()) return;
        AstIfaceRefDType* const dtypep
            = VN_CAST(nodep->fromp()->dtypep()->skipRefp(), IfaceRefDType);
        if (!dtypep || !dtypep->isVirtual()) return;  // Not virtual interface handle
        const std::vector<AstVarScope*>* const vscpsp = m_ifaceMemberVscps.tryGet(nodep->varp());
        if (!vscpsp) return;  // Not a traced signal
        for (AstVarScope* const vscp : *vscpsp) addWriteEdge(vscp);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TraceVisitor(AstNetlist* nodep) {
        iterate(nodep);
        V3Stats::addStat("Tracing, Activity setters fast", m_statSettersFast);
        V3Stats::addStat("Tracing, Activity setters slow", m_statSettersSlow);
        V3Stats::addStat("Tracing, Activity sets", nodep->actSets().size());
        V3Stats::addStat("Tracing, Traced signals", m_statSignals);
    }
};

//######################################################################
// Trace class functions

void V3Trace::traceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { TraceVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("trace", 0, dumpTreeEitherLevel() >= 3);
}
