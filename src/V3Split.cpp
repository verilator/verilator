// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements to reduce temps
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
// V3Split implements two separate transformations:
//  splitAlwaysAll() splits large always blocks into smaller always blocks
//  when possible (but does not change the order of statements relative
//  to one another.)
//
//  splitReorderAll() reorders statements within individual blocks
//  to avoid delay vars when possible. It no longer splits always blocks.
//
// Both use a common base class, and common graph-building code to reflect
// data dependencies within an always block (the "scoreboard".)
//
// The scoreboard tracks data deps as follows:
//
//      ALWAYS
//              ASSIGN ({var} <= {cons})
//              Record as generating var_DLY (independent of use of var), consumers
//              ASSIGN ({var} = {cons}
//              Record generator and consumer
//      Any var that is only consumed can be ignored.
//      Then we split into separate ALWAYS blocks.
//
// The scoreboard includes innards of if/else nodes also.  Splitting is no
// longer limited to top-level statements, we can split within if-else
// blocks. We want to be able to split this:
//
//    always @ (...) begin
//      if (reset) begin
//        a <= 0;
//        b <= 0;
//         // ... ten thousand more
//      end
//      else begin
//        a <= a_in;
//        b <= b_in;
//         // ... ten thousand more
//      end
//    end
//
// ...into a separate block for each of a, b, and so on.  Even though this
// requires duplicating the conditional many times, it's usually
// better. Later modules (V3Gate, V3Order) run faster if they aren't
// handling enormous blocks with long lists of inputs and outputs.
//
// Furthermore, the optional reorder routine can optimize this:
//      NODEASSIGN/NODEIF/WHILE
//              S1: ASSIGN {v1} <= 0.   // Duplicate of below
//              S2: ASSIGN {v1} <= {v0}
//              S3: IF (...,
//                      X1: ASSIGN {v2} <= {v1}
//                      X2: ASSIGN {v3} <= {v2}
//      We'd like to swap S2 and S3, and X1 and X2.
//
//  Create a graph in split assignment order.
//      v3 -breakable-> v3Dly --> X2 --> v2 -brk-> v2Dly -> X1 -> v1
//      Likewise on each "upper" statement vertex
//              v3Dly & v2Dly -> S3 -> v1 & v2
//              v1 -brk-> v1Dly -> S2 -> v0
//                        v1Dly -> S1 -> {empty}
//  Multiple assignments to the same variable must remain in order
//
//  Also vars must not be "public" and we also scoreboard nodep->isPure()
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Split.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3Graph.h"

#include <algorithm>
#include <cstdarg>
#include <map>
#include <vector>
#include VL_INCLUDE_UNORDERED_MAP
#include VL_INCLUDE_UNORDERED_SET

//######################################################################
// Support classes

class SplitNodeVertex : public V3GraphVertex {
    AstNode*    m_nodep;
protected:
    SplitNodeVertex(V3Graph* graphp, AstNode* nodep)
        : V3GraphVertex(graphp), m_nodep(nodep) {}
    virtual ~SplitNodeVertex() {}
    // ACCESSORS
    // Do not make accessor for nodep(),  It may change due to
    // reordering a lower block, but we don't repair it
    virtual string name() const {
        return cvtToHex(m_nodep) + ' ' + m_nodep->prettyTypeName();
    }
    virtual FileLine* fileline() const { return nodep()->fileline(); }
public:
    virtual AstNode* nodep() const { return m_nodep; }
};

class SplitPliVertex : public SplitNodeVertex {
public:
    explicit SplitPliVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex(graphp, nodep) {}
    virtual ~SplitPliVertex() {}
    virtual string name() const { return "*PLI*"; }
    virtual string dotColor() const { return "green"; }
};

class SplitLogicVertex : public SplitNodeVertex {
public:
    SplitLogicVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex(graphp, nodep) {}
    virtual ~SplitLogicVertex() {}
    virtual string dotColor() const { return "yellow"; }
};

class SplitVarStdVertex : public SplitNodeVertex {
public:
    SplitVarStdVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex(graphp, nodep) {}
    virtual ~SplitVarStdVertex() {}
    virtual string dotColor() const { return "skyblue"; }
};

class SplitVarPostVertex : public SplitNodeVertex {
public:
    SplitVarPostVertex(V3Graph* graphp, AstNode* nodep)
        : SplitNodeVertex(graphp, nodep) {}
    virtual ~SplitVarPostVertex() {}
    virtual string name() const { return string("POST ")+SplitNodeVertex::name(); }
    virtual string dotColor() const { return "CadetBlue"; }
};

//######################################################################
// Edge types

class SplitEdge : public V3GraphEdge {
    uint32_t m_ignoreInStep;  // Step number that if set to, causes this edge to be ignored
    static uint32_t s_stepNum;  // Global step number
protected:
    enum { WEIGHT_NORMAL = 10 };
    SplitEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
                int weight, bool cutable=CUTABLE)
        : V3GraphEdge(graphp, fromp, top, weight, cutable)
        , m_ignoreInStep(0) {}
    virtual ~SplitEdge() {}
public:
    // Iterator for graph functions
    static void incrementStep() { ++s_stepNum; }
    bool ignoreThisStep() const { return m_ignoreInStep == s_stepNum; }
    void setIgnoreThisStep() { m_ignoreInStep = s_stepNum; }
    virtual bool followScoreboard() const = 0;
    static bool followScoreboard(const V3GraphEdge* edgep) {
        const SplitEdge* oedgep = dynamic_cast<const SplitEdge*>(edgep);
        if (!oedgep) v3fatalSrc("Following edge of non-SplitEdge type");
        if (oedgep->ignoreThisStep()) return false;
        return oedgep->followScoreboard();
    }
    static bool followCyclic(const V3GraphEdge* edgep) {
        const SplitEdge* oedgep = dynamic_cast<const SplitEdge*>(edgep);
        if (!oedgep) v3fatalSrc("Following edge of non-SplitEdge type");
        return (!oedgep->ignoreThisStep());
    }
    virtual string dotStyle() const {
        return ignoreThisStep() ? "dotted" : V3GraphEdge::dotStyle();
    }
};
uint32_t        SplitEdge::s_stepNum = 0;

class SplitPostEdge : public SplitEdge {
public:
    SplitPostEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitPostEdge() {}
    virtual bool followScoreboard() const { return false; }
    virtual string dotColor() const { return "khaki"; }
};

class SplitLVEdge : public SplitEdge {
public:
    SplitLVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitLVEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "yellowGreen"; }
};

class SplitRVEdge : public SplitEdge {
public:
    SplitRVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitRVEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "green"; }
};

struct SplitScorebdEdge : public SplitEdge {
public:
    SplitScorebdEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitScorebdEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "blue"; }
};

struct SplitStrictEdge : public SplitEdge {
    // A strict order, based on the original statement order in the graph
    // The only non-cutable edge type
public:
    SplitStrictEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
        : SplitEdge(graphp, fromp, top, WEIGHT_NORMAL, NOT_CUTABLE) {}
    virtual ~SplitStrictEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "blue"; }
};

//######################################################################
// Split class functions

class SplitReorderBaseVisitor : public AstNVisitor {
private:
    // NODE STATE
    // AstVarScope::user1p      -> Var SplitNodeVertex* for usage var, 0=not set yet
    // AstVarScope::user2p      -> Var SplitNodeVertex* for delayed assignment var, 0=not set yet
    // Ast*::user3p             -> Statement SplitLogicVertex* (temporary only)
    // Ast*::user4              -> Current ordering number (reorderBlock usage)
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;
    AstUser3InUse       m_inuser3;
    AstUser4InUse       m_inuser4;

protected:
    // TYPES
    typedef std::vector<SplitLogicVertex*> VStack;

    // STATE
    string              m_noReorderWhy;  // Reason we can't reorder
    VStack              m_stmtStackps;  // Current statements being tracked
    SplitPliVertex*     m_pliVertexp;   // Element specifying PLI ordering
    V3Graph             m_graph;        // Scoreboard of var usages/dependencies
    bool                m_inDly;        // Inside ASSIGNDLY
    VDouble0            m_statSplits;   // Statistic tracking

    // CONSTRUCTORS
public:
    SplitReorderBaseVisitor() {
        scoreboardClear();
    }
    virtual ~SplitReorderBaseVisitor() {
        V3Stats::addStat("Optimizations, Split always", m_statSplits);
    }

    // METHODS
protected:
    VL_DEBUG_FUNC;  // Declare debug()

    void scoreboardClear() {
        //VV*****  We reset user1p() and user2p on each block!!!
        m_inDly = false;
        m_graph.clear();
        m_stmtStackps.clear();
        m_pliVertexp = NULL;
        m_noReorderWhy = "";
        AstNode::user1ClearTree();
        AstNode::user2ClearTree();
        AstNode::user3ClearTree();
        AstNode::user4ClearTree();
    }

private:
    void scoreboardPli(AstNode* nodep) {
        // Order all PLI statements with other PLI statements
        // This ensures $display's and such remain in proper order
        // We don't prevent splitting out other non-pli statements, however.
        if (!m_pliVertexp) {
            m_pliVertexp = new SplitPliVertex(&m_graph, nodep);  // m_graph.clear() will delete it
        }
        for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
            // Both ways...
            new SplitScorebdEdge(&m_graph, *it, m_pliVertexp);
            new SplitScorebdEdge(&m_graph, m_pliVertexp, *it);
        }
    }
    void scoreboardPushStmt(AstNode* nodep) {
        //UINFO(9,"    push "<<nodep<<endl);
        SplitLogicVertex* vertexp = new SplitLogicVertex(&m_graph, nodep);
        m_stmtStackps.push_back(vertexp);
        UASSERT_OBJ(!nodep->user3p(), nodep, "user3p should not be used; cleared in processBlock");
        nodep->user3p(vertexp);
    }
    void scoreboardPopStmt() {
        //UINFO(9,"    pop"<<endl);
        if (m_stmtStackps.empty()) v3fatalSrc("Stack underflow");
        m_stmtStackps.pop_back();
    }

protected:
    void scanBlock(AstNode* nodep) {
        // Iterate across current block, making the scoreboard
        for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
            scoreboardPushStmt(nextp);
            iterate(nextp);
            scoreboardPopStmt();
        }
    }

    void pruneDepsOnInputs() {
        for (V3GraphVertex* vertexp = m_graph.verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            if (!vertexp->outBeginp()
                && dynamic_cast<SplitVarStdVertex*>(vertexp)) {
                if (debug() >= 9) {
                    SplitVarStdVertex* stdp = static_cast<SplitVarStdVertex*>(vertexp);
                    UINFO(0, "Will prune deps on var "<<stdp->nodep()<<endl);
                    stdp->nodep()->dumpTree(cout, "- ");
                }
                for (V3GraphEdge* edgep = vertexp->inBeginp();
                     edgep; edgep=edgep->inNextp()) {
                    SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
                    oedgep->setIgnoreThisStep();
                }
            }
        }
    }

    virtual void makeRvalueEdges(SplitVarStdVertex* vstdp) = 0;

    // VISITORS
    virtual void visit(AstAlways* nodep) VL_OVERRIDE = 0;
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE = 0;

    // We don't do AstNodeFor/AstWhile loops, due to the standard question
    // of what is before vs. after

    virtual void visit(AstAssignDly* nodep) VL_OVERRIDE {
        m_inDly = true;
        UINFO(4,"    ASSIGNDLY "<<nodep<<endl);
        iterateChildren(nodep);
        m_inDly = false;
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (!m_stmtStackps.empty()) {
            AstVarScope* vscp = nodep->varScopep();
            UASSERT_OBJ(vscp, nodep, "Not linked");
            if (!nodep->varp()->isConst()) {  // Constant lookups can be ignored
                // ---
                // NOTE: Formerly at this location we would avoid
                // splitting or reordering if the variable is public.
                //
                // However, it should be perfectly safe to split an
                // always block containing a public variable.
                // Neither operation should perturb PLI's view of
                // the variable.
                //
                // Former code:
                //
                //   if (nodep->varp()->isSigPublic()) {
                //       // Public signals shouldn't be changed,
                //       // pli code might be messing with them
                //       scoreboardPli(nodep);
                //   }
                // ---

                // Create vertexes for variable
                if (!vscp->user1p()) {
                    SplitVarStdVertex* vstdp = new SplitVarStdVertex(&m_graph, vscp);
                    vscp->user1p(vstdp);
                }
                SplitVarStdVertex* vstdp = reinterpret_cast<SplitVarStdVertex*>(vscp->user1p());

                // SPEEDUP: We add duplicate edges, that should be fixed
                if (m_inDly && nodep->lvalue()) {
                    UINFO(4,"     VARREFDLY: "<<nodep<<endl);
                    // Delayed variable is different from non-delayed variable
                    if (!vscp->user2p()) {
                        SplitVarPostVertex* vpostp = new SplitVarPostVertex(&m_graph, vscp);
                        vscp->user2p(vpostp);
                        new SplitPostEdge(&m_graph, vstdp, vpostp);
                    }
                    SplitVarPostVertex* vpostp
                        = reinterpret_cast<SplitVarPostVertex*>(vscp->user2p());
                    // Add edges
                    for (VStack::iterator it = m_stmtStackps.begin();
                         it != m_stmtStackps.end(); ++it) {
                        new SplitLVEdge(&m_graph, vpostp, *it);
                    }
                } else {  // Nondelayed assignment
                    if (nodep->lvalue()) {
                        // Non-delay; need to maintain existing ordering
                        // with all consumers of the signal
                        UINFO(4,"     VARREFLV: "<<nodep<<endl);
                        for (VStack::iterator it = m_stmtStackps.begin();
                             it != m_stmtStackps.end(); ++it) {
                            new SplitLVEdge(&m_graph, vstdp, *it);
                        }
                    } else {
                        UINFO(4,"     VARREF:   "<<nodep<<endl);
                        makeRvalueEdges(vstdp);
                    }
                }
            }
        }
    }

    virtual void visit(AstJumpGo* nodep) VL_OVERRIDE {
        // Jumps will disable reordering at all levels
        // This is overly pessimistic; we could treat jumps as barriers, and
        // reorder everything between jumps/labels, however jumps are rare
        // in always, so the performance gain probably isn't worth the work.
        UINFO(9,"         NoReordering "<<nodep<<endl);
        m_noReorderWhy = "JumpGo";
        iterateChildren(nodep);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // **** SPECIAL default type that sets PLI_ORDERING
        if (!m_stmtStackps.empty() && !nodep->isPure()) {
            UINFO(9,"         NotSplittable "<<nodep<<endl);
            scoreboardPli(nodep);
        }
        iterateChildren(nodep);
    }

private:
    VL_UNCOPYABLE(SplitReorderBaseVisitor);
};

class ReorderVisitor : public SplitReorderBaseVisitor {
    // CONSTRUCTORS
public:
    explicit ReorderVisitor(AstNetlist* nodep) {
        iterate(nodep);
    }
    virtual ~ReorderVisitor() {}

    // METHODS
protected:
    virtual void makeRvalueEdges(SplitVarStdVertex* vstdp) VL_OVERRIDE {
        for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
            new SplitRVEdge(&m_graph, *it, vstdp);
        }
    }

    void cleanupBlockGraph(AstNode* nodep) {
        // Transform the graph into what we need
        UINFO(5, "ReorderBlock "<<nodep<<endl);
        m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

        if (debug()>=9) {
            m_graph.dumpDotFilePrefixed("reorderg_nodup", false);
            //m_graph.dump(); cout<<endl;
        }

        // Mark all the logic for this step
        // Vertex::m_user begin: true indicates logic for this step
        m_graph.userClearVertices();
        for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
            SplitLogicVertex* vvertexp = reinterpret_cast<SplitLogicVertex*>(nextp->user3p());
            vvertexp->user(true);
        }

        // If a var vertex has only inputs, it's a input-only node,
        // and can be ignored for coloring **this block only**
        SplitEdge::incrementStep();
        pruneDepsOnInputs();

        // For reordering this single block only, mark all logic
        // vertexes not involved with this step as unimportant
        for (V3GraphVertex* vertexp = m_graph.verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            if (SplitLogicVertex* vvertexp = dynamic_cast<SplitLogicVertex*>(vertexp)) {
                if (!vvertexp->user()) {
                    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
                        SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
                        oedgep->setIgnoreThisStep();
                    }
                    for (V3GraphEdge* edgep = vertexp->outBeginp();
                         edgep; edgep=edgep->outNextp()) {
                        SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
                        oedgep->setIgnoreThisStep();
                    }
                }
            }
        }

        // Weak coloring to determine what needs to remain in order
        // This follows all step-relevant edges excluding PostEdges, which are done later
        m_graph.weaklyConnected(&SplitEdge::followScoreboard);

        // Add hard orderings between all nodes of same color, in the order they appeared
        vl_unordered_map<uint32_t, SplitLogicVertex*> lastOfColor;
        for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
            SplitLogicVertex* vvertexp = reinterpret_cast<SplitLogicVertex*>(nextp->user3p());
            uint32_t color = vvertexp->color();
            UASSERT_OBJ(color, nextp, "No node color assigned");
            if (lastOfColor[color]) {
                new SplitStrictEdge(&m_graph, lastOfColor[color], vvertexp);
            }
            lastOfColor[color] = vvertexp;
        }

        // And a real ordering to get the statements into something reasonable
        // We don't care if there's cutable violations here...
        // Non-cutable violations should be impossible; as those edges are program-order
        if (debug()>=9) m_graph.dumpDotFilePrefixed(string("splitg_preo"), false);
        m_graph.acyclic(&SplitEdge::followCyclic);
        m_graph.rank(&SplitEdge::followCyclic);  // Or order(), but that's more expensive
        if (debug()>=9) m_graph.dumpDotFilePrefixed(string("splitg_opt"), false);
    }

    void reorderBlock(AstNode* nodep) {
        // Reorder statements in the completed graph

        // Map the rank numbers into nodes they associate with
        typedef std::multimap<uint32_t,AstNode*> RankNodeMap;
        RankNodeMap rankMap;
        int currOrder = 0;  // Existing sequence number of assignment
        for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
            SplitLogicVertex* vvertexp = reinterpret_cast<SplitLogicVertex*>(nextp->user3p());
            rankMap.insert(make_pair(vvertexp->rank(), nextp));
            nextp->user4(++currOrder);  // Record current ordering
        }

        // Is the current ordering OK?
        bool leaveAlone = true;
        int newOrder = 0;  // New sequence number of assignment
        for (RankNodeMap::const_iterator it = rankMap.begin();
             it != rankMap.end(); ++it) {
            AstNode* nextp = it->second;
            if (++newOrder != nextp->user4()) leaveAlone = false;
        }
        if (leaveAlone) {
            UINFO(6,"   No changes\n");
        } else {
            AstNRelinker replaceHandle;  // Where to add the list
            AstNode* newListp = NULL;
            for (RankNodeMap::const_iterator it = rankMap.begin(); it != rankMap.end(); ++it) {
                AstNode* nextp = it->second;
                UINFO(6, "   New order: "<<nextp<<endl);
                if (nextp == nodep) nodep->unlinkFrBack(&replaceHandle);
                else nextp->unlinkFrBack();
                if (newListp) newListp = newListp->addNext(nextp);
                else newListp = nextp;
            }
            replaceHandle.relink(newListp);
        }
    }

    void processBlock(AstNode* nodep) {
        if (!nodep) return;  // Empty lists are ignorable
        // Pass the first node in a list of block items, we'll process them
        // Check there's >= 2 sub statements, else nothing to analyze
        // Save recursion state
        AstNode* firstp = nodep;  // We may reorder, and nodep is no longer first.
        void* oldBlockUser3 = nodep->user3p();  // May be overloaded in below loop, save it
        nodep->user3p(NULL);
        UASSERT_OBJ(nodep->firstAbovep(), nodep,
                    "Node passed is in next list; should have processed all list at once");
        // Process it
        if (!nodep->nextp()) {
            // Just one, so can't reorder.  Just look for more blocks/statements.
            iterate(nodep);
        } else {
            UINFO(9,"  processBlock "<<nodep<<endl);
            // Process block and followers
            scanBlock(nodep);
            if (m_noReorderWhy != "") {  // Jump or something nasty
                UINFO(9,"  NoReorderBlock because "<<m_noReorderWhy<<endl);
            } else {
                // Reorder statements in this block
                cleanupBlockGraph(nodep);
                reorderBlock(nodep);
                // Delete old vertexes and edges only applying to this block
                // First, walk back to first in list
                while (firstp->backp()->nextp()==firstp) firstp = firstp->backp();
                for (AstNode* nextp=firstp; nextp; nextp=nextp->nextp()) {
                    SplitLogicVertex* vvertexp
                        = reinterpret_cast<SplitLogicVertex*>(nextp->user3p());
                    vvertexp->unlinkDelete(&m_graph);
                }
            }
        }
        // Again, nodep may no longer be first.
        firstp->user3p(oldBlockUser3);
    }

    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        UINFO(4,"   ALW   "<<nodep<<endl);
        if (debug()>=9) nodep->dumpTree(cout, "   alwIn:: ");
        scoreboardClear();
        processBlock(nodep->bodysp());
        if (debug()>=9) nodep->dumpTree(cout, "   alwOut: ");
    }

    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        UINFO(4,"     IF "<<nodep<<endl);
        iterateAndNextNull(nodep->condp());
        processBlock(nodep->ifsp());
        processBlock(nodep->elsesp());
    }
private:
    VL_UNCOPYABLE(ReorderVisitor);
};

typedef vl_unordered_set<uint32_t> ColorSet;
typedef std::vector<AstAlways*> AlwaysVec;

class IfColorVisitor : public AstNVisitor {
    // MEMBERS
    ColorSet m_colors;  // All colors in the original always block

    typedef std::vector<AstNodeIf*> IfStack;
    IfStack m_ifStack;  // Stack of nested if-statements we're currently processing

    typedef vl_unordered_map<AstNodeIf*, ColorSet> IfColorMap;
    IfColorMap m_ifColors;  // Map each if-statement to the set of colors (split blocks)
    // that will get a copy of that if-statement

    // CONSTRUCTORS
public:
    // Visit through *nodep and map each AstNodeIf within to the set of
    // colors it will participate in. Also find the whole set of colors.
    explicit IfColorVisitor(AstAlways* nodep) {
        iterate(nodep);
    }
    virtual ~IfColorVisitor() {}

    // METHODS
    const ColorSet& colors() const { return m_colors; }
    const ColorSet& colors(AstNodeIf* nodep) const {
        IfColorMap::const_iterator it = m_ifColors.find(nodep);
        UASSERT_OBJ(it != m_ifColors.end(), nodep, "Node missing from split color() map");
        return it->second;
    }

private:
    void trackNode(AstNode* nodep) {
        if (nodep->user3p()) {
            SplitLogicVertex* vertexp = reinterpret_cast<SplitLogicVertex*>(nodep->user3p());
            uint32_t color = vertexp->color();
            m_colors.insert(color);
            UINFO(8, "  SVL " << vertexp << " has color " << color << "\n");

            // Record that all containing ifs have this color.
            for (IfStack::const_iterator it = m_ifStack.begin();
                 it != m_ifStack.end(); ++it) {
                m_ifColors[*it].insert(color);
            }
        }
    }

protected:
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        m_ifStack.push_back(nodep);
        trackNode(nodep);
        iterateChildren(nodep);
        m_ifStack.pop_back();
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        trackNode(nodep);
        iterateChildren(nodep);
    }

    VL_DEBUG_FUNC;  // Declare debug()
private:
    VL_UNCOPYABLE(IfColorVisitor);
};

class EmitSplitVisitor : public AstNVisitor {
    // MEMBERS
    AstAlways* m_origAlwaysp;  // Block that *this will split
    const IfColorVisitor* m_ifColorp;  // Digest of results of prior coloring

    // Map each color to our current place within the color's new always
    typedef vl_unordered_map<uint32_t, AstNode*> LocMap;
    LocMap m_addAfter;

    AlwaysVec* m_newBlocksp;  // Split always blocks we have generated

    // CONSTRUCTORS
public:
    // EmitSplitVisitor visits through always block *nodep
    // and generates its split blocks, writing the split blocks
    // into *newBlocksp.
    EmitSplitVisitor(AstAlways* nodep,
                     const IfColorVisitor* ifColorp,
                     AlwaysVec* newBlocksp)
        : m_origAlwaysp(nodep)
        , m_ifColorp(ifColorp)
        , m_newBlocksp(newBlocksp) {
        UINFO(6, "  splitting always " << nodep << endl);
    }

    virtual ~EmitSplitVisitor() {}

    // METHODS
    void go() {
        // Create a new always for each color
        const ColorSet& colors = m_ifColorp->colors();
        for (ColorSet::const_iterator color = colors.begin();
             color != colors.end(); ++color) {
            // We don't need to clone m_origAlwaysp->sensesp() here;
            // V3Activate already moved it to a parent node.
            AstAlways* alwaysp =
                new AstAlways(m_origAlwaysp->fileline(), VAlwaysKwd::ALWAYS,
                              NULL, NULL);
            // Put a placeholder node into stmtp to track our position.
            // We'll strip these out after the blocks are fully cloned.
            AstSplitPlaceholder* placeholderp = makePlaceholderp();
            alwaysp->addStmtp(placeholderp);
            m_addAfter[*color] = placeholderp;
            m_newBlocksp->push_back(alwaysp);
        }
        // Scan the body of the always. We'll handle if/else
        // specially, everything else is a leaf node that we can
        // just clone into one of the split always blocks.
        iterateAndNextNull(m_origAlwaysp->bodysp());
    }

protected:
    VL_DEBUG_FUNC;  // Declare debug()

    AstSplitPlaceholder* makePlaceholderp() {
        return new AstSplitPlaceholder(m_origAlwaysp->fileline());
    }

    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // Anything that's not an if/else we assume is a leaf
        // (that is, something we won't split.) Don't visit further
        // into the leaf.
        //
        // A leaf might contain another if, for example a WHILE loop
        // could contain an if. We can't split WHILE loops, so we
        // won't split its nested if either. Just treat it as part
        // of the leaf; do not visit further; do not reach visit(AstNodeIf*)
        // for such an embedded if.

        // Each leaf must have a user3p
        UASSERT_OBJ(nodep->user3p(), nodep, "null user3p in V3Split leaf");

        // Clone the leaf into its new always block
        SplitLogicVertex* vxp = reinterpret_cast<SplitLogicVertex*>(nodep->user3p());
        uint32_t color = vxp->color();
        AstNode* clonedp = nodep->cloneTree(false);
        m_addAfter[color]->addNextHere(clonedp);
        m_addAfter[color] = clonedp;
    }

    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        const ColorSet& colors = m_ifColorp->colors(nodep);
        typedef vl_unordered_map<uint32_t, AstNodeIf*> CloneMap;
        CloneMap clones;

        for (ColorSet::const_iterator color = colors.begin();
             color != colors.end(); ++color) {
            // Clone this if into its set of split blocks
            AstSplitPlaceholder* if_placeholderp = makePlaceholderp();
            AstSplitPlaceholder* else_placeholderp = makePlaceholderp();
            AstIf* clonep =
                new AstIf(nodep->fileline(),
                          nodep->condp()->cloneTree(true),
                          if_placeholderp,
                          else_placeholderp);
            AstIf* origp = VN_CAST(nodep, If);
            if (origp) {
                // Preserve pragmas from unique if's
                // so assertions work properly
                clonep->uniquePragma(origp->uniquePragma());
                clonep->unique0Pragma(origp->unique0Pragma());
                clonep->priorityPragma(origp->priorityPragma());
            }
            clones[*color] = clonep;
            m_addAfter[*color]->addNextHere(clonep);
            m_addAfter[*color] = if_placeholderp;
        }

        iterateAndNextNull(nodep->ifsp());

        for (ColorSet::const_iterator color = colors.begin();
             color != colors.end(); ++color) {
            m_addAfter[*color] = clones[*color]->elsesp();
        }

        iterateAndNextNull(nodep->elsesp());

        for (ColorSet::const_iterator color = colors.begin();
             color != colors.end(); ++color) {
            m_addAfter[*color] = clones[*color];
        }
    }

private:
    VL_UNCOPYABLE(EmitSplitVisitor);
};

class RemovePlaceholdersVisitor : public AstNVisitor {
    typedef vl_unordered_set<AstNode*> NodeSet;
    NodeSet m_removeSet;  // placeholders to be removed
public:
    explicit RemovePlaceholdersVisitor(AstNode* nodep) {
        iterate(nodep);
        for (NodeSet::const_iterator it = m_removeSet.begin();
             it != m_removeSet.end(); ++it) {
            AstNode* np = *it;
            np->unlinkFrBack();  // Without next
            VL_DO_DANGLING(np->deleteTree(), np);
        }
    }
    virtual ~RemovePlaceholdersVisitor() {}
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
    virtual void visit(AstSplitPlaceholder* nodep) VL_OVERRIDE {
        m_removeSet.insert(nodep);
    }
private:
    VL_UNCOPYABLE(RemovePlaceholdersVisitor);
};

class SplitVisitor : public SplitReorderBaseVisitor {
private:
    // Keys are original always blocks pending delete,
    // values are newly split always blocks pending insertion
    // at the same position as the originals:
    typedef vl_unordered_map<AstAlways*, AlwaysVec> ReplaceMap;
    ReplaceMap m_replaceBlocks;

    // AstNodeIf* whose condition we're currently visiting
    AstNode* m_curIfConditional;

    // CONSTRUCTORS
public:
    explicit SplitVisitor(AstNetlist* nodep)
        : m_curIfConditional(NULL) {
        iterate(nodep);

        // Splice newly-split blocks into the tree. Remove placeholders
        // from newly-split blocks. Delete the original always blocks
        // that we're replacing.
        for (ReplaceMap::iterator it = m_replaceBlocks.begin();
             it != m_replaceBlocks.end(); ++it) {
            AstAlways* origp = it->first;
            for (AlwaysVec::iterator addme = it->second.begin();
                 addme != it->second.end(); ++addme) {
                origp->addNextHere(*addme);
                RemovePlaceholdersVisitor removePlaceholders(*addme);
            }
            origp->unlinkFrBack();  // Without next
            VL_DO_DANGLING(origp->deleteTree(), origp);
        }
    }

    virtual ~SplitVisitor() {}

    // METHODS
protected:
    virtual void makeRvalueEdges(SplitVarStdVertex* vstdp) VL_OVERRIDE {
        // Each 'if' depends on rvalues in its own conditional ONLY,
        // not rvalues in the if/else bodies.
        for (VStack::const_iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
            AstNodeIf* ifNodep = VN_CAST((*it)->nodep(), NodeIf);
            if (ifNodep && (m_curIfConditional != ifNodep)) {
                continue;
            }
            new SplitRVEdge(&m_graph, *it, vstdp);
        }
    }

    void colorAlwaysGraph() {
        // Color the graph to indicate subsets, each of which
        // we can split into its own always block.
        m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

        // Some vars are primary inputs to the always block; prune
        // edges on those vars. Reasoning: if two statements both depend
        // on primary input A, it's ok to split these statements. Whereas
        // if they both depend on locally-generated variable B, the statements
        // must be kept together.
        SplitEdge::incrementStep();
        pruneDepsOnInputs();

        // For any 'if' node whose deps have all been pruned
        // (meaning, its conditional expression only looks at primary
        // inputs) prune all edges that depend on the 'if'.
        for (V3GraphVertex* vertexp = m_graph.verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            SplitLogicVertex* logicp = dynamic_cast<SplitLogicVertex*>(vertexp);
            if (!logicp) continue;

            AstNodeIf* ifNodep = VN_CAST(logicp->nodep(), NodeIf);
            if (!ifNodep) continue;

            bool pruneMe = true;
            for (V3GraphEdge* edgep = logicp->outBeginp();
                 edgep; edgep = edgep->outNextp()) {
                SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
                if (!oedgep->ignoreThisStep()) {
                    // This if conditional depends on something we can't
                    // prune -- a variable generated in the current block.
                    pruneMe = false;

                    // When we can't prune dependencies on the conditional,
                    // give a hint about why...
                    if (debug() >= 9) {
                        V3GraphVertex* vxp = oedgep->top();
                        SplitNodeVertex* nvxp = dynamic_cast<SplitNodeVertex*>(vxp);
                        UINFO(0, "Cannot prune if-node due to edge "<<oedgep<<
                              " pointing to node "<<nvxp->nodep()<<endl);
                        nvxp->nodep()->dumpTree(cout, "- ");
                    }

                    break;
                }
            }

            if (!pruneMe) continue;

            // This if can be split; prune dependencies on it.
            for (V3GraphEdge* edgep = logicp->inBeginp();
                 edgep; edgep = edgep->inNextp()) {
                SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
                oedgep->setIgnoreThisStep();
            }
        }

        if (debug()>=9) m_graph.dumpDotFilePrefixed("splitg_nodup", false);

        // Weak coloring to determine what needs to remain grouped
        // in a single always. This follows all edges excluding:
        //  - those we pruned above
        //  - PostEdges, which are done later
        m_graph.weaklyConnected(&SplitEdge::followScoreboard);
        if (debug()>=9) m_graph.dumpDotFilePrefixed("splitg_colored", false);
    }

    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        // build the scoreboard
        scoreboardClear();
        scanBlock(nodep->bodysp());

        if (m_noReorderWhy != "") {
            // We saw a jump or something else rare that we don't handle.
            UINFO(9,"  NoSplitBlock because "<<m_noReorderWhy<<endl);
            return;
        }

        // Look across the entire tree of if/else blocks in the always,
        // and color regions that must be kept together.
        UINFO(5, "SplitVisitor @ "<<nodep<<endl);
        colorAlwaysGraph();

        // Map each AstNodeIf to the set of colors (split always blocks)
        // it must participate in. Also find the whole set of colors.
        IfColorVisitor ifColor(nodep);

        if (ifColor.colors().size() > 1) {
            // Counting original always blocks rather than newly-split
            // always blocks makes it a little easier to use this stat to
            // check the result of the t_alw_split test:
            ++m_statSplits;

            // Visit through the original always block one more time,
            // and emit the split always blocks into m_replaceBlocks:
            EmitSplitVisitor emitSplit(nodep, &ifColor,
                                       &(m_replaceBlocks[nodep]));
            emitSplit.go();
        }
    }
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        UINFO(4,"     IF "<<nodep<<endl);
        m_curIfConditional = nodep;
        iterateAndNextNull(nodep->condp());
        m_curIfConditional = NULL;
        scanBlock(nodep->ifsp());
        scanBlock(nodep->elsesp());
    }
private:
    VL_UNCOPYABLE(SplitVisitor);
};

//######################################################################
// Split class functions

void V3Split::splitReorderAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ReorderVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("reorder", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
void V3Split::splitAlwaysAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        SplitVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("split", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
