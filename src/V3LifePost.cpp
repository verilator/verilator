// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AssignPost Variable assignment elimination
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
// LIFE TRANSFORMATIONS:
//      Build control-flow graph with assignments and var usages
//      All modules:
//          Delete these
//              ASSIGN(Vdly, a)
//              ... {no reads or writes of a after the first write to Vdly}
//              ... {no reads of a after the first write to Vdly}
//              ASSIGNPOST(Vdly, tmp)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3PartitionGraph.h"
#include "V3GraphPathChecker.h"
#include "V3LifePost.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <cstdarg>
#include <memory>  // for vl_unique_ptr -> auto_ptr or unique_ptr
#include VL_INCLUDE_UNORDERED_MAP

//######################################################################
// LifePost class functions

class LifePostElimVisitor : public AstNVisitor {
private:
    bool        m_tracingCall;  // Iterating into a CCall to a CFunc

    // NODE STATE
    // INPUT:
    //  AstVarScope::user4p()   -> AstVarScope*, If set, replace this
    //                             varscope with specified new one
    // STATE
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        AstVarScope* vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");
        if (AstVarScope* newvscp = reinterpret_cast<AstVarScope*>(vscp->user4p())) {
            UINFO(9, "  Replace "<<nodep<<" to "<<newvscp<<endl);
            AstVarRef* newrefp = new AstVarRef(nodep->fileline(), newvscp, nodep->lvalue());
            nodep->replaceWith(newrefp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Only track the top scopes, not lower level functions
        if (nodep->isTop()) iterateChildren(nodep);
    }
    virtual void visit(AstNodeCCall* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (!nodep->funcp()->entryPoint()) {
            // Enter the function and trace it
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    virtual void visit(AstExecGraph* nodep) VL_OVERRIDE {
        // Can just iterate across the MTask bodies in any order.  Order
        // isn't important for LifePostElimVisitor's simple substitution.
        iterateChildren(nodep);
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        if (!m_tracingCall && !nodep->entryPoint()) return;
        m_tracingCall = false;
        iterateChildren(nodep);
    }
    virtual void visit(AstVar*) VL_OVERRIDE {}  // Don't want varrefs under it
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit LifePostElimVisitor(AstTopScope* nodep)
        : m_tracingCall(false) {
        iterate(nodep);
    }
    virtual ~LifePostElimVisitor() {}
};

//######################################################################
// Location within the execution graph, identified by an mtask
// and a sequence number within the mtask:

struct LifeLocation {
    const ExecMTask* mtaskp;
    uint32_t sequence;
public:
    LifeLocation() : mtaskp(NULL), sequence(0) {}
    LifeLocation(const ExecMTask* mtaskp_, uint32_t sequence_)
        : mtaskp(mtaskp_), sequence(sequence_) {}
    bool operator< (const LifeLocation& b) const {
        unsigned a_id = mtaskp ? mtaskp->id() : 0;
        unsigned b_id = b.mtaskp ? b.mtaskp->id() : 0;
        if (a_id < b_id) { return true; }
        if (b_id < a_id) { return false; }
        return sequence < b.sequence;
    }
};

struct LifePostLocation {
    LifeLocation loc;
    AstAssignPost* nodep;
    LifePostLocation() : nodep(NULL) {}
    LifePostLocation(LifeLocation loc_, AstAssignPost* nodep_)
        : loc(loc_), nodep(nodep_) {}
};

//######################################################################
// LifePost delay elimination

class LifePostDlyVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on entire tree
    //  AstVarScope::user4()    -> AstVarScope*: Passed to LifePostElim to substitute this var
    AstUser4InUse       m_inuser4;

    // STATE
    uint32_t            m_sequence;     // Sequence number of assigns/varrefs,
    //                                  // local to the current MTask.
    const ExecMTask*    m_execMTaskp;   // Current ExecMTask being processed,
    //                                  // or NULL for serial code.
    VDouble0            m_statAssnDel;  // Statistic tracking
    bool                m_tracingCall;  // Currently tracing a CCall to a CFunc

    // Map each varscope to one or more locations where it's accessed.
    // These maps will not include any ASSIGNPOST accesses:
    typedef vl_unordered_map<const AstVarScope*, std::set<LifeLocation> > LocMap;
    LocMap              m_reads;        // VarScope read locations
    LocMap              m_writes;       // VarScope write locations

    // Map each dly var to its AstAssignPost* node and the location thereof
    typedef vl_unordered_map<const AstVarScope*, LifePostLocation> PostLocMap;
    PostLocMap          m_assignposts;  // AssignPost dly var locations

    const V3Graph*      m_mtasksGraphp;  // Mtask tracking graph
    vl_unique_ptr<GraphPathChecker> m_checker;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool before(const LifeLocation& a, const LifeLocation& b) {
        if (a.mtaskp == b.mtaskp) return a.sequence < b.sequence;
        return m_checker->pathExistsFrom(a.mtaskp, b.mtaskp);
    }
    bool outsideCriticalArea(LifeLocation loc,
                             const std::set<LifeLocation>& dlyVarAssigns,
                             LifeLocation assignPostLoc) {
        // If loc is before all of dlyVarAssigns, return true.
        // ("Before" means certain to be ordered before them at execution time.)
        // If assignPostLoc is before loc, return true.
        //
        // Otherwise, loc could fall in the "critical" area where the
        // substitution affects the result of the operation at loc, so
        // return false.
        if (!loc.mtaskp && assignPostLoc.mtaskp) {
            // This is threaded mode; 'loc' is something that happens at
            // initial/settle time, or perhaps in _eval() but outside of
            // the mtask graph.
            // In either case, it's not in the critical area.
            return true;
        }
        if (before(assignPostLoc, loc)) return true;
        for (std::set<LifeLocation>::iterator it = dlyVarAssigns.begin();
             it != dlyVarAssigns.end(); ++it) {
            if (!before(loc, *it)) return false;
        }
        return true;
    }
    void squashAssignposts() {
        for (PostLocMap::iterator it = m_assignposts.begin();
             it != m_assignposts.end(); ++it) {
            LifePostLocation* app = &it->second;
            AstVarRef* lhsp = VN_CAST(app->nodep->lhsp(), VarRef);  // original var
            AstVarRef* rhsp = VN_CAST(app->nodep->rhsp(), VarRef);  // dly var
            AstVarScope* dlyVarp = rhsp->varScopep();
            AstVarScope* origVarp = lhsp->varScopep();

            // Scrunch these:
            //  X1:  __Vdly__q = __PVT__clk_clocks;
            //      ... {no reads or writes of __PVT__q after the first write to __Vdly__q}
            //      ... {no reads of __Vdly__q after the first write to __Vdly__q}
            //  X2:  __PVT__q = __Vdly__q;
            //
            // Into just this:
            //  X1:  __PVT__q = __PVT__clk_clocks;
            //  X2:   (nothing)

            // More formally, with the non-sequential mtasks graph, we must
            // prove all of these before doing the scrunch:
            //  1) No reads of the dly var anywhere except for the ASSIGNPOST
            //  2) Every read of the original var either falls before each of
            //     the dly var's assignments, or after the ASSIGNPOST.
            //  3) Every write of the original var either falls before each of
            //     the dly var's assignments, or after the ASSIGNPOST.

            const std::set<LifeLocation>& dlyVarAssigns = m_writes[dlyVarp];
            // Proof (1)
            const std::set<LifeLocation>& dlyVarReads = m_reads[dlyVarp];
            if (!dlyVarReads.empty()) {
                continue;  // do not scrunch, go to next LifePostLocation
            }

            // Proof (2)
            bool canScrunch = true;
            const std::set<LifeLocation>& origVarReads = m_reads[origVarp];
            for (std::set<LifeLocation>::iterator rdLocIt = origVarReads.begin();
                 rdLocIt != origVarReads.end(); ++rdLocIt) {
                if (!outsideCriticalArea(*rdLocIt, dlyVarAssigns, app->loc)) {
                    canScrunch = false;
                    break;
                }
            }
            if (!canScrunch) continue;

            // Proof (3)
            const std::set<LifeLocation>& origVarWrites = m_writes[origVarp];
            for (std::set<LifeLocation>::iterator wrLocIt = origVarWrites.begin();
                 wrLocIt != origVarWrites.end(); ++wrLocIt) {
                if (!outsideCriticalArea(*wrLocIt, dlyVarAssigns, app->loc)) {
                    canScrunch = false;
                    break;
                }
            }
            if (!canScrunch) continue;

            // Delete and mark so LifePostElimVisitor will get it
            UINFO(4,"    DELETE "<<app->nodep<<endl);
            dlyVarp->user4p(origVarp);
            VL_DO_DANGLING(app->nodep->unlinkFrBack()->deleteTree(), app->nodep);
            ++m_statAssnDel;
        }
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep) VL_OVERRIDE {
        AstNode::user4ClearTree();  // user4p() used on entire tree

        // First, build maps of every location (mtask and sequence
        // within the mtask) where each varscope is read, and written.
        iterateChildren(nodep);

        if (v3Global.opt.mtasks()) {
            UASSERT_OBJ(m_mtasksGraphp, nodep,
                        "Should have initted m_mtasksGraphp by now");
            m_checker.reset(new GraphPathChecker(m_mtasksGraphp));
        } else {
            UASSERT_OBJ(!m_mtasksGraphp, nodep,
                        "Did not expect any m_mtasksGraphp in serial mode");
        }

        // Find all assignposts. Determine which ones can be
        // eliminated. Remove those, and mark their dly vars' user4 field
        // to indicate we should replace these dly vars with their original
        // variables.
        squashAssignposts();

        // Replace any node4p varscopes with the new scope
        LifePostElimVisitor visitor (nodep);
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        // Consumption/generation of a variable,
        AstVarScope* vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");

        LifeLocation loc(m_execMTaskp, ++m_sequence);
        if (nodep->lvalue()) {
            m_writes[vscp].insert(loc);
        } else {
            m_reads[vscp].insert(loc);
        }
    }
    virtual void visit(AstAssignPre* nodep) VL_OVERRIDE {
        // Do not record varrefs within assign pre.
        //
        // The pre-assignment into the dly var should not count as its
        // first write; we only want to consider reads and writes that
        // would still happen if the dly var were eliminated.
    }
    virtual void visit(AstAssignPost* nodep) VL_OVERRIDE {
        // Don't record ASSIGNPOST in the read/write maps, record them in a
        // separate map
        if (AstVarRef* rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
            // rhsp is the dly var
            AstVarScope* dlyVarp = rhsp->varScopep();
            UASSERT_OBJ(m_assignposts.find(dlyVarp) == m_assignposts.end(), nodep,
                        "LifePostLocation attempted duplicate dlyvar map addition");
            LifeLocation loc(m_execMTaskp, ++m_sequence);
            m_assignposts[dlyVarp] = LifePostLocation(loc, nodep);
        }
    }
    virtual void visit(AstNodeModule* nodep) VL_OVERRIDE {
        // Only track the top scopes, not lower level functions
        if (nodep->isTop()) iterateChildren(nodep);
    }
    virtual void visit(AstNodeCCall* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
        if (!nodep->funcp()->entryPoint()) {
            // Enter the function and trace it
            m_tracingCall = true;
            iterate(nodep->funcp());
        }
    }
    virtual void visit(AstExecGraph* nodep) VL_OVERRIDE {
        // Treat the ExecGraph like a call to each mtask body
        m_mtasksGraphp = nodep->depGraphp();
        for (V3GraphVertex* mtaskVxp = m_mtasksGraphp->verticesBeginp();
             mtaskVxp; mtaskVxp = mtaskVxp->verticesNextp()) {
            ExecMTask* mtaskp = dynamic_cast<ExecMTask*>(mtaskVxp);
            m_execMTaskp = mtaskp;
            m_sequence = 0;
            iterate(mtaskp->bodyp());
        }
        m_execMTaskp = NULL;
    }
    virtual void visit(AstCFunc* nodep) VL_OVERRIDE {
        if (!m_tracingCall && !nodep->entryPoint()) return;
        m_tracingCall = false;
        iterateChildren(nodep);
    }
    //-----
    virtual void visit(AstVar*) VL_OVERRIDE {}  // Don't want varrefs under it
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        iterateChildren(nodep);
    }
public:
    // CONSTRUCTORS
    explicit LifePostDlyVisitor(AstNetlist* nodep)
        : m_sequence(0)
        , m_execMTaskp(NULL)
        , m_tracingCall(false)
        , m_mtasksGraphp(NULL) {
        iterate(nodep);
    }
    virtual ~LifePostDlyVisitor() {
        V3Stats::addStat("Optimizations, Lifetime postassign deletions", m_statAssnDel);
    }
};

//######################################################################
// LifePost class functions

void V3LifePost::lifepostAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Mark redundant AssignPost
    {
        LifePostDlyVisitor visitor(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("life_post", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
