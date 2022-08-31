// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Combine common code into functions
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
// V3Combine's Transformations:
//
//      Combine identical CFuncs by retaining only a single copy
//      Also drop empty CFuncs
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Combine.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3DupFinder.h"
#include "V3Global.h"
#include "V3Stats.h"

#include <list>
#include <vector>

class CombineVisitor final : VNVisitor {
    // NODE STATE
    // AstNodeModule::user1()   List of AstCFuncs in this module (via m_cfuncs)
    // AstCFunc::user1()        List of AstCCalls to this function (via m_callSites)
    // AstCFunc::user2()        bool: Already replaced (in 'process')
    // AstCFunc::user3()        bool: Marks functions earlier in iteration order (in 'combinePass')
    // *::user4()               Used by V3Hasher
    const VNUser1InUse m_user1InUse;

    // TYPES
    using funcit_t = std::list<AstCFunc*>::iterator;
    struct CFuncs {
        std::list<AstCFunc*> m_fast;
        std::list<AstCFunc*> m_slow;
    };

    // STATE
    AstUser1Allocator<AstNodeModule, CFuncs> m_cfuncs;  // AstCFuncs under module
    AstUser1Allocator<AstCFunc, std::vector<AstCCall*>> m_callSites;  // Call sites of the AstCFunc
    AstNodeModule* m_modp = nullptr;  // Current module
    const V3Hasher m_hasher;  // For hashing
    VDouble0 m_cfuncsCombined;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void removeEmptyFunctions(std::list<AstCFunc*>& funcps) {
        for (funcit_t it = funcps.begin(), nit; it != funcps.end(); it = nit) {
            AstCFunc* const funcp = *it;
            nit = it;
            ++nit;

            if (funcp->emptyBody()) {
                // Delete call sites
                for (AstCCall* const callp : m_callSites(funcp)) {
                    VL_DO_DANGLING(callp->unlinkFrBack()->deleteTree(), callp);
                }
                m_callSites(funcp).clear();
                // Remove from list
                funcps.erase(it);
                // Delete function
                VL_DO_DANGLING(funcp->unlinkFrBack()->deleteTree(), funcp);
            }
        }
    }

    // One pass of combining. Returns true if did replacement.
    bool combinePass(std::list<AstCFunc*>& funcps, V3DupFinder& dupFinder) {
        const VNUser3InUse user3InUse;

        bool replaced = false;

        // Replace all identical functions with the first function in the list
        for (funcit_t it = funcps.begin(), nit; it != funcps.end(); it = nit) {
            AstCFunc* const funcp = *it;
            nit = it;
            ++nit;

            // Remove functions already replaced in the previous iteration
            if (funcp->user2()) {
                funcps.erase(it);
                VL_DO_DANGLING(funcp->unlinkFrBack()->deleteTree(), funcp);
                continue;
            }

            while (true) {
                auto dit = dupFinder.findDuplicate(funcp);
                if (dit == dupFinder.end()) break;

                AstCFunc* oldp = VN_AS(dit->second, CFunc);
                AstCFunc* newp = funcp;
                UASSERT_OBJ(!oldp->user2(), oldp, "Should have been removed from dupFinder");

                // Swap them, if the duplicate is earlier in the list of functions. This is
                // necessary because replacing a call site in a later function might have made that
                // function equivalent to an earlier function, but we want the first equivalent
                // function in the list to be the canonical one.
                if (oldp->user3()) std::swap(oldp, newp);

                // Something is being replaced
                UINFO(9, "Replacing " << oldp << endl);
                UINFO(9, "     with " << newp << endl);
                ++m_cfuncsCombined;
                replaced = true;

                // Mark as replaced
                oldp->user2(true);

                // Redirect the calls
                for (AstCCall* const callp : m_callSites(oldp)) {
                    // For sanity check only
                    const V3Hash oldHash = m_hasher(callp);

                    // Redirect the call
                    callp->funcp(newp);

                    // When redirecting a call to an equivalent function, we do not need to re-hash
                    // the caller, because the hash of the two calls must be the same, and hence
                    // the hash of the caller should not change.
                    UASSERT_OBJ(oldHash == m_hasher.rehash(callp), callp, "Hash changed");
                }

                // Erase the replaced duplicate
                UASSERT_OBJ(dupFinder.erase(oldp) == 1, oldp, "Replaced node not in dupFinder");

                // If we just replaced the function we are iterating (because there was an
                // equivalent earlier in the list), then move on, as this is on longer a candidate
                if (oldp == funcp) break;
            }

            // Mark as function earlier in list of functions.
            funcp->user3(true);
        }

        return replaced;
    }

    void process(AstNetlist* netlistp) {
        // First, remove empty functions. We need to do this separately, because removing
        // calls can change the hashes of the callers.
        for (AstNodeModule* modulep = netlistp->modulesp(); modulep;
             modulep = VN_AS(modulep->nextp(), NodeModule)) {
            removeEmptyFunctions(m_cfuncs(modulep).m_fast);
            removeEmptyFunctions(m_cfuncs(modulep).m_slow);
        }

        // Combine functions within each module
        for (AstNodeModule* modulep = netlistp->modulesp(); modulep;
             modulep = VN_AS(modulep->nextp(), NodeModule)) {
            // Put fast functions first, so they are preferred over slow functions
            auto funcps = std::move(m_cfuncs(modulep).m_fast);
            funcps.splice(funcps.end(), m_cfuncs(modulep).m_slow);

            V3DupFinder dupFinder{m_hasher};

            // First, hash all functions
            for (AstCFunc* const funcp : funcps) dupFinder.insert(funcp);

            // Iterate to fixed point
            {
                const VNUser2InUse user2InUse;
                while (combinePass(funcps, dupFinder)) {}
            }
        }
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        // Gather functions and references
        iterateChildrenConst(nodep);
        // Combine functions
        process(nodep);
    }
    virtual void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Should not nest");
        m_modp = nodep;
        iterateChildrenConst(nodep);
        m_modp = nullptr;
    }
    virtual void visit(AstCFunc* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->dontCombine()) return;
        auto& coll = nodep->slow() ? m_cfuncs(m_modp).m_slow : m_cfuncs(m_modp).m_fast;
        coll.emplace_back(nodep);
    }
    virtual void visit(AstCCall* nodep) override {
        iterateChildrenConst(nodep);
        AstCFunc* const funcp = nodep->funcp();
        if (funcp->dontCombine()) return;
        m_callSites(funcp).emplace_back(nodep);
    }

    virtual void visit(AstAddrOfCFunc* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->funcp()->dontCombine()) return;
        // LCOV_EXCL_START
        // We cannot yet handle references via AstAddrOfCFunc, but currently those are
        // only used in tracing functions, which are not combined. Blow up in case this changes.
        nodep->v3fatalSrc(
            "Don't know how to combine functions that are referenced via AstAddrOfCFunc");
        // LCOV_EXCL_END
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit CombineVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CombineVisitor() override {
        V3Stats::addStat("Optimizations, Combined CFuncs", m_cfuncsCombined);
    }

public:
    static void apply(AstNetlist* netlistp) { CombineVisitor{netlistp}; }
};

//######################################################################
// Combine class functions

void V3Combine::combineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    CombineVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("combine", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
