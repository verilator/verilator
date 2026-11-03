// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Combine common code into functions
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
// V3Combine's Transformations:
//
//      Combine identical CFuncs by retaining only a single copy
//      Also drop empty CFuncs
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Combine.h"

#include "V3AstUserAllocator.h"
#include "V3DupFinder.h"
#include "V3Stats.h"

#include <list>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class CombineVisitor final : VNVisitor {
    // NODE STATE
    // AstNodeModule::user1()   List of AstCFuncs in this module (via m_cfuncs)
    // AstCFunc::user1()        CFuncInfo (via m_cfuncInfo)
    // *::user4()               Used by V3Hasher
    const VNUser1InUse m_user1InUse;

    // TYPES
    using funcit_t = std::list<AstCFunc*>::iterator;
    struct CFuncs final {
        std::list<AstCFunc*> m_fast;  // Functions that are not slow
        std::list<AstCFunc*> m_slow;  // Functions marked for slow files
    };
    struct CFuncInfo final {
        std::vector<AstCCall*> m_callSites;  // Call sites of this function
        size_t m_index = 0;  // Position in the list of functions being combined
        bool m_replaced = false;  // Already replaced by an equivalent function
    };

    // STATE
    AstUser1Allocator<AstNodeModule, CFuncs> m_cfuncs;  // AstCFuncs under module
    AstUser1Allocator<AstCFunc, CFuncInfo> m_cfuncInfo;  // Data associated with each AstCFunc
    AstNodeModule* m_modp = nullptr;  // Current module
    const V3Hasher m_hasher;  // For hashing
    VDouble0 m_cfuncsCombined;  // Statistic tracking

    // METHODS

    void removeEmptyFunctions(std::list<AstCFunc*>& funcps) {
        for (funcit_t it = funcps.begin(), nit; it != funcps.end(); it = nit) {
            AstCFunc* const funcp = *it;
            nit = it;
            ++nit;

            if (funcp->emptyBody()) {
                // Delete call sites
                std::vector<AstCCall*>& callSites = m_cfuncInfo(funcp).m_callSites;
                for (AstCCall* const callp : callSites) {
                    UASSERT_OBJ(VN_IS(callp->backp(), StmtExpr), callp,
                                "Deleting non-statement call");
                    VL_DO_DANGLING(callp->backp()->unlinkFrBack()->deleteTree(), callp);
                }
                callSites.clear();
                // Remove from list
                funcps.erase(it);
                // Delete function
                VL_DO_DANGLING(funcp->unlinkFrBack()->deleteTree(), funcp);
            }
        }
    }

    // One pass of combining. Returns true if did replacement.
    bool combinePass(std::list<AstCFunc*>& funcps, V3DupFinder& dupFinder) {
        bool replaced = false;

        // Replace all identical functions with the first function in the list
        for (funcit_t it = funcps.begin(), nit; it != funcps.end(); it = nit) {
            AstCFunc* const funcp = *it;
            nit = it;
            ++nit;

            // Remove functions already replaced in the previous iteration
            if (m_cfuncInfo(funcp).m_replaced) {
                funcps.erase(it);
                VL_DO_DANGLING(funcp->unlinkFrBack()->deleteTree(), funcp);
                continue;
            }

            while (true) {
                auto dit = dupFinder.findDuplicate(funcp);
                if (dit == dupFinder.end()) break;

                AstCFunc* oldp = VN_AS(dit->second, CFunc);
                AstCFunc* newp = funcp;
                UASSERT_OBJ(!m_cfuncInfo(oldp).m_replaced, oldp,
                            "Should have been removed from dupFinder");

                // Swap them, if the duplicate is earlier in the list of functions. This is
                // necessary because replacing a call site in a later function might have made that
                // function equivalent to an earlier function, but we want the first equivalent
                // function in the list to be the canonical one.
                if (m_cfuncInfo(oldp).m_index < m_cfuncInfo(newp).m_index) {
                    std::swap(oldp, newp);
                }

                // Something is being replaced
                UINFO(9, "Replacing " << oldp);
                UINFO(9, "     with " << newp);
                ++m_cfuncsCombined;
                replaced = true;

                // Mark as replaced
                m_cfuncInfo(oldp).m_replaced = true;

                // Redirect the calls
                for (AstCCall* const callp : m_cfuncInfo(oldp).m_callSites) {
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
        }

        return replaced;
    }

    // cppcheck-suppress constParameterPointer
    void process(AstNetlist* netlistp) {
        // First, remove empty functions. We need to do this separately, because removing
        // calls can change the hashes of the callers.
        for (AstNodeModule* const modulep : netlistp->modulespList()) {
            removeEmptyFunctions(m_cfuncs(modulep).m_fast);
            removeEmptyFunctions(m_cfuncs(modulep).m_slow);
        }

        // Combine functions within each module
        for (AstNodeModule* const modulep : netlistp->modulespList()) {
            // Put fast functions first, so they are preferred over slow functions
            auto funcps = std::move(m_cfuncs(modulep).m_fast);
            funcps.splice(funcps.end(), m_cfuncs(modulep).m_slow);

            V3DupFinder dupFinder{m_hasher};

            // First, hash all functions, and record their position in the list
            size_t index = 0;
            for (AstCFunc* const funcp : funcps) {
                m_cfuncInfo(funcp).m_index = index++;
                dupFinder.insert(funcp);
            }

            // Iterate to fixed point
            while (combinePass(funcps, dupFinder)) {}
        }
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // Gather functions and references
        iterateChildrenConst(nodep);
        // Combine functions
        process(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Should not nest");
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstCFunc* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->dontCombine()) return;
        auto& coll = nodep->slow() ? m_cfuncs(m_modp).m_slow : m_cfuncs(m_modp).m_fast;
        coll.emplace_back(nodep);
    }
    void visit(AstCCall* nodep) override {
        iterateChildrenConst(nodep);
        AstCFunc* const funcp = nodep->funcp();
        if (funcp->dontCombine()) return;
        m_cfuncInfo(funcp).m_callSites.emplace_back(nodep);
    }

    void visit(AstAddrOfCFunc* nodep) override {
        iterateChildrenConst(nodep);
        if (nodep->funcp()->dontCombine()) return;
        // LCOV_EXCL_START
        // We cannot yet handle references via AstAddrOfCFunc, but currently those are
        // only used in tracing functions, which are not combined. Blow up in case this changes.
        nodep->v3fatalSrc(
            "Don't know how to combine functions that are referenced via AstAddrOfCFunc");
        // LCOV_EXCL_STOP
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

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
    UINFO(2, __FUNCTION__ << ":");
    CombineVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("combine", 0, dumpTreeEitherLevel() >= 3);
}
