// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Variable ordering
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
// V3VariableOrder's Transformations:
//
// Each module:
//   Order module variables
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3VariableOrder.h"

#include "V3AstUserAllocator.h"
#include "V3EmitCBase.h"
#include "V3ExecGraph.h"
#include "V3ThreadPool.h"

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

using MTaskIdVec = std::vector<bool>;  // Used as a bit-set indexed by MTask ID
using MTaskAffinityMap = std::unordered_map<const AstVar*, MTaskIdVec>;

// Trace through code reachable form an MTask and annotate referenced variabels
class GatherMTaskAffinity final : VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user1()  // bool: Already traced this function
    //  AstVar::user1()  // bool: Already traced this variable
    const VNUser1InUse m_user1InUse;

    // STATE
    MTaskAffinityMap& m_results;  // The result map being built;
    const uint32_t m_id;  // Id of mtask being analysed
    const size_t m_usedIds = ExecMTask::numUsedIds();  // Value of max id + 1

    // CONSTRUCTOR
    GatherMTaskAffinity(const ExecMTask* mTaskp, MTaskAffinityMap& results)
        : m_results{results}
        , m_id{mTaskp->id()} {
        iterateConst(mTaskp->funcp());
    }
    ~GatherMTaskAffinity() = default;
    VL_UNMOVABLE(GatherMTaskAffinity);

    // VISIT
    void visit(AstNodeVarRef* nodep) override {
        // Cheaper than relying on emplace().second
        if (nodep->user1SetOnce()) return;
        AstVar* const varp = nodep->varp();
        // Set affinity bit
        MTaskIdVec& affinity = m_results
                                   .emplace(std::piecewise_construct,  //
                                            std::forward_as_tuple(varp),  //
                                            std::forward_as_tuple(m_usedIds))
                                   .first->second;
        affinity[m_id] = true;
    }

    void visit(AstCFunc* nodep) override {
        if (nodep->user1SetOnce()) return;  // Prevent repeat traversals/recursion
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);  // Arguments
        iterateConst(nodep->funcp());  // Callee
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    static void apply(const ExecMTask* mTaskp, MTaskAffinityMap& results) {
        GatherMTaskAffinity{mTaskp, results};
    }
};

struct VarAttributes final {
    uint8_t stratum;  // Roughly equivalent to alignment requirement, to avoid padding
    bool anonOk;  // Can be emitted as part of anonymous structure
};
class VariableOrder final {
    std::unordered_map<const AstVar*, VarAttributes> m_attributes;

    const MTaskAffinityMap& m_mTaskAffinity;
    std::vector<AstVar*>& m_varps;

    VariableOrder(AstNodeModule* modp, const MTaskAffinityMap& mTaskAffinity,
                  std::vector<AstVar*>& varps)
        : m_mTaskAffinity{mTaskAffinity}
        , m_varps{varps} {
        orderModuleVars(modp);
    }
    ~VariableOrder() = default;
    VL_UNCOPYABLE(VariableOrder);

    //######################################################################

    // Simple sort
    void simpleSortVars(std::vector<AstVar*>& varps) {
        stable_sort(varps.begin(), varps.end(),
                    [this](const AstVar* ap, const AstVar* bp) -> bool {
                        if (ap->isStatic() != bp->isStatic()) {  // Non-statics before statics
                            return bp->isStatic();
                        }
                        UASSERT(m_attributes.find(ap) != m_attributes.end()
                                    && m_attributes.find(bp) != m_attributes.end(),
                                "m_attributes should be populated for each AstVar");
                        const auto& attrA = m_attributes.at(ap);
                        const auto& attrB = m_attributes.at(bp);
                        if (attrA.anonOk != attrB.anonOk) {  // Anons before non-anons
                            return attrA.anonOk;
                        }
                        return attrA.stratum < attrB.stratum;  // Finally sort by stratum
                    });
    }

    static bool emptyAffinity(const MTaskIdVec& vec) {
        return std::find(vec.begin(), vec.end(), true) == vec.end();
    }
    static size_t firstMTaskId(const MTaskIdVec& vec) {
        const auto it = std::find(vec.begin(), vec.end(), true);
        UASSERT(it != vec.end(), "No MTask affinity");
        return static_cast<size_t>(it - vec.begin());
    }
    static size_t mTaskPopcount(const MTaskIdVec& vec) {
        return static_cast<size_t>(std::count(vec.begin(), vec.end(), true));
    }
    static bool isEmittedDesignState(const AstVar* varp) {
        return !varp->isStatic()
               && (varp->isIO() || varp->isSignal() || varp->isClassMember() || varp->isTemp()
                   || varp->isGenVar());
    }

    // Sort by MTask-affinity first, then the same as simpleSortVars
    void mtaskSortVars(std::vector<AstVar*>& varps) {
        // Map from "MTask affinity" -> "variable list"
        std::map<MTaskIdVec, std::vector<AstVar*>> m2v;
        const MTaskIdVec emptyVec(ExecMTask::numUsedIds(), false);
        for (AstVar* const varp : varps) {
            const auto it = m_mTaskAffinity.find(varp);
            const MTaskIdVec& key = it == m_mTaskAffinity.end() ? emptyVec : it->second;
            m2v[key].push_back(varp);
        }

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend = [this, &varps](std::vector<AstVar*>& subVarps) {
            simpleSortVars(subVarps);
            for (AstVar* const varp : subVarps) varps.push_back(varp);
        };
        const auto sortAlignAndAppend = [this, &varps](std::vector<AstVar*>& subVarps) {
            simpleSortVars(subVarps);
            bool aligned = false;
            for (AstVar* const varp : subVarps) {
                if (!aligned && isEmittedDesignState(varp)) {
                    varp->mtaskCacheLineAlign(true);
                    V3Stats::addStatSum("VariableOrder, MTask aligned group starts", 1);
                    aligned = true;
                }
                varps.push_back(varp);
            }
        };

        // Sort non-empty MTask affinity groups deterministically. This keeps memory linear in the
        // number of affinity groups, unlike the old complete pairwise-distance ordering.
        std::vector<std::map<MTaskIdVec, std::vector<AstVar*>>::iterator> groups;
        for (auto it = m2v.begin(); it != m2v.end(); ++it) {
            if (!emptyAffinity(it->first)) groups.push_back(it);
        }
        std::stable_sort(groups.begin(), groups.end(), [](const auto& ap, const auto& bp) {
            const MTaskIdVec& avec = ap->first;
            const MTaskIdVec& bvec = bp->first;
            const size_t afirst = firstMTaskId(avec);
            const size_t bfirst = firstMTaskId(bvec);
            if (afirst != bfirst) return afirst < bfirst;
            const size_t apop = mTaskPopcount(avec);
            const size_t bpop = mTaskPopcount(bvec);
            if (apop != bpop) return apop < bpop;
            return avec < bvec;
        });
        for (const auto& it : groups) sortAlignAndAppend(it->second);

        // Finally add the variables with no known MTask affinity
        sortAndAppend(m2v[emptyVec]);

        V3Stats::addStatSum("VariableOrder, MTask affinity groups", groups.size());
        V3Stats::addStatSum("VariableOrder, no-affinity variables", m2v[emptyVec].size());
    }

    // cppcheck-suppress constParameterPointer
    void orderModuleVars(AstNodeModule* modp) {
        // Unlink all module variables from the module, compute attributes
        for (AstNode *nodep = modp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                m_varps.push_back(varp);

                // Compute attributes up front
                // Stratum
                const int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                const uint8_t stratum = (v3Global.opt.hierChild() && varp->isPrimaryIO())   ? 0
                                        : (varp->isPrimaryClock() && varp->widthMin() == 1) ? 1
                                        : VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)    ? 9
                                        : (varp->basicp() && varp->basicp()->isOpaque())    ? 8
                                        : (varp->isScBv() || varp->isScBigUint())           ? 7
                                        : (sigbytes == 8)                                   ? 6
                                        : (sigbytes == 4)                                   ? 5
                                        : (sigbytes == 2)                                   ? 3
                                        : (sigbytes == 1)                                   ? 2
                                                                                            : 10;
                m_attributes.emplace(varp, VarAttributes{stratum, EmitCUtil::isAnonOk(varp)});
            }
        }

        if (!m_varps.empty()) {
            if (!v3Global.opt.mtasks()) {
                simpleSortVars(m_varps);
            } else {
                mtaskSortVars(m_varps);
            }
        }
    }

public:
    static void processModule(AstNodeModule* modp, const MTaskAffinityMap& mTaskAffinity,
                              std::vector<AstVar*>& varps) VL_MT_STABLE {
        VariableOrder{modp, mTaskAffinity, varps};
    }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");

    MTaskAffinityMap mTaskAffinity;

    // Gather MTask affinities
    if (v3Global.opt.mtasks()) {
        netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
            for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                GatherMTaskAffinity::apply(vtx.as<const ExecMTask>(), mTaskAffinity);
            }
        });
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-gather");

    // Sort variables for each module
    std::unordered_map<AstNodeModule*, std::vector<AstVar*>> sortedVars;
    {
        V3ThreadScope threadScope;

        for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
             modp = VN_AS(modp->nextp(), NodeModule)) {
            std::vector<AstVar*>& varps = sortedVars[modp];
            threadScope.enqueue([modp, &mTaskAffinity, &varps]() {
                VariableOrder::processModule(modp, mTaskAffinity, varps);
            });
        }
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-sort");

    // Insert them back under the module, in the new order, but at
    // the front of the list so they come out first in dumps/JSON.
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        const std::vector<AstVar*>& varps = sortedVars[modp];

        if (!varps.empty()) {
            auto it = varps.cbegin();
            AstVar* const firstp = *it++;
            firstp->unlinkFrBack();
            for (; it != varps.cend(); ++it) {
                AstVar* const varp = *it;
                varp->unlinkFrBack();
                firstp->addNext(varp);
            }
            if (AstNode* const stmtsp = modp->stmtsp()) {
                stmtsp->unlinkFrBackWithNext();
                AstNode::addNext<AstNode, AstNode>(firstp, stmtsp);
            }
            modp->addStmtsp(firstp);
        }
    }

    // Done
    V3Global::dumpCheckGlobalTree("variableorder", 0, dumpTreeEitherLevel() >= 3);
}
