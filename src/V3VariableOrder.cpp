// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Variable ordering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
#include "V3TSP.h"
#include "V3ThreadPool.h"

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
        iterateChildrenConst(mTaskp->bodyp());
    }
    ~GatherMTaskAffinity() = default;
    VL_UNMOVABLE(GatherMTaskAffinity);

    // VISIT
    void visit(AstNodeVarRef* nodep) override {
        // Cheaper than relying on emplace().second
        if (nodep->user1SetOnce()) return;
        AstVar* const varp = nodep->varp();
        // Ignore TriggerVec. They are big and read-only in the MTask bodies
        AstBasicDType* const basicp = varp->dtypep()->basicp();
        if (basicp && basicp->isTriggerVec()) return;
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

//######################################################################
// Establish mtask variable sort order in mtasks mode

class VarTspSorter final : public V3TSP::TspStateBase {
    // MEMBERS
    const MTaskIdVec& m_mTaskIds;  // Mtask we're ordering
    static uint32_t s_serialNext;  // Unique ID to establish serial order
    const uint32_t m_serial = ++s_serialNext;  // Serial ordering
public:
    // CONSTRUCTORS
    explicit VarTspSorter(const MTaskIdVec& mTaskIds)
        : m_mTaskIds{mTaskIds} {
        UASSERT(mTaskIds.size() == ExecMTask::numUsedIds(), "Wrong size for MTask ID vector");
    }
    ~VarTspSorter() override = default;
    // METHODS
    bool operator<(const TspStateBase& other) const override {
        return operator<(static_cast<const VarTspSorter&>(other));
    }
    bool operator<(const VarTspSorter& other) const { return m_serial < other.m_serial; }
    const MTaskIdVec& mTaskIds() const { return m_mTaskIds; }
    int cost(const TspStateBase* otherp) const override VL_MT_SAFE {
        return cost(static_cast<const VarTspSorter*>(otherp));
    }
    int cost(const VarTspSorter* otherp) const VL_MT_SAFE {
        // Compute the number of MTasks not shared (Hamming distance)
        int cost = 0;
        const size_t size = ExecMTask::numUsedIds();
        for (size_t i = 0; i < size; ++i) cost += m_mTaskIds.at(i) ^ otherp->m_mTaskIds.at(i);
        return cost;
    }
};

uint32_t VarTspSorter::s_serialNext = 0;

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

    // Sort by MTask-affinity first, then the same as simpleSortVars
    void tspSortVars(std::vector<AstVar*>& varps) {
        // Map from "MTask affinity" -> "variable list"
        std::map<const MTaskIdVec, std::vector<AstVar*>> m2v;
        const MTaskIdVec emptyVec(ExecMTask::numUsedIds(), false);
        for (AstVar* const varp : varps) {
            const auto it = m_mTaskAffinity.find(varp);
            const MTaskIdVec& key = it == m_mTaskAffinity.end() ? emptyVec : it->second;
            m2v[key].push_back(varp);
        }

        // Create a TSP sort state for each unique MTaskIdSet, except for the empty set
        V3TSP::StateVec states;
        for (const auto& pair : m2v) {
            const MTaskIdVec& vec = pair.first;
            const bool empty = std::find(vec.begin(), vec.end(), true) == vec.end();
            if (!empty) states.push_back(new VarTspSorter{vec});
        }

        // Do the TSP sort
        V3TSP::StateVec sortedStates;
        V3TSP::tspSort(states, &sortedStates);

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend = [this, &varps](std::vector<AstVar*>& subVarps) {
            simpleSortVars(subVarps);
            for (AstVar* const varp : subVarps) varps.push_back(varp);
        };

        // Enumerate by sorted MTaskIdSet, sort within the set separately
        for (const V3TSP::TspStateBase* const stateBasep : sortedStates) {
            const VarTspSorter* const statep = dynamic_cast<const VarTspSorter*>(stateBasep);
            sortAndAppend(m2v[statep->mTaskIds()]);
            VL_DO_DANGLING(delete statep, statep);
        }

        // Finally add the variables with no known MTask affinity
        sortAndAppend(m2v[emptyVec]);
    }

    void orderModuleVars(AstNodeModule* modp) {
        // Unlink all module variables from the module, compute attributes
        for (AstNode *nodep = modp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                m_varps.push_back(varp);

                // Compute attributes up front
                // Stratum
                const int sigbytes = varp->dtypeSkipRefp()->widthAlignBytes();
                const uint8_t stratum = (v3Global.opt.hierChild() && varp->isPrimaryIO()) ? 0
                                        : (varp->isUsedClock() && varp->widthMin() == 1)  ? 1
                                        : VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)  ? 9
                                        : (varp->basicp() && varp->basicp()->isOpaque())  ? 8
                                        : (varp->isScBv() || varp->isScBigUint())         ? 7
                                        : (sigbytes == 8)                                 ? 6
                                        : (sigbytes == 4)                                 ? 5
                                        : (sigbytes == 2)                                 ? 3
                                        : (sigbytes == 1)                                 ? 2
                                                                                          : 10;
                m_attributes.emplace(varp, VarAttributes{stratum, EmitCBase::isAnonOk(varp)});
            }
        }

        if (!m_varps.empty()) {
            if (!v3Global.opt.mtasks()) {
                simpleSortVars(m_varps);
            } else {
                tspSortVars(m_varps);
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
    UINFO(2, __FUNCTION__ << ": " << endl);

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
            threadScope.enqueue([modp, mTaskAffinity, &varps]() {
                VariableOrder::processModule(modp, mTaskAffinity, varps);
            });
        }
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-sort");

    // Insert them back under the module, in the new order, but at
    // the front of the list so they come out first in dumps/XML.
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
