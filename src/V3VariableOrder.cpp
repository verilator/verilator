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
// With multithreading, variables accessed by MTasks are grouped by the exact
// set of MTasks writing them (variables MTasks only read form one group), and
// the first instance field of each group is aligned to a cache line. Variables
// no MTask accesses follow, unaligned.
//
// Separating writers is enough to avoid false sharing. Every MTask accessing a
// variable is ordered relative to the variable's writers by the MTask graph, so
// a cache line holding one group is never written while another thread is using
// it, however the MTasks are packed onto threads. Grouping by readers as well
// would only add padding.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3VariableOrder.h"

#include "V3AstUserAllocator.h"
#include "V3EmitCBase.h"
#include "V3ExecGraph.h"

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

using MTaskIdVec = std::vector<bool>;  // Used as a bit-set indexed by MTask ID
// Writing MTasks of each variable accessed by any MTask
using MTaskWritersMap = std::unordered_map<const AstVar*, MTaskIdVec>;

// Trace through code reachable from an MTask and record the writers of referenced variables
class GatherMTaskWriters final : VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user1()  // bool: Already traced this function
    //  AstVar::user1()  // bool: Already traced this variable
    const VNUser1InUse m_user1InUse;

    // STATE
    MTaskWritersMap& m_results;  // The result map being built;
    const uint32_t m_id;  // Id of mtask being analysed
    const size_t m_usedIds = ExecMTask::numUsedIds();  // Value of max id + 1

    // CONSTRUCTOR
    GatherMTaskWriters(const ExecMTask* mTaskp, MTaskWritersMap& results)
        : m_results{results}
        , m_id{mTaskp->id()} {
        iterateConst(mTaskp->funcp());
    }
    ~GatherMTaskWriters() = default;
    VL_UNMOVABLE(GatherMTaskWriters);

    // VISIT
    void visit(AstNodeVarRef* nodep) override {
        // Cheaper than relying on emplace().second
        if (nodep->user1SetOnce()) return;
        AstVar* const varp = nodep->varp();
        // Record the access, and the writer bit if written
        MTaskIdVec& writers = m_results
                                  .emplace(std::piecewise_construct,  //
                                           std::forward_as_tuple(varp),  //
                                           std::forward_as_tuple(m_usedIds))
                                  .first->second;
        if (nodep->access().isWriteOrRW()) writers[m_id] = true;
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
    static void apply(const ExecMTask* mTaskp, MTaskWritersMap& results) {
        GatherMTaskWriters{mTaskp, results};
    }
};

struct VarAttributes final {
    uint8_t stratum;  // Roughly equivalent to alignment requirement, to avoid padding
    bool anonOk;  // Can be emitted as part of anonymous structure
};
class VariableOrder final {
    std::unordered_map<const AstVar*, VarAttributes> m_attributes;

    const MTaskWritersMap& m_mTaskWriters;
    std::vector<AstVar*>& m_varps;

    VariableOrder(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                  std::vector<AstVar*>& varps)
        : m_mTaskWriters{mTaskWriters}
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

    // Sort by writing MTasks first, then the same as simpleSortVars
    void mtaskSortVars(std::vector<AstVar*>& varps) {
        // Map from "writing MTasks" -> "variable list", for variables accessed by MTasks
        std::map<MTaskIdVec, std::vector<AstVar*>> m2v;
        // Variables not accessed by any MTask
        std::vector<AstVar*> noAffinityVarps;
        for (AstVar* const varp : varps) {
            const auto it = m_mTaskWriters.find(varp);
            if (it == m_mTaskWriters.end()) {
                noAffinityVarps.push_back(varp);
            } else {
                m2v[it->second].push_back(varp);
            }
        }

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend
            = [this, &varps](std::vector<AstVar*>& subVarps, bool alignFirst) {
                  simpleSortVars(subVarps);
                  bool aligned = !alignFirst;
                  for (AstVar* const varp : subVarps) {
                      // Align the first variable with instance storage
                      if (!aligned && varp->isModelState()) {
                          varp->mtaskCacheLineAlign(true);
                          V3Stats::addStatSum("VariableOrder, MTask aligned group starts", 1);
                          aligned = true;
                      }
                      varps.push_back(varp);
                  }
              };

        // Add the groups in the map's deterministic key order
        for (auto& pair : m2v) sortAndAppend(pair.second, true);

        // Finally add the variables with no known MTask affinity
        sortAndAppend(noAffinityVarps, false);

        V3Stats::addStatSum("VariableOrder, MTask affinity groups", m2v.size());
        V3Stats::addStatSum("VariableOrder, no-affinity variables", noAffinityVarps.size());
    }

    // cppcheck-suppress constParameterPointer
    void orderModuleVars(AstNodeModule* modp) {
        // Top level ports stay first in source order, as a --lib-create wrapper must match
        // the interface of the module it replaces
        std::vector<AstVar*> portps;
        // Unlink all module variables from the module, compute attributes
        for (AstNode *nodep = modp->stmtsp(), *nextp; nodep; nodep = nextp) {
            nextp = nodep->nextp();
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                if (modp->isTop() && varp->isIO()) {
                    portps.push_back(varp);
                    continue;
                }
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
        m_varps.insert(m_varps.begin(), portps.begin(), portps.end());
    }

public:
    static void processModule(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                              std::vector<AstVar*>& varps) {
        VariableOrder{modp, mTaskWriters, varps};
    }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");

    MTaskWritersMap mTaskWriters;

    // Gather writing MTasks
    if (v3Global.opt.mtasks()) {
        netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
            for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                GatherMTaskWriters::apply(vtx.as<const ExecMTask>(), mTaskWriters);
            }
        });
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-gather");

    // Sort variables for each module
    std::unordered_map<AstNodeModule*, std::vector<AstVar*>> sortedVars;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (modp->isConstPool()) continue;
        VariableOrder::processModule(modp, mTaskWriters, sortedVars[modp]);
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-sort");

    // Insert them back under the module, in the new order, but at
    // the front of the list so they come out first in dumps/JSON.
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        if (modp->isConstPool()) continue;
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
