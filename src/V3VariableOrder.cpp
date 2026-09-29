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

#include <algorithm>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Accessing-worker representatives followed by exact writing-task IDs, in separate bit ranges.
using MTaskIdVec = std::vector<bool>;
using MTaskAffinityMap = std::unordered_map<const AstVar*, MTaskIdVec>;

// Diagnostic inputs retain exact accessing/writing tasks before layout coalesces them.
// Only collected with --stats or --dumpi-V3VariableOrder.
class VariableOrderStats final {
    MTaskAffinityMap m_taskSets;  // Original accessing/writing task bits for each variable
    std::unique_ptr<std::ofstream> m_dumpp;  // Optional layout dump stream
    std::set<MTaskIdVec> m_sharedWorkers;  // Shared worker sets seen in the current module
    size_t m_group = 0;  // Next group number in the current module's dump
    uint64_t m_statNoAffinity = 0;  // Variables with no scheduled-task accesses
    uint64_t m_statSingleWorker = 0;  // Variables accessed by exactly one worker
    uint64_t m_statSharedReadOnly = 0;  // Variables shared by workers with no task writes
    uint64_t m_statSharedWritten = 0;  // Variables shared by workers with task writes
    // Groups eliminated by mapping accessing tasks to workers, with writers fixed
    uint64_t m_statWorkerEliminated = 0;
    // Further groups eliminated by dropping writer distinctions for single-worker state
    uint64_t m_statSingleWorkerEliminated = 0;
    // Additional shared groups retained to separate exact writing-task sets
    uint64_t m_statSharedWriterAdditional = 0;

    void dumpSet(const MTaskIdVec& vec, size_t begin, size_t end) const {
        *m_dumpp << '{';
        const char* sep = "";
        for (size_t i = begin; i < end; ++i) {
            if (!vec[i]) continue;
            *m_dumpp << sep << i - begin;
            sep = ",";
        }
        *m_dumpp << '}';
    }

public:
    VariableOrderStats() {
        if (v3Global.opt.mtasks() && dumpLevel()) {
            const string filename = v3Global.debugFilename("variableorder.txt");
            m_dumpp.reset(V3File::new_ofstream(filename));
            if (m_dumpp->fail()) v3fatal("Can't write file: " << filename);
        }
    }
    MTaskAffinityMap& taskSets() { return m_taskSets; }
    void startModule(const AstNodeModule* modp) {
        m_sharedWorkers.clear();
        m_group = 0;
        if (m_dumpp) *m_dumpp << "Module " << modp->name() << '\n';
    }
    void recordGroup(const MTaskIdVec& key, const std::vector<AstVar*>& varps) {
        if (varps.empty()) return;
        const size_t usedIds = ExecMTask::numUsedIds();
        const MTaskIdVec workers(key.begin(), key.begin() + usedIds);
        const size_t nWorkers = std::count(workers.begin(), workers.end(), true);
        // Within each actual final group, hold writers fixed while counting collapsed
        // accessing-task sets. Then count any further collapse of distinct writer sets.
        // This measures realized reductions, not opportunities in a hypothetical layout.
        std::map<MTaskIdVec, std::set<MTaskIdVec>> writersToAccesses;
        if (m_dumpp) {
            *m_dumpp << "  Group " << m_group++ << " workers=";
            dumpSet(key, 0, usedIds);
            *m_dumpp << " writers=";
            dumpSet(key, usedIds, key.size());
            *m_dumpp << '\n';
        }
        for (const AstVar* const varp : varps) {
            const auto it = m_taskSets.find(varp);
            // Unaccessed variables have no task sets.
            const MTaskIdVec& tasks = it == m_taskSets.end() ? key : it->second;
            if (!nWorkers) {
                ++m_statNoAffinity;
            } else {
                const MTaskIdVec accesses(tasks.begin(), tasks.begin() + usedIds);
                const MTaskIdVec writers(tasks.begin() + usedIds, tasks.end());
                writersToAccesses[writers].emplace(accesses);
                if (nWorkers == 1) {
                    ++m_statSingleWorker;
                } else if (std::find(writers.begin(), writers.end(), true) == writers.end()) {
                    ++m_statSharedReadOnly;
                } else {
                    ++m_statSharedWritten;
                }
            }
            if (m_dumpp) {
                *m_dumpp << "    " << varp->name() << " tasks=";
                dumpSet(tasks, 0, usedIds);
                *m_dumpp << " writers=";
                dumpSet(tasks, usedIds, tasks.size());
                *m_dumpp << " aligned=" << varp->mtaskCacheLineAlign() << '\n';
            }
        }
        for (const auto& pair : writersToAccesses) {
            m_statWorkerEliminated += pair.second.size() - 1;
        }
        if (nWorkers == 1) m_statSingleWorkerEliminated += writersToAccesses.size() - 1;
        if (nWorkers > 1 && !m_sharedWorkers.emplace(workers).second)
            ++m_statSharedWriterAdditional;
    }
    void report() const {
        // Add once, including zeros, so every variable category and transformation is visible.
        V3Stats::addStat("VariableOrder, no-affinity variables", m_statNoAffinity);
        V3Stats::addStat("VariableOrder, single-worker variables", m_statSingleWorker);
        V3Stats::addStat("VariableOrder, shared read-only variables", m_statSharedReadOnly);
        V3Stats::addStat("VariableOrder, shared written variables", m_statSharedWritten);
        V3Stats::addStat("VariableOrder, groups eliminated by worker affinity",
                         m_statWorkerEliminated);
        V3Stats::addStat("VariableOrder, groups eliminated for single-worker variables",
                         m_statSingleWorkerEliminated);
        V3Stats::addStat("VariableOrder, additional groups for shared writers",
                         m_statSharedWriterAdditional);
    }
};

// Trace through code reachable form an MTask and annotate referenced variabels
class GatherMTaskAffinity final : VNVisitorConst {
    // NODE STATE
    //  AstCFunc::user1()  // bool: Already traced this function
    //  AstVar::user1()  // bool: Already traced this variable
    const VNUser1InUse m_user1InUse;

    // STATE
    MTaskAffinityMap& m_results;  // The result map being built;
    VariableOrderStats* const m_statsp;  // Optional diagnostic collector
    const uint32_t m_id;  // Representative ID of the scheduled worker being analysed
    const uint32_t m_writeId;  // Preserve the precise task responsible for writes
    const size_t m_usedIds = ExecMTask::numUsedIds();  // Value of max id + 1

    // CONSTRUCTOR
    GatherMTaskAffinity(const ExecMTask* mTaskp, MTaskAffinityMap& results,
                        VariableOrderStats* statsp)
        : m_results{results}
        , m_statsp{statsp}
        , m_id{mTaskp->affinityId()}
        , m_writeId{mTaskp->id()} {
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
                                            std::forward_as_tuple(2 * m_usedIds))
                                   .first->second;
        affinity[m_id] = true;
        if (nodep->access().isWriteOrRW()) affinity[m_usedIds + m_writeId] = true;
        if (m_statsp) {
            MTaskIdVec& tasks = m_statsp->taskSets().emplace(varp, 2 * m_usedIds).first->second;
            tasks[m_writeId] = true;
            if (nodep->access().isWriteOrRW()) tasks[m_usedIds + m_writeId] = true;
        }
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
    static void apply(const ExecMTask* mTaskp, MTaskAffinityMap& results,
                      VariableOrderStats* statsp) {
        GatherMTaskAffinity{mTaskp, results, statsp};
    }
};

struct VarAttributes final {
    uint8_t stratum;  // Roughly equivalent to alignment requirement, to avoid padding
    bool anonOk;  // Can be emitted as part of anonymous structure
};
class VariableOrder final {
    std::unordered_map<const AstVar*, VarAttributes> m_attributes;  // Per-variable sort attributes

    const MTaskAffinityMap& m_mTaskAffinity;  // Final worker/writer grouping keys
    std::vector<AstVar*>& m_varps;  // Module variables in emission order
    VariableOrderStats* const m_statsp;  // Optional diagnostic collector

    VariableOrder(AstNodeModule* modp, const MTaskAffinityMap& mTaskAffinity,
                  std::vector<AstVar*>& varps, VariableOrderStats* statsp)
        : m_mTaskAffinity{mTaskAffinity}
        , m_varps{varps}
        , m_statsp{statsp} {
        if (m_statsp) m_statsp->startModule(modp);
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

    // Sort by MTask-affinity first, then the same as simpleSortVars
    void mtaskSortVars(std::vector<AstVar*>& varps) {
        // Map from "MTask affinity" -> "variable list"
        std::map<MTaskIdVec, std::vector<AstVar*>> m2v;
        const MTaskIdVec emptyVec(2 * ExecMTask::numUsedIds(), false);
        for (AstVar* const varp : varps) {
            const auto it = m_mTaskAffinity.find(varp);
            const MTaskIdVec& key = it == m_mTaskAffinity.end() ? emptyVec : it->second;
            m2v[key].push_back(varp);
        }

        varps.clear();

        // Helper function to sort given vector, then append to 'varps'
        const auto sortAndAppend
            = [this, &varps](std::vector<AstVar*>& subVarps, bool alignFirst) {
                  simpleSortVars(subVarps);
                  bool aligned = !alignFirst;
                  for (AstVar* const varp : subVarps) {
                      if (!aligned && !varp->isStatic()) {
                          varp->mtaskCacheLineAlign(true);
                          V3Stats::addStatSum("VariableOrder, MTask aligned group starts", 1);
                          aligned = true;
                      }
                      varps.push_back(varp);
                  }
              };

        // Sort non-empty MTask affinity groups in the map's deterministic key order. This keeps
        // memory linear in the number of affinity groups, unlike the old complete
        // pairwise-distance ordering.
        size_t affinityGroups = 0;
        for (auto& pair : m2v) {
            if (emptyAffinity(pair.first)) continue;
            sortAndAppend(pair.second, true);
            if (m_statsp) m_statsp->recordGroup(pair.first, pair.second);
            ++affinityGroups;
        }

        // Finally add the variables with no known MTask affinity
        sortAndAppend(m2v[emptyVec], false);
        if (m_statsp) m_statsp->recordGroup(emptyVec, m2v[emptyVec]);

        V3Stats::addStatSum("VariableOrder, MTask affinity groups", affinityGroups);
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
                              std::vector<AstVar*>& varps, VariableOrderStats* statsp) {
        VariableOrder{modp, mTaskAffinity, varps, statsp};
    }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");

    MTaskAffinityMap mTaskAffinity;
    VariableOrderStats stats;
    VariableOrderStats* const statsp
        = v3Global.opt.mtasks() && (v3Global.opt.stats() || dumpLevel()) ? &stats : nullptr;

    // Gather MTask affinities
    if (v3Global.opt.mtasks()) {
        netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
            for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                GatherMTaskAffinity::apply(vtx.as<const ExecMTask>(), mTaskAffinity, statsp);
            }
        });
        // Writer identities only separate state shared between workers. State accessed by a
        // single worker cannot be falsely shared, so group it by that worker alone.
        const size_t usedIds = ExecMTask::numUsedIds();
        for (auto& pair : mTaskAffinity) {
            MTaskIdVec& affinity = pair.second;
            const auto writersBegin = affinity.begin() + usedIds;
            if (std::count(affinity.begin(), writersBegin, true) == 1) {
                std::fill(writersBegin, affinity.end(), false);
            }
        }
    }
    if (v3Global.opt.stats()) V3Stats::statsStage("variableorder-gather");

    // Sort variables for each module
    std::unordered_map<AstNodeModule*, std::vector<AstVar*>> sortedVars;
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp;
         modp = VN_AS(modp->nextp(), NodeModule)) {
        VariableOrder::processModule(modp, mTaskAffinity, sortedVars[modp], statsp);
    }
    if (statsp && v3Global.opt.stats()) stats.report();
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
