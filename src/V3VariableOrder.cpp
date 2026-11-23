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
// RepCut storage roles are an explicit exception: candidate and state roles have
// separate boundaries, and the trailing ordinary variables form their own group.
// Within a role, fields read by the same set of worker slots are grouped and
// ordered by first use. This keeps a worker's private candidate line separate
// from published state while another worker is still reading it.
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3VariableOrder.h"

#include "V3ExecGraph.h"
#include "V3RepCut.h"
#include "V3Stats.h"
#include "V3VNUserAllocator.h"

#include <algorithm>
#include <cstdint>
#include <map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

using MTaskIdVec = std::vector<bool>;  // Used as a bit-set indexed by MTask ID
// Writing MTasks of each variable accessed by any MTask
using MTaskWritersMap = std::unordered_map<const AstVar*, MTaskIdVec>;

struct RepCutReaders final {
    MTaskIdVec readers;
    size_t firstRead = 0;
};
using RepCutReaderMap = std::unordered_map<const AstVar*, RepCutReaders>;

// Follow actual worker calls after optimization and chunk construction. Read
// affinity uses physical worker slots, so edge and non-edge jobs share identities.
class GatherRepCutAccess final : VNVisitorConst {
    const VNUser2InUse m_user2InUse;  // AstCFunc::user2: Already visited this job
    RepCutReaderMap& m_readers;  // Worker read sets and first-use order by model field
    const std::unordered_set<const AstVar*>& m_fields;
    std::unordered_set<const AstVar*>& m_written;
    const uint32_t m_thread;  // Physical worker slot being traversed
    size_t& m_order;  // Next sequence index assigned to a variable read

    void visit(AstNodeVarRef* nodep) override {
        const AstVar* const varp = nodep->varp();
        if (!m_fields.count(varp)) return;  // Stack temporaries need no model layout.
        if (nodep->access().isWriteOrRW()) {
            const uint32_t group = varp->repcutStorageGroup();
            const uint32_t threads = v3Global.opt.threads();
            if (group) {
                UASSERT_OBJ((V3RepCut::storageOwner(group) + threads - 1) % threads == m_thread,
                            varp, "RepCut worker writes another owner's storage");
            }
            m_written.insert(varp);
        }
        if (nodep->access().isReadOrRW()) {
            auto it = m_readers.find(varp);
            if (it == m_readers.end()) {
                it = m_readers
                         .emplace(varp, RepCutReaders{MTaskIdVec(v3Global.opt.threads(), false),
                                                      m_order})
                         .first;
            }
            ++m_order;
            it->second.readers[m_thread] = true;
        }
    }
    void visit(AstCFunc* nodep) override {
        if (!nodep->user2SetOnce()) iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        iterateConst(nodep->funcp());
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    GatherRepCutAccess(const ExecMTask* taskp, RepCutReaderMap& readers,
                       const std::unordered_set<const AstVar*>& fields,
                       std::unordered_set<const AstVar*>& written, size_t& order)
        : m_readers{readers}
        , m_fields{fields}
        , m_written{written}
        , m_thread{static_cast<uint32_t>(taskp->fixedThread())}
        , m_order{order} {
        UASSERT_OBJ(taskp->hasFixedThread(), taskp->funcp(), "RepCut job lacks a fixed worker");
        iterateConst(taskp->funcp());
    }
};

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
    ~GatherMTaskWriters() override = default;
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

class VariableOrder final {
    // NODE STATE
    //  AstVar::user1()   ->   uint64_t: Stratum, roughly equivalent to alignment
    //                                   requirement, to avoid padding
    const VNUser1InUse m_user1InUse;

    const MTaskWritersMap& m_mTaskWriters;  // Writer mtasks of each variable
    const RepCutReaderMap& m_repcutReaders;  // Reader worker slots, with first-use order

    VariableOrder(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                  const RepCutReaderMap& repcutReaders)
        : m_mTaskWriters{mTaskWriters}
        , m_repcutReaders{repcutReaders} {
        orderModuleVars(modp);
    }
    ~VariableOrder() = default;
    VL_UNCOPYABLE(VariableOrder);

    //######################################################################

    // Simple sort by stratum
    void simpleSortVars(std::vector<AstVar*>& varps) {
        stable_sort(varps.begin(), varps.end(), [](const AstVar* ap, const AstVar* bp) -> bool {
            return ap->user1() < bp->user1();
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

    // Explicit writer ownership takes precedence over read affinity. Candidate
    // and state roles have separate boundaries, including the trailing ordinary
    // variables. Early state writes cannot invalidate neighboring shared-state
    // fields while another worker is still reading them during next evaluation.
    void repcutSortVars(std::vector<AstVar*>& varps) {
        std::map<uint32_t, std::vector<AstVar*>> groups;
        for (AstVar* const varp : varps) groups[varp->repcutStorageGroup()].push_back(varp);
        varps.clear();
        const auto append = [this, &varps](std::vector<AstVar*>& group, bool& aligned) {
            // First-use order reflects optimized sequential evaluation. Keep that
            // order within equal alignment strata rather than adding padding
            // between every differently sized field.
            std::stable_sort(group.begin(), group.end(),
                             [this](const AstVar* ap, const AstVar* bp) {
                                 const auto a = m_repcutReaders.find(ap);
                                 const auto b = m_repcutReaders.find(bp);
                                 if (a == m_repcutReaders.end()) return false;
                                 if (b == m_repcutReaders.end()) return true;
                                 return a->second.firstRead < b->second.firstRead;
                             });
            simpleSortVars(group);
            for (AstVar* const varp : group) {
                if (!aligned && varp->isModelState()) {
                    varp->mtaskCacheLineAlign(true);
                    aligned = true;
                }
                varps.push_back(varp);
            }
        };
        size_t readerGroups = 0;
        const MTaskIdVec noReaders(v3Global.opt.threads(), false);
        for (const auto& pair : groups) {
            if (!pair.first) continue;
            std::map<MTaskIdVec, std::vector<AstVar*>> byReaders;
            for (AstVar* const varp : pair.second) {
                const auto it = m_repcutReaders.find(varp);
                byReaders[it == m_repcutReaders.end() ? noReaders : it->second.readers].push_back(
                    varp);
            }
            bool aligned = false;
            for (auto& readers : byReaders) append(readers.second, aligned);
            readerGroups += byReaders.size();
        }
        // Ordinary fields retain their previous order and a separate boundary.
        simpleSortVars(groups[0]);
        bool aligned = false;
        for (AstVar* const varp : groups[0]) {
            if (!aligned && varp->isModelState()) {
                varp->mtaskCacheLineAlign(true);
                aligned = true;
            }
            varps.push_back(varp);
        }
        V3Stats::addStatSum("VariableOrder, RepCut reader groups", readerGroups);
        V3Stats::addStatSum("VariableOrder, RepCut storage groups", groups.size() - 1);
    }

    // cppcheck-suppress constParameterPointer
    void orderModuleVars(AstNodeModule* modp) {
        // Top level ports stay first, in source order (--lib-create wrapper must match original)
        std::vector<AstVar*> portps;
        // Followed by trivially constructible variables
        std::vector<AstVar*> trivps;
        // Followed by not trivially constructible variables
        std::vector<AstVar*> nontps;
        // Followed by variables that are not model state, in source order
        std::vector<AstVar*> restps;

        // Gather variables, compute stratum
        for (AstNode* const nodep : modp->stmtspList()) {
            if (AstVar* const varp = VN_CAST(nodep, Var)) {
                if (varp->isPrimaryIO()) {
                    portps.push_back(varp);
                    continue;
                }
                if (!varp->isModelState()) {
                    restps.push_back(varp);
                    continue;
                }

                if (varp->isTriviallyConstructible()) {
                    trivps.push_back(varp);
                } else {
                    nontps.push_back(varp);
                }

                AstNodeDType* const dtypep = varp->dtypeSkipRefp();
                const int sigbytes = dtypep->widthAlignBytes();
                const uint64_t stratum = VN_IS(dtypep, UnpackArrayDType)                  ? 9
                                         : (varp->basicp() && varp->basicp()->isString()) ? 4
                                         : (varp->basicp() && varp->basicp()->isOpaque()) ? 8
                                         : (sigbytes == 8)                                ? 3
                                         : (sigbytes == 4)                                ? 2
                                         : (sigbytes == 2)                                ? 1
                                         : (sigbytes == 1)                                ? 0
                                                                                          : 10;
                varp->user1(stratum);
            }
        }

        // Sort them. RepCut storage groups live in the trivially
        // constructible block; non-trivial fields keep master's layout and
        // their explicit constructor/destructor emission.
        const bool repcutTriv = std::any_of(trivps.begin(), trivps.end(), [](const AstVar* varp) {
            return varp->repcutStorageGroup() != 0;
        });
        const bool repcutNon = std::any_of(nontps.begin(), nontps.end(), [](const AstVar* varp) {
            return varp->repcutStorageGroup() != 0;
        });
        if (repcutTriv) {
            repcutSortVars(trivps);
        } else if (v3Global.opt.mtasks()) {
            mtaskSortVars(trivps);
        } else {
            simpleSortVars(trivps);
        }
        if (repcutNon) {
            repcutSortVars(nontps);
        } else if (v3Global.opt.mtasks()) {
            mtaskSortVars(nontps);
        } else {
            simpleSortVars(nontps);
        }

        // Insert them back under the module, in the new order, but at
        // the front of the list so they come out first in dumps/JSON.
        AstNode* nodesp = nullptr;
        for (AstVar* const varp : portps)
            nodesp = AstNode::addNextNull(nodesp, varp->unlinkFrBack());
        for (AstVar* const varp : trivps)
            nodesp = AstNode::addNextNull(nodesp, varp->unlinkFrBack());
        for (AstVar* const varp : nontps)
            nodesp = AstNode::addNextNull(nodesp, varp->unlinkFrBack());
        for (AstVar* const varp : restps)
            nodesp = AstNode::addNextNull(nodesp, varp->unlinkFrBack());
        modp->prependStmtsp(nodesp);
    }

public:
    static void apply(AstNodeModule* modp, const MTaskWritersMap& mTaskWriters,
                      const RepCutReaderMap& repcutReaders) {
        VariableOrder{modp, mTaskWriters, repcutReaders};
    }
};

//######################################################################
// V3VariableOrder static functions

void V3VariableOrder::orderAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ":");

    MTaskWritersMap mTaskWriters;
    RepCutReaderMap repcutReaders;
    std::unordered_set<const AstVar*> repcutWritten;
    std::unordered_set<const AstVar*> modelFields;
    for (AstNodeModule* const modp : v3Global.rootp()->modulespList()) {
        for (AstNode* const nodep : modp->stmtspList()) {
            if (const AstVar* const varp = VN_CAST(nodep, Var)) modelFields.insert(varp);
        }
    }

    // Gather MTask writers and RepCut worker read affinity
    if (v3Global.opt.mtasks()) {
        size_t repcutReadOrder = 0;
        netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
            for (const V3GraphVertex& vtx : execGraphp->depGraphp()->vertices()) {
                const ExecMTask* const taskp = vtx.as<const ExecMTask>();
                GatherMTaskWriters::apply(taskp, mTaskWriters);
                if (taskp->funcp()->isRepCut()) {
                    GatherRepCutAccess{taskp, repcutReaders, modelFields, repcutWritten,
                                       repcutReadOrder};
                }
            }
        });
    }
    if (!repcutWritten.empty()) {
        V3Stats::addStat("VariableOrder, RepCut audited worker-written fields",
                         repcutWritten.size());
    }

    // Sort variables of each module
    for (AstNodeModule* const modp : v3Global.rootp()->modulespList()) {
        if (modp->isConstPool()) continue;
        VariableOrder::apply(modp, mTaskWriters, repcutReaders);
    }

    V3Global::dumpCheckGlobalTree("variableorder", 0, dumpTreeEitherLevel() >= 3);
}
