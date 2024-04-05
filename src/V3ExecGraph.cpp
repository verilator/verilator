// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstExecGraph code construction
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3ExecGraph.h"

#include "V3Config.h"
#include "V3EmitCBase.h"
#include "V3File.h"
#include "V3GraphStream.h"
#include "V3Hasher.h"
#include "V3InstrCount.h"
#include "V3Os.h"
#include "V3Stats.h"

#include <memory>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

ExecMTask::ExecMTask(V3Graph* graphp, AstMTaskBody* bodyp) VL_MT_DISABLED  //
    : V3GraphVertex{graphp},
      m_bodyp{bodyp},
      m_id{s_nextId++},
      m_hashName{V3Hasher::uncachedHash(bodyp).toString()} {
    UASSERT_OBJ(bodyp->stmtsp(), bodyp, "AstMTaskBody should already be populated for hashing");
    UASSERT_OBJ(!bodyp->execMTaskp(), bodyp, "AstMTaskBody already linked to an ExecMTask");
    bodyp->execMTaskp(this);
}

void ExecMTask::dump(std::ostream& str) const {
    str << name() << "." << cvtToHex(this);
    if (priority() || cost()) str << " [pr=" << priority() << " c=" << cvtToStr(cost()) << "]";
}

uint32_t ExecMTask::s_nextId = 0;

namespace V3ExecGraph {

//######################################################################
// ThreadSchedule

// The thread schedule, containing all information needed later. Note that this is a simple
// aggregate data type and the only way to get hold of an instance of it is via
// PackThreads::pack, which is moved from there and is const, which means we can only acquire a
// const reference to is so no further modifications are allowed, so all members are public
// (attributes).
class ThreadSchedule final {
    friend class PackThreads;

public:
    // CONSTANTS
    static constexpr uint32_t UNASSIGNED = 0xffffffff;

    // TYPES
    struct MTaskState final {
        uint32_t completionTime = 0;  // Estimated time this mtask will complete
        uint32_t threadId = UNASSIGNED;  // Thread id this MTask is assigned to
        const ExecMTask* nextp = nullptr;  // Next MTask on same thread after this
    };

    // MEMBERS
    // Allocation of sequence of MTasks to threads. Can be considered a map from thread ID to
    // the sequence of MTasks to be executed by that thread.
    std::vector<std::vector<const ExecMTask*>> threads;

    // State for each mtask.
    std::unordered_map<const ExecMTask*, MTaskState> mtaskState;

    uint32_t threadId(const ExecMTask* mtaskp) const {
        const auto& it = mtaskState.find(mtaskp);
        return it != mtaskState.end() ? it->second.threadId : UNASSIGNED;
    }

private:
    explicit ThreadSchedule(uint32_t nThreads)
        : threads{nThreads} {}
    VL_UNCOPYABLE(ThreadSchedule);  // But movable
    ThreadSchedule(ThreadSchedule&&) = default;
    ThreadSchedule& operator=(ThreadSchedule&&) = default;

    // Debugging
    void dumpDotFile(const V3Graph& graph, const string& filename) const {
        // This generates a file used by graphviz, https://www.graphviz.org
        const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
        if (logp->fail()) v3fatal("Can't write " << filename);

        // Header
        *logp << "digraph v3graph {\n";
        *logp << "  graph[layout=\"neato\" labelloc=t labeljust=l label=\"" << filename << "\"]\n";
        *logp << "  node[shape=\"rect\" ratio=\"fill\" fixedsize=true]\n";

        // Thread labels
        *logp << "\n  // Threads\n";
        const int threadBoxWidth = 2;
        for (int i = 0; i < v3Global.opt.threads(); i++) {
            *logp << "  t" << i << " [label=\"Thread " << i << "\" width=" << threadBoxWidth
                  << " pos=\"" << (-threadBoxWidth / 2) << "," << -i
                  << "!\" style=\"filled\" fillcolor=\"grey\"] \n";
        }

        // MTask nodes
        *logp << "\n  // MTasks\n";

        // Find minimum cost MTask for scaling MTask node widths
        uint32_t minCost = UINT32_MAX;
        for (const V3GraphVertex& vtx : graph.vertices()) {
            if (const ExecMTask* const mtaskp = vtx.cast<const ExecMTask>()) {
                minCost = minCost > mtaskp->cost() ? mtaskp->cost() : minCost;
            }
        }
        const double minWidth = 2.0;
        const auto mtaskXPos = [&](const ExecMTask* mtaskp, const double nodeWidth) {
            const double startPosX = (minWidth * startTime(mtaskp)) / minCost;
            return nodeWidth / minWidth + startPosX;
        };

        const auto emitMTask = [&](const ExecMTask* mtaskp) {
            const int thread = threadId(mtaskp);
            const double nodeWidth = minWidth * (static_cast<double>(mtaskp->cost()) / minCost);
            const double x = mtaskXPos(mtaskp, nodeWidth);
            const int y = -thread;
            const string label = "label=\"" + mtaskp->name() + " (" + cvtToStr(startTime(mtaskp))
                                 + ":" + std::to_string(endTime(mtaskp)) + ")" + "\"";
            *logp << "  " << mtaskp->name() << " [" << label << " width=" << nodeWidth << " pos=\""
                  << x << "," << y << "!\"]\n";
        };

        // Emit MTasks
        for (const V3GraphVertex& vtx : graph.vertices()) {
            if (const ExecMTask* const mtaskp = vtx.cast<const ExecMTask>()) emitMTask(mtaskp);
        }

        // Emit MTask dependency edges
        *logp << "\n  // MTask dependencies\n";
        for (const V3GraphVertex& vtx : graph.vertices()) {
            if (const ExecMTask* const mtaskp = vtx.cast<const ExecMTask>()) {
                for (const V3GraphEdge& edge : mtaskp->outEdges()) {
                    const V3GraphVertex* const top = edge.top();
                    *logp << "  " << vtx.name() << " -> " << top->name() << "\n";
                }
            }
        }

        // Trailer
        *logp << "}\n";
        logp->close();
    }

    // Variant of dumpDotFilePrefixed without --dump option check
    void dumpDotFilePrefixedAlways(const V3Graph& graph, const string& nameComment) const {
        dumpDotFile(graph, v3Global.debugFilename(nameComment) + ".dot");
    }

public:
    // Returns the number of cross-thread dependencies of the given MTask. If > 0, the MTask must
    // test whether its dependencies are ready before starting, and therefore may need to block.
    uint32_t crossThreadDependencies(const ExecMTask* mtaskp) const {
        const uint32_t thisThreadId = threadId(mtaskp);
        uint32_t result = 0;
        for (const V3GraphEdge& edge : mtaskp->inEdges()) {
            const ExecMTask* const prevp = edge.fromp()->as<ExecMTask>();
            if (threadId(prevp) != thisThreadId) ++result;
        }
        return result;
    }

    uint32_t startTime(const ExecMTask* mtaskp) const {
        return mtaskState.at(mtaskp).completionTime - mtaskp->cost();
    }
    uint32_t endTime(const ExecMTask* mtaskp) const {
        return mtaskState.at(mtaskp).completionTime;
    }
};

//######################################################################
// PackThreads

// Statically pack tasks into threads.
//
// The simplest thing that could possibly work would be to assume that our
// predictions of task runtimes are precise, and that every thread will
// make progress at an equal rate. Simulate a single "clock", pack the the
// highest priority ready task into whatever thread becomes ready earliest,
// repeating until no tasks remain.
//
// That doesn't work well, as our predictions of task runtimes have wide
// error bars (+/- 60% is typical.)
//
// So be a little more clever: let each task have a different end time,
// depending on which thread is looking. Be a little bit pessimistic when
// thread A checks the end time of an mtask running on thread B. This extra
// "padding" avoids tight "layovers" at cross-thread dependencies.
class PackThreads final {
    // TYPES
    struct MTaskCmp final {
        bool operator()(const ExecMTask* ap, const ExecMTask* bp) const {
            return ap->id() < bp->id();
        }
    };

    // MEMBERS
    const uint32_t m_nThreads;  // Number of threads
    const uint32_t m_sandbagNumerator;  // Numerator padding for est runtime
    const uint32_t m_sandbagDenom;  // Denominator padding for est runtime

    // CONSTRUCTORS
    explicit PackThreads(uint32_t nThreads = v3Global.opt.threads(),
                         unsigned sandbagNumerator = 30, unsigned sandbagDenom = 100)
        : m_nThreads{nThreads}
        , m_sandbagNumerator{sandbagNumerator}
        , m_sandbagDenom{sandbagDenom} {}
    ~PackThreads() = default;
    VL_UNCOPYABLE(PackThreads);

    // METHODS
    uint32_t completionTime(const ThreadSchedule& schedule, const ExecMTask* mtaskp,
                            uint32_t threadId) {
        const ThreadSchedule::MTaskState& state = schedule.mtaskState.at(mtaskp);
        UASSERT(state.threadId != ThreadSchedule::UNASSIGNED, "Mtask should have assigned thread");
        if (threadId == state.threadId) {
            // No overhead on same thread
            return state.completionTime;
        }

        // Add some padding to the estimated runtime when looking from
        // another thread
        uint32_t sandbaggedEndTime
            = state.completionTime + (m_sandbagNumerator * mtaskp->cost()) / m_sandbagDenom;

        // If task B is packed after task A on thread 0, don't let thread 1
        // think that A finishes earlier than thread 0 thinks that B
        // finishes, otherwise we get priority inversions and fail the self
        // test.
        if (state.nextp) {
            const uint32_t successorEndTime
                = completionTime(schedule, state.nextp, state.threadId);
            if ((sandbaggedEndTime >= successorEndTime) && (successorEndTime > 1)) {
                sandbaggedEndTime = successorEndTime - 1;
            }
        }

        UINFO(6, "Sandbagged end time for " << mtaskp->name() << " on th " << threadId << " = "
                                            << sandbaggedEndTime << endl);
        return sandbaggedEndTime;
    }

    bool isReady(ThreadSchedule& schedule, const ExecMTask* mtaskp) {
        for (const V3GraphEdge& edgeIn : mtaskp->inEdges()) {
            const ExecMTask* const prevp = edgeIn.fromp()->as<const ExecMTask>();
            if (schedule.threadId(prevp) == ThreadSchedule::UNASSIGNED) {
                // This predecessor is not assigned yet
                return false;
            }
        }
        return true;
    }

    // Pack an MTasks from given graph into m_nThreads threads, return the schedule.
    ThreadSchedule pack(V3Graph& mtaskGraph) {
        // The result
        ThreadSchedule schedule{m_nThreads};

        // Time each thread is occupied until
        std::vector<uint32_t> busyUntil(m_nThreads, 0);

        // MTasks ready to be assigned next. All their dependencies are already assigned.
        std::set<ExecMTask*, MTaskCmp> readyMTasks;

        // Build initial ready list
        for (V3GraphVertex& vtx : mtaskGraph.vertices()) {
            ExecMTask* const mtaskp = vtx.as<ExecMTask>();
            if (isReady(schedule, mtaskp)) readyMTasks.insert(mtaskp);
        }

        while (!readyMTasks.empty()) {
            // For each task in the ready set, compute when it might start
            // on each thread (in that thread's local time frame.)
            uint32_t bestTime = 0xffffffff;
            uint32_t bestThreadId = 0;
            ExecMTask* bestMtaskp = nullptr;  // Todo: const ExecMTask*
            for (uint32_t threadId = 0; threadId < m_nThreads; ++threadId) {
                for (ExecMTask* const mtaskp : readyMTasks) {
                    uint32_t timeBegin = busyUntil[threadId];
                    if (timeBegin > bestTime) {
                        UINFO(6, "th " << threadId << " busy until " << timeBegin
                                       << ", later than bestTime " << bestTime
                                       << ", skipping thread.\n");
                        break;
                    }
                    for (const V3GraphEdge& edge : mtaskp->inEdges()) {
                        const ExecMTask* const priorp = edge.fromp()->as<ExecMTask>();
                        const uint32_t priorEndTime = completionTime(schedule, priorp, threadId);
                        if (priorEndTime > timeBegin) timeBegin = priorEndTime;
                    }
                    UINFO(6, "Task " << mtaskp->name() << " start at " << timeBegin
                                     << " on thread " << threadId << endl);
                    if ((timeBegin < bestTime)
                        || ((timeBegin == bestTime)
                            && bestMtaskp  // Redundant, but appeases static analysis tools
                            && (mtaskp->priority() > bestMtaskp->priority()))) {
                        bestTime = timeBegin;
                        bestThreadId = threadId;
                        bestMtaskp = mtaskp;
                    }
                }
            }

            UASSERT(bestMtaskp, "Should have found some task");
            UINFO(6, "Will schedule " << bestMtaskp->name() << " onto thread " << bestThreadId
                                      << endl);

            // Reference to thread in schedule we are assigning this MTask to.
            std::vector<const ExecMTask*>& bestThread = schedule.threads[bestThreadId];

            // Update algorithm state
            bestMtaskp->predictStart(bestTime);  // Only for gantt reporting
            const uint32_t bestEndTime = bestTime + bestMtaskp->cost();
            schedule.mtaskState[bestMtaskp].completionTime = bestEndTime;
            schedule.mtaskState[bestMtaskp].threadId = bestThreadId;
            if (!bestThread.empty()) schedule.mtaskState[bestThread.back()].nextp = bestMtaskp;
            busyUntil[bestThreadId] = bestEndTime;

            // Add the MTask to the schedule
            bestThread.push_back(bestMtaskp);

            // Update the ready list
            const size_t erased = readyMTasks.erase(bestMtaskp);
            UASSERT_OBJ(erased > 0, bestMtaskp, "Should have erased something?");
            for (V3GraphEdge& edgeOut : bestMtaskp->outEdges()) {
                ExecMTask* const nextp = edgeOut.top()->as<ExecMTask>();
                // Dependent MTask should not yet be assigned to a thread
                UASSERT(schedule.threadId(nextp) == ThreadSchedule::UNASSIGNED,
                        "Tasks after one being assigned should not be assigned yet");
                // Dependent MTask should not be ready yet, since dependency is just being assigned
                UASSERT_OBJ(readyMTasks.find(nextp) == readyMTasks.end(), nextp,
                            "Tasks after one being assigned should not be ready");
                if (isReady(schedule, nextp)) {
                    readyMTasks.insert(nextp);
                    UINFO(6, "Inserted " << nextp->name() << " into ready\n");
                }
            }
        }

        if (dumpGraphLevel() >= 4) schedule.dumpDotFilePrefixedAlways(mtaskGraph, "schedule");

        return schedule;
    }

public:
    // SELF TEST
    static void selfTest() {
        V3Graph graph;
        FileLine* const flp = v3Global.rootp()->fileline();
        std::vector<AstMTaskBody*> mTaskBodyps;
        const auto makeBody = [&]() {
            AstMTaskBody* const bodyp = new AstMTaskBody{flp};
            mTaskBodyps.push_back(bodyp);
            bodyp->addStmtsp(new AstComment{flp, ""});
            return bodyp;
        };
        ExecMTask* const t0 = new ExecMTask{&graph, makeBody()};
        t0->cost(1000);
        t0->priority(1100);
        ExecMTask* const t1 = new ExecMTask{&graph, makeBody()};
        t1->cost(100);
        t1->priority(100);
        ExecMTask* const t2 = new ExecMTask{&graph, makeBody()};
        t2->cost(100);
        t2->priority(100);

        new V3GraphEdge{&graph, t0, t1, 1};
        new V3GraphEdge{&graph, t0, t2, 1};

        PackThreads packer{2,  // Threads
                           3,  // Sandbag numerator
                           10};  // Sandbag denom
        const ThreadSchedule& schedule = packer.pack(graph);

        UASSERT_SELFTEST(size_t, schedule.threads.size(), 2);

        UASSERT_SELFTEST(size_t, schedule.threads[0].size(), 2);
        UASSERT_SELFTEST(size_t, schedule.threads[1].size(), 1);

        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[0][0], t0);
        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[0][1], t1);
        UASSERT_SELFTEST(const ExecMTask*, schedule.threads[1][0], t2);

        UASSERT_SELFTEST(size_t, schedule.mtaskState.size(), 3);

        UASSERT_SELFTEST(uint32_t, schedule.threadId(t0), 0);
        UASSERT_SELFTEST(uint32_t, schedule.threadId(t1), 0);
        UASSERT_SELFTEST(uint32_t, schedule.threadId(t2), 1);

        // On its native thread, we see the actual end time for t0:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t0, 0), 1000);
        // On the other thread, we see a sandbagged end time which does not
        // exceed the t1 end time:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t0, 1), 1099);

        // Actual end time on native thread:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t1, 0), 1100);
        // Sandbagged end time seen on thread 1.  Note it does not compound
        // with t0's sandbagged time; compounding caused trouble in
        // practice.
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t1, 1), 1130);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t2, 0), 1229);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(schedule, t2, 1), 1199);

        for (AstNode* const nodep : mTaskBodyps) nodep->deleteTree();
    }

    static const ThreadSchedule apply(V3Graph& mtaskGraph) {
        return PackThreads{}.pack(mtaskGraph);
    }
};

using EstimateAndProfiled = std::pair<uint64_t, uint64_t>;  // cost est, cost profiled
using Costs = std::unordered_map<uint32_t, EstimateAndProfiled>;

void normalizeCosts(Costs& costs) {
    const auto scaleCost = [](uint64_t value, double multiplier) {
        double scaled = static_cast<double>(value) * multiplier;
        if (value && scaled < 1) scaled = 1;
        return static_cast<uint64_t>(scaled);
    };

    // For all costs with a profile, compute sum
    uint64_t sumCostProfiled = 0;  // For data with estimate and profile
    uint64_t sumCostEstimate = 0;  // For data with estimate and profile
    for (const auto& est : costs) {
        if (est.second.second) {
            sumCostEstimate += est.second.first;
            sumCostProfiled += est.second.second;
        }
    }

    if (sumCostEstimate) {
        // For data where we don't have profiled data, compute how much to
        // scale up/down the estimate to make on same relative scale as
        // profiled data.  (Improves results if only a few profiles missing.)
        const double estToProfile
            = static_cast<double>(sumCostProfiled) / static_cast<double>(sumCostEstimate);
        UINFO(5, "Estimated data needs scaling by "
                     << estToProfile << ", sumCostProfiled=" << sumCostProfiled
                     << " sumCostEstimate=" << sumCostEstimate << endl);
        for (auto& est : costs) {
            uint64_t& costEstimate = est.second.first;
            costEstimate = scaleCost(costEstimate, estToProfile);
        }
    }

    // COSTS can overflow a uint32.  Using maximum value of costs, scale all down
    uint64_t maxCost = 0;
    for (auto& est : costs) {
        const uint64_t& costEstimate = est.second.first;
        const uint64_t& costProfiled = est.second.second;
        if (maxCost < costEstimate) maxCost = costEstimate;
        if (maxCost < costProfiled) maxCost = costProfiled;
        UINFO(9,
              "Post uint scale: ce = " << est.second.first << " cp=" << est.second.second << endl);
    }
    const uint64_t scaleDownTo = 10000000;  // Extra room for future algorithms to add costs
    if (maxCost > scaleDownTo) {
        const double scaleup = static_cast<double>(scaleDownTo) / static_cast<double>(maxCost);
        UINFO(5, "Scaling data to within 32-bits by multiply by=" << scaleup << ", maxCost="
                                                                  << maxCost << endl);
        for (auto& est : costs) {
            est.second.first = scaleCost(est.second.first, scaleup);
            est.second.second = scaleCost(est.second.second, scaleup);
        }
    }
}

void fillinCosts(V3Graph* execMTaskGraphp) {
    // Pass 1: See what profiling data applies
    Costs costs;  // For each mtask, costs

    for (V3GraphVertex& vtx : execMTaskGraphp->vertices()) {
        ExecMTask* const mtp = vtx.as<ExecMTask>();
        // This estimate is 64 bits, but the final mtask graph algorithm needs 32 bits
        const uint64_t costEstimate = V3InstrCount::count(mtp->bodyp(), false);
        const uint64_t costProfiled
            = V3Config::getProfileData(v3Global.opt.prefix(), mtp->hashName());
        if (costProfiled) {
            UINFO(5, "Profile data for mtask " << mtp->id() << " " << mtp->hashName()
                                               << " cost override " << costProfiled << endl);
        }
        costs[mtp->id()] = std::make_pair(costEstimate, costProfiled);
    }

    normalizeCosts(costs /*ref*/);

    int totalEstimates = 0;
    int missingProfiles = 0;
    for (V3GraphVertex& vtx : execMTaskGraphp->vertices()) {
        ExecMTask* const mtp = vtx.as<ExecMTask>();
        const uint32_t costEstimate = costs[mtp->id()].first;
        const uint64_t costProfiled = costs[mtp->id()].second;
        UINFO(9, "ce = " << costEstimate << " cp=" << costProfiled << endl);
        UASSERT(costEstimate <= (1UL << 31), "cost scaling math would overflow uint32");
        UASSERT(costProfiled <= (1UL << 31), "cost scaling math would overflow uint32");
        const uint64_t costProfiled32 = static_cast<uint32_t>(costProfiled);
        uint32_t costToUse = costProfiled32;
        if (!costProfiled32) {
            costToUse = costEstimate;
            if (costEstimate != 0) ++missingProfiles;
        }
        if (costEstimate != 0) ++totalEstimates;
        mtp->cost(costToUse);
        mtp->priority(costToUse);
    }

    if (missingProfiles) {
        if (FileLine* const fl = V3Config::getProfileDataFileLine()) {
            fl->v3warn(PROFOUTOFDATE, "Profile data for mtasks may be out of date. "
                                          << missingProfiles << " of " << totalEstimates
                                          << " mtasks had no data");
        }
    }
}

void finalizeCosts(V3Graph* execMTaskGraphp) {
    GraphStreamUnordered ser(execMTaskGraphp, GraphWay::REVERSE);
    while (const V3GraphVertex* const vxp = ser.nextp()) {
        ExecMTask* const mtp = const_cast<V3GraphVertex*>(vxp)->as<ExecMTask>();
        // "Priority" is the critical path from the start of the mtask, to
        // the end of the graph reachable from this mtask.  Given the
        // choice among several ready mtasks, we'll want to start the
        // highest priority one first, so we're always working on the "long
        // pole"
        for (V3GraphEdge& edge : mtp->outEdges()) {
            const ExecMTask* const followp = edge.top()->as<ExecMTask>();
            if ((followp->priority() + mtp->cost()) > mtp->priority()) {
                mtp->priority(followp->priority() + mtp->cost());
            }
        }
    }

    // Some MTasks may now have zero cost, eliminate those.
    // (It's common for tasks to shrink to nothing when V3LifePost
    // removes dly assignments.)
    for (V3GraphVertex* const vtxp : execMTaskGraphp->vertices().unlinkable()) {
        ExecMTask* const mtp = vtxp->as<ExecMTask>();

        // Don't rely on checking mtp->cost() == 0 to detect an empty task.
        // Our cost-estimating logic is just an estimate. Instead, check
        // the MTaskBody to see if it's empty. That's the source of truth.
        AstMTaskBody* const bodyp = mtp->bodyp();
        if (!bodyp->stmtsp()) {  // Kill this empty mtask
            UINFO(6, "Removing zero-cost " << mtp->name() << endl);
            for (V3GraphEdge& in : mtp->inEdges()) {
                for (V3GraphEdge& out : mtp->outEdges()) {
                    new V3GraphEdge{execMTaskGraphp, in.fromp(), out.top(), 1};
                }
            }
            VL_DO_DANGLING(mtp->unlinkDelete(execMTaskGraphp), mtp);
            // Also remove and delete the AstMTaskBody, otherwise it would
            // keep a dangling pointer to the ExecMTask.
            VL_DO_DANGLING(bodyp->unlinkFrBack()->deleteTree(), bodyp);
        }
    }

    // Removing tasks may cause edges that were formerly non-transitive to
    // become transitive. Also we just created new edges around the removed
    // tasks, which could be transitive. Prune out all transitive edges.
    execMTaskGraphp->removeTransitiveEdges();

    // Record summary stats for final m_tasks graph.
    const auto report = execMTaskGraphp->parallelismReport(
        [](const V3GraphVertex* vtxp) { return vtxp->as<const ExecMTask>()->cost(); });
    V3Stats::addStat("MTask graph, final, critical path cost", report.criticalPathCost());
    V3Stats::addStat("MTask graph, final, total graph cost", report.totalGraphCost());
    V3Stats::addStat("MTask graph, final, mtask count", report.vertexCount());
    V3Stats::addStat("MTask graph, final, edge count", report.edgeCount());
    V3Stats::addStat("MTask graph, final, parallelism factor", report.parallelismFactor());
    if (debug() >= 3) {
        UINFO(0, "\n");
        UINFO(0, "    Final mtask parallelism report:\n");
        UINFO(0, "    Critical path cost = " << report.criticalPathCost() << "\n");
        UINFO(0, "    Total graph cost = " << report.totalGraphCost() << "\n");
        UINFO(0, "    MTask vertex count = " << report.vertexCount() << "\n");
        UINFO(0, "    Edge count = " << report.edgeCount() << "\n");
        UINFO(0, "    Parallelism factor = " << report.parallelismFactor() << "\n");
    }
}

void addMTaskToFunction(const ThreadSchedule& schedule, const uint32_t threadId, AstCFunc* funcp,
                        const ExecMTask* mtaskp) {
    AstNodeModule* const modp = v3Global.rootp()->topModulep();
    FileLine* const fl = modp->fileline();

    // Helper function to make the code a bit more legible
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        funcp->addStmtsp(new AstCStmt{fl, stmt});
    };

    if (const uint32_t nDependencies = schedule.crossThreadDependencies(mtaskp)) {
        // This mtask has dependencies executed on another thread, so it may block. Create the task
        // state variable and wait to be notified.
        const string name = "__Vm_mtaskstate_" + cvtToStr(mtaskp->id());
        AstBasicDType* const mtaskStateDtypep
            = v3Global.rootp()->typeTablep()->findBasicDType(fl, VBasicDTypeKwd::MTASKSTATE);
        AstVar* const varp = new AstVar{fl, VVarType::MODULETEMP, name, mtaskStateDtypep};
        varp->valuep(new AstConst{fl, nDependencies});
        varp->protect(false);  // Do not protect as we still have references in AstText
        modp->addStmtsp(varp);
        // For now, reference is still via text bashing
        addStrStmt("vlSelf->" + name + +".waitUntilUpstreamDone(even_cycle);\n");
    }

    if (v3Global.opt.profPgo()) {
        // No lock around startCounter, as counter numbers are unique per thread
        addStrStmt("vlSymsp->_vm_pgoProfiler.startCounter(" + std::to_string(mtaskp->id())
                   + ");\n");
    }

    // Move the actual body into this function
    funcp->addStmtsp(mtaskp->bodyp()->unlinkFrBack());

    if (v3Global.opt.profPgo()) {
        // No lock around stopCounter, as counter numbers are unique per thread
        addStrStmt("vlSymsp->_vm_pgoProfiler.stopCounter(" + std::to_string(mtaskp->id())
                   + ");\n");
    }

    // For any dependent mtask that's on another thread, signal one dependency completion.
    for (const V3GraphEdge& edge : mtaskp->outEdges()) {
        const ExecMTask* const nextp = edge.top()->as<ExecMTask>();
        if (schedule.threadId(nextp) != threadId) {
            addStrStmt("vlSelf->__Vm_mtaskstate_" + cvtToStr(nextp->id())
                       + ".signalUpstreamDone(even_cycle);\n");
        }
    }
}

const std::vector<AstCFunc*> createThreadFunctions(const ThreadSchedule& schedule,
                                                   const string& tag) {
    AstNodeModule* const modp = v3Global.rootp()->topModulep();
    FileLine* const fl = modp->fileline();

    std::vector<AstCFunc*> funcps;

    // For each thread, create a function representing its entry point
    for (const std::vector<const ExecMTask*>& thread : schedule.threads) {
        if (thread.empty()) continue;
        const uint32_t threadId = schedule.threadId(thread.front());
        const string name{"__Vthread__" + tag + "__" + cvtToStr(threadId)};
        AstCFunc* const funcp = new AstCFunc{fl, name, nullptr, "void"};
        modp->addStmtsp(funcp);
        funcps.push_back(funcp);
        funcp->isStatic(true);  // Uses void self pointer, so static and hand rolled
        funcp->isLoose(true);
        funcp->entryPoint(true);
        funcp->argTypes("void* voidSelf, bool even_cycle");

        // Setup vlSelf an vlSyms
        funcp->addStmtsp(new AstCStmt{fl, EmitCBase::voidSelfAssign(modp)});
        funcp->addStmtsp(new AstCStmt{fl, EmitCBase::symClassAssign()});

        // Invoke each mtask scheduled to this thread from the thread function
        for (const ExecMTask* const mtaskp : thread) {
            addMTaskToFunction(schedule, threadId, funcp, mtaskp);
        }

        // Unblock the fake "final" mtask when this thread is finished
        funcp->addStmtsp(new AstCStmt{fl, "vlSelf->__Vm_mtaskstate_final__" + tag
                                              + ".signalUpstreamDone(even_cycle);\n"});
    }

    // Create the fake "final" mtask state variable
    AstBasicDType* const mtaskStateDtypep
        = v3Global.rootp()->typeTablep()->findBasicDType(fl, VBasicDTypeKwd::MTASKSTATE);
    AstVar* const varp
        = new AstVar{fl, VVarType::MODULETEMP, "__Vm_mtaskstate_final__" + tag, mtaskStateDtypep};
    varp->valuep(new AstConst(fl, funcps.size()));
    varp->protect(false);  // Do not protect as we still have references in AstText
    modp->addStmtsp(varp);

    return funcps;
}

void addThreadStartToExecGraph(AstExecGraph* const execGraphp,
                               const std::vector<AstCFunc*>& funcps) {
    // FileLine used for constructing nodes below
    FileLine* const fl = v3Global.rootp()->fileline();
    const string& tag = execGraphp->name();

    // Add thread function invocations to execGraph
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        execGraphp->addStmtsp(new AstCStmt{fl, stmt});
    };
    const auto addTextStmt = [=](const string& text) -> void {
        execGraphp->addStmtsp(new AstText{fl, text, /* tracking: */ true});
    };

    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).execGraphBegin();\n");
    }

    addStrStmt("vlSymsp->__Vm_even_cycle__" + tag + " = !vlSymsp->__Vm_even_cycle__" + tag
               + ";\n");

    const uint32_t last = funcps.size() - 1;
    for (uint32_t i = 0; i <= last; ++i) {
        AstCFunc* const funcp = funcps.at(i);
        if (i != last) {
            // The first N-1 will run on the thread pool.
            addTextStmt("vlSymsp->__Vm_threadPoolp->workerp(" + cvtToStr(i) + ")->addTask(");
            execGraphp->addStmtsp(new AstAddrOfCFunc{fl, funcp});
            addTextStmt(", vlSelf, vlSymsp->__Vm_even_cycle__" + tag + ");\n");
        } else {
            // The last will run on the main thread.
            AstCCall* const callp = new AstCCall{fl, funcp};
            callp->dtypeSetVoid();
            callp->argTypes("vlSelf, vlSymsp->__Vm_even_cycle__" + tag);
            execGraphp->addStmtsp(callp->makeStmt());
            addStrStmt("Verilated::mtaskId(0);\n");
        }
    }

    addStrStmt("vlSelf->__Vm_mtaskstate_final__" + tag
               + ".waitUntilUpstreamDone(vlSymsp->__Vm_even_cycle__" + tag + ");\n");

    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).execGraphEnd();\n");
    }
}

void wrapMTaskBodies(AstExecGraph* const execGraphp) {
    FileLine* const flp = execGraphp->fileline();
    const string& tag = execGraphp->name();
    AstNodeModule* const modp = v3Global.rootp()->topModulep();

    for (AstMTaskBody* mtaskBodyp = execGraphp->mTaskBodiesp(); mtaskBodyp;
         mtaskBodyp = VN_AS(mtaskBodyp->nextp(), MTaskBody)) {
        ExecMTask* const mtaskp = mtaskBodyp->execMTaskp();
        const std::string name = tag + "_mtask" + std::to_string(mtaskp->id());
        AstCFunc* const funcp = new AstCFunc{flp, name, nullptr};
        funcp->isLoose(true);
        modp->addStmtsp(funcp);

        // Helper function to make the code a bit more legible
        const auto addStrStmt = [=](const string& stmt) -> void {  //
            funcp->addStmtsp(new AstCStmt{flp, stmt});
        };

        if (v3Global.opt.profExec()) {
            const string& id = std::to_string(mtaskp->id());
            const string& predictStart = std::to_string(mtaskp->predictStart());
            addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskBegin(" + id + ", " + predictStart
                       + ");\n");
        }

        // Set mtask ID in the run-time system
        addStrStmt("Verilated::mtaskId(" + std::to_string(mtaskp->id()) + ");\n");

        // Run body
        funcp->addStmtsp(mtaskBodyp->stmtsp()->unlinkFrBackWithNext());

        // Flush message queue
        addStrStmt("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");

        if (v3Global.opt.profExec()) {
            const string& id = std::to_string(mtaskp->id());
            const string& predictConst = std::to_string(mtaskp->cost());
            addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskEnd(" + id + ", " + predictConst
                       + ");\n");
        }

        // AstMTask will simply contain a call
        AstCCall* const callp = new AstCCall{flp, funcp};
        callp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        callp->dtypeSetVoid();
        mtaskBodyp->addStmtsp(callp->makeStmt());
    }
}

void implementExecGraph(AstExecGraph* const execGraphp, const ThreadSchedule& schedule) {
    // Nothing to be done if there are no MTasks in the graph at all.
    if (execGraphp->depGraphp()->empty()) return;

    // Create a function to be run by each thread. Note this moves all AstMTaskBody nodes form the
    // AstExecGrap into the AstCFunc created
    const std::vector<AstCFunc*>& funcps = createThreadFunctions(schedule, execGraphp->name());
    UASSERT(!funcps.empty(), "Non-empty ExecGraph yields no threads?");

    // Start the thread functions at the point this AstExecGraph is located in the tree.
    addThreadStartToExecGraph(execGraphp, funcps);
}

void implement(AstNetlist* netlistp) {
    // Called by Verilator top stage
    netlistp->topModulep()->foreach([&](AstExecGraph* execGraphp) {
        // Back in V3Order, we partitioned mtasks using provisional cost
        // estimates. However, V3Order precedes some optimizations (notably
        // V3LifePost) that can change the cost of logic within each mtask.
        // Now that logic is final, recompute the cost and priority of each
        // ExecMTask.
        fillinCosts(execGraphp->depGraphp());
        finalizeCosts(execGraphp->depGraphp());

        // Schedule the mtasks: statically associate each mtask with a thread,
        // and determine the order in which each thread will runs its mtasks.
        const ThreadSchedule& schedule = PackThreads::apply(*execGraphp->depGraphp());

        // Wrap each MTask body into a CFunc for better profiling/debugging
        wrapMTaskBodies(execGraphp);

        // Replace the graph body with its multi-threaded implementation.
        implementExecGraph(execGraphp, schedule);
    });
}

void selfTest() {
    {  // Test that omitted profile data correctly scales estimates
        Costs costs({// id  est  prof
                     {1, {10, 1000}},
                     {2, {20, 0}},  // Note no profile
                     {3, {30, 3000}}});
        normalizeCosts(costs);
        UASSERT_SELFTEST(uint64_t, costs[1].first, 1000);
        UASSERT_SELFTEST(uint64_t, costs[1].second, 1000);
        UASSERT_SELFTEST(uint64_t, costs[2].first, 2000);
        UASSERT_SELFTEST(uint64_t, costs[2].second, 0);
        UASSERT_SELFTEST(uint64_t, costs[3].first, 3000);
        UASSERT_SELFTEST(uint64_t, costs[3].second, 3000);
    }
    {  // Test that very large profile data properly scales
        Costs costs({// id  est  prof
                     {1, {10, 100000000000}},
                     {2, {20, 200000000000}},
                     {3, {30, 1}}});  // Make sure doesn't underflow
        normalizeCosts(costs);
        UASSERT_SELFTEST(uint64_t, costs[1].first, 2500000);
        UASSERT_SELFTEST(uint64_t, costs[1].second, 5000000);
        UASSERT_SELFTEST(uint64_t, costs[2].first, 5000000);
        UASSERT_SELFTEST(uint64_t, costs[2].second, 10000000);
        UASSERT_SELFTEST(uint64_t, costs[3].first, 7500000);
        UASSERT_SELFTEST(uint64_t, costs[3].second, 1);
    }

    PackThreads::selfTest();
}

}  // namespace V3ExecGraph
