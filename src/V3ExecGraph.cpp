// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstExecGraph code construction
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
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

std::atomic<uint32_t> ExecMTask::s_nextId{0};

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

    uint32_t m_id;  // Unique ID of a schedule
    static uint32_t s_nextId;  // Next ID number to use
    std::unordered_set<const ExecMTask*> mtasks;  // Mtasks in this schedule
    uint32_t m_endTime = 0;  // Latest task end time in this schedule

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

    // Global state for each mtask.
    static std::unordered_map<const ExecMTask*, MTaskState> mtaskState;

    explicit ThreadSchedule(uint32_t nThreads)
        : m_id(s_nextId++)
        , threads{nThreads} {}
    ThreadSchedule(ThreadSchedule&&) = default;
    ThreadSchedule& operator=(ThreadSchedule&&) = default;

private:
    VL_UNCOPYABLE(ThreadSchedule);

    static constexpr double s_threadBoxWidth = 2.0;
    static constexpr double s_threadBoxHeight = 1.5;
    static constexpr double s_horizontalGap = s_threadBoxWidth / 2;

    // Debugging
    // Variant of dumpDotFilePrefixed without --dump option check
    static void dumpDotFilePrefixedAlways(const std::vector<ThreadSchedule>& schedules,
                                          const string& nameComment, uint32_t nThreads) {
        dumpDotFile(schedules, v3Global.debugFilename(nameComment) + ".dot", nThreads);
    }
    static void dumpDotFile(const std::vector<ThreadSchedule>& schedules, const string& filename,
                            uint32_t nThreads) {
        // This generates a file used by graphviz, https://www.graphviz.org
        const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
        if (logp->fail()) v3fatal("Can't write file: " << filename);

        // Header
        *logp << "digraph v3graph {\n";
        *logp << "  graph[layout=\"neato\" labelloc=t labeljust=l label=\"" << filename << "\"]\n";
        *logp << "  node[shape=\"rect\" ratio=\"fill\" fixedsize=true]\n";

        // Thread labels
        *logp << "\n  // Threads\n";

        for (uint32_t i = 0; i < nThreads; ++i) {
            const string name = "t" + std::to_string(i);
            const string label = "Thread " + std::to_string(i);
            constexpr double posX = -s_horizontalGap;
            const double posY = -static_cast<double>(i) * s_threadBoxHeight;
            dumpDotFileEmitBlock(logp, name, label, s_threadBoxWidth, s_threadBoxHeight, posX,
                                 posY, "grey");
        }

        // MTask nodes
        *logp << "\n  // MTasks\n";

        // Create columns of tasks whose execution intervals overlaps
        int offset = 0;
        for (const ThreadSchedule& schedule : schedules) {
            using Column = std::vector<const ExecMTask*>;
            std::vector<Column> columns = {{}};

            // Order tasks based on their start time
            struct Cmp final {
                bool operator()(const ExecMTask* const a, const ExecMTask* const b) const {
                    if (startTime(a) == startTime(b)) return threadId(a) < threadId(b);
                    return startTime(a) < startTime(b);
                }
            };
            const std::multiset<const ExecMTask*, Cmp> tasks(schedule.mtasks.begin(),
                                                             schedule.mtasks.end());
            UASSERT(!tasks.empty(), "Thread schedule should have tasks");

            for (const ExecMTask* const mtaskp : tasks) {
                Column& column = columns.back();
                UASSERT(column.size() <= nThreads, "Invalid partitioning");
                bool intersects = true;
                for (const ExecMTask* const earlierMtask : column) {
                    if (endTime(mtaskp) <= startTime(earlierMtask)
                        || startTime(mtaskp) >= endTime(earlierMtask)) {
                        intersects = false;
                        break;
                    }
                }
                if (intersects) {
                    column.emplace_back(mtaskp);
                } else {
                    columns.emplace_back(Column{mtaskp});
                }
            }

            UASSERT(!columns.front().empty(), "Should be populated by mtasks");

            for (const Column& column : columns) {
                for (const ExecMTask* const mtask : column) {
                    dumpDotFileEmitMTask(logp, mtask, offset, schedule);
                }
                ++offset;
            }
            dumpDotFileEmitFork(logp, offset, nThreads);

            // Emit MTask dependency edges
            *logp << "\n  // MTask dependencies\n";

            for (const std::vector<const ExecMTask*>& thread : schedule.threads) {
                if (thread.empty()) break;  // No more threads

                // Show that schedule ends when all tasks are finished
                *logp << "  " << thread.back()->name() << " -> fork_" << offset << "\n";

                // Show that tasks from the same thread are executed in a sequence
                for (size_t i = 1; i < thread.size(); ++i)
                    *logp << "  " << thread[i - 1]->name() << " -> " << thread[i]->name() << "\n";

                // Emit cross-task dependencies
                for (const ExecMTask* const mtaskp : thread) {
                    for (const V3GraphEdge& edge : mtaskp->outEdges()) {
                        const ExecMTask* const topMTaskp = edge.top()->cast<const ExecMTask>();
                        if (topMTaskp && schedule.contains(topMTaskp)
                            && threadId(topMTaskp) != threadId(mtaskp))
                            *logp << "  " << mtaskp->name() << " -> " << topMTaskp->name() << "\n";
                    }
                }
            }
        }

        // Trailer
        *logp << "}\n";
        logp->close();
    }
    static void dumpDotFileEmitBlock(const std::unique_ptr<std::ofstream>& logp,
                                     const string& name, const string& label, double width,
                                     double height, double xPos, double yPos,
                                     const string& fillColor) {
        *logp << "  " << name << " [label=\"" << label << "\" width=" << width
              << " height=" << height << " pos=\"" << xPos << "," << yPos
              << "!\" style=\"filled\" fillcolor=\"" << fillColor << "\"]\n";
    }
    static void dumpDotFileEmitMTask(const std::unique_ptr<std::ofstream>& logp,
                                     const ExecMTask* const mtaskp, int index,
                                     const ThreadSchedule& schedule) {
        for (int i = 0; i < mtaskp->threads(); ++i) {
            // Keep original name for the original thread of hierarchical task to keep
            // dependency tracking, add '_' for the rest to differentiate them.
            const string name = i == 0 ? mtaskp->name() : mtaskp->name() + '_' + std::to_string(i);
            const string label = mtaskp->name() + " (" + std::to_string(startTime(mtaskp)) + ':'
                                 + std::to_string(endTime(mtaskp)) + ')'
                                 + "\\ncost=" + std::to_string(mtaskp->cost())
                                 + "\\npriority=" + std::to_string(mtaskp->priority());
            const double xPos = (s_threadBoxWidth + s_horizontalGap) * index + s_horizontalGap;
            const double yPos
                = -s_threadBoxHeight
                  * static_cast<double>(threadId(mtaskp) + i * schedule.threads.size());
            const string fillColor = i == 0 ? "white" : "lightgreen";
            dumpDotFileEmitBlock(logp, name, label, s_threadBoxWidth, s_threadBoxHeight, xPos,
                                 yPos, fillColor);
        }
    }

    static void dumpDotFileEmitFork(const std::unique_ptr<std::ofstream>& logp, int index,
                                    uint32_t nThreads) {
        const string& name = "fork_" + std::to_string(index);
        constexpr double width = s_threadBoxWidth / 8;
        const double height = s_threadBoxHeight * nThreads;
        const double xPos = index * (s_threadBoxWidth + s_horizontalGap) - s_horizontalGap / 2;
        const double yPos
            = -static_cast<double>(nThreads) / 2 * s_threadBoxHeight + s_threadBoxHeight / 2;
        dumpDotFileEmitBlock(logp, name, "", width, height, xPos, yPos, "black");
    }

public:
    static uint32_t threadId(const ExecMTask* mtaskp) {
        const auto& it = mtaskState.find(mtaskp);
        return it != mtaskState.end() ? it->second.threadId : UNASSIGNED;
    }
    static uint32_t startTime(const ExecMTask* mtaskp) {
        return mtaskState.at(mtaskp).completionTime - mtaskp->cost();
    }
    static uint32_t endTime(const ExecMTask* mtaskp) {
        return mtaskState.at(mtaskp).completionTime;
    }

    // Returns the number of cross-thread dependencies of the given MTask. If > 0, the MTask must
    // test whether its dependencies are ready before starting, and therefore may need to block.
    uint32_t crossThreadDependencies(const ExecMTask* mtaskp) const {
        const uint32_t thisThreadId = threadId(mtaskp);
        uint32_t result = 0;
        for (const V3GraphEdge& edge : mtaskp->inEdges()) {
            const ExecMTask* const prevp = edge.fromp()->as<ExecMTask>();
            if (threadId(prevp) != thisThreadId && contains(prevp)) ++result;
        }
        return result;
    }

    uint32_t id() const { return m_id; }
    uint32_t scheduleOn(const ExecMTask* mtaskp, uint32_t bestThreadId) {
        mtasks.emplace(mtaskp);
        const uint32_t bestEndTime = mtaskp->predictStart() + mtaskp->cost();
        m_endTime = std::max(m_endTime, bestEndTime);
        mtaskState[mtaskp].completionTime = bestEndTime;
        mtaskState[mtaskp].threadId = bestThreadId;

        // Reference to thread in schedule we are assigning this MTask to.
        std::vector<const ExecMTask*>& bestThread = threads[bestThreadId];
        if (!bestThread.empty()) mtaskState[bestThread.back()].nextp = mtaskp;

        // Add the MTask to the schedule
        bestThread.push_back(mtaskp);
        return bestEndTime;
    }
    bool contains(const ExecMTask* mtaskp) const { return mtasks.count(mtaskp); }
    uint32_t endTime() const { return m_endTime; }
};

uint32_t ThreadSchedule::s_nextId = 0;
std::unordered_map<const ExecMTask*, ThreadSchedule::MTaskState> ThreadSchedule::mtaskState{};

//######################################################################
// PackThreads

// Statically pack tasks into threads.
//
// The simplest thing that could possibly work would be to assume that our
// predictions of task runtimes are precise, and that every thread will
// make progress at an equal rate. Simulate a single "clock", pack the
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
        // Ignore tasks that were scheduled on a different schedule
        if (!schedule.contains(mtaskp)) return 0;
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

    static bool isReady(ThreadSchedule& schedule, const ExecMTask* mtaskp) {
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
    std::vector<ThreadSchedule> pack(V3Graph& mtaskGraph) {
        std::vector<ThreadSchedule> result;
        result.emplace_back(ThreadSchedule{m_nThreads});

        // To support scheduling tasks that utilize more than one thread, we introduce a wide
        // task (ExecMTask with threads() > 1). Those tasks are scheduled on a separate thread
        // schedule to ensure that indexes for simulation-time thread pool workers are not shadowed
        // by another tasks.
        // For retaining control over thread schedules, we distinguish SchedulingModes:
        enum class SchedulingMode {
            SCHEDULING  // Schedule normal tasks
            ,
            WIDE_TASK_DISCOVERED  // We found a wide task, if this is the only one available,
                                  // switch to WIDE_TASK_SCHEDULING
            ,
            WIDE_TASK_SCHEDULING  // Schedule wide tasks
        };
        SchedulingMode mode = SchedulingMode::SCHEDULING;

        // Time each thread is occupied until
        std::vector<uint32_t> busyUntil(m_nThreads, 0);

        // MTasks ready to be assigned next. All their dependencies are already assigned.
        std::set<ExecMTask*, MTaskCmp> readyMTasks;
        int maxThreadWorkers = 1;

        // Build initial ready list
        for (V3GraphVertex& vtx : mtaskGraph.vertices()) {
            ExecMTask* const mtaskp = vtx.as<ExecMTask>();
            if (isReady(result.back(), mtaskp)) readyMTasks.insert(mtaskp);
            // TODO right now we schedule tasks assuming they take the same number of threads for
            // simplification.
            maxThreadWorkers = std::max(maxThreadWorkers, mtaskp->threads());
        }

        while (!readyMTasks.empty()) {
            // For each task in the ready set, compute when it might start
            // on each thread (in that thread's local time frame.)
            uint32_t bestTime = 0xffffffff;
            uint32_t bestThreadId = 0;
            ExecMTask* bestMtaskp = nullptr;  // Todo: const ExecMTask*
            ThreadSchedule& schedule = result.back();
            for (uint32_t threadId = 0; threadId < schedule.threads.size(); ++threadId) {
                for (ExecMTask* const mtaskp : readyMTasks) {
                    if (mode != SchedulingMode::WIDE_TASK_SCHEDULING && mtaskp->threads() > 1) {
                        mode = SchedulingMode::WIDE_TASK_DISCOVERED;
                        continue;
                    }
                    if (mode == SchedulingMode::WIDE_TASK_SCHEDULING && mtaskp->threads() <= 1)
                        continue;

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

            const uint32_t endTime = schedule.endTime();

            if (!bestMtaskp && mode == SchedulingMode::WIDE_TASK_DISCOVERED) {
                mode = SchedulingMode::WIDE_TASK_SCHEDULING;
                const uint32_t size = m_nThreads / maxThreadWorkers;
                UASSERT(size, "Thread pool size should be bigger than 0");
                // If no tasks were added to the normal thread schedule, clear it.
                if (schedule.mtaskState.empty()) result.clear();
                result.emplace_back(ThreadSchedule{size});
                std::fill(busyUntil.begin(), busyUntil.end(), endTime);
                continue;
            }

            if (!bestMtaskp && mode == SchedulingMode::WIDE_TASK_SCHEDULING) {
                mode = SchedulingMode::SCHEDULING;
                UASSERT(!schedule.mtaskState.empty(), "Mtask should be added");
                result.emplace_back(ThreadSchedule{m_nThreads});
                std::fill(busyUntil.begin(), busyUntil.end(), endTime);
                continue;
            }

            UASSERT(bestMtaskp, "Should have found some task");

            bestMtaskp->predictStart(bestTime);
            const uint32_t bestEndTime = schedule.scheduleOn(bestMtaskp, bestThreadId);
            busyUntil[bestThreadId] = bestEndTime;

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

        // All schedules are combined on a single graph
        if (dumpGraphLevel() >= 4)
            ThreadSchedule::dumpDotFilePrefixedAlways(result, "schedule", m_nThreads);

        return result;
    }

public:
    // SELF TEST
    static void selfTest() {
        selfTestHierFirst();
        selfTestNormalFirst();
    }
    static void selfTestNormalFirst() {
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
        t2->threads(2);
        ExecMTask* const t3 = new ExecMTask{&graph, makeBody()};
        t3->cost(100);
        t3->priority(100);
        t3->threads(3);
        ExecMTask* const t4 = new ExecMTask{&graph, makeBody()};
        t4->cost(100);
        t4->priority(100);
        t4->threads(3);
        ExecMTask* const t5 = new ExecMTask{&graph, makeBody()};
        t5->cost(100);
        t5->priority(100);
        ExecMTask* const t6 = new ExecMTask{&graph, makeBody()};
        t6->cost(100);
        t6->priority(100);

        /*
                          0
                         / \
                        1   2
                           / \
                          3   4
                         /    \
                        5      6
        */
        new V3GraphEdge{&graph, t0, t1, 1};
        new V3GraphEdge{&graph, t0, t2, 1};
        new V3GraphEdge{&graph, t2, t3, 1};
        new V3GraphEdge{&graph, t2, t4, 1};
        new V3GraphEdge{&graph, t3, t5, 1};
        new V3GraphEdge{&graph, t4, t6, 1};

        constexpr uint32_t threads = 6;
        PackThreads packer{threads,
                           3,  // Sandbag numerator
                           10};  // Sandbag denom

        const std::vector<ThreadSchedule> scheduled = packer.pack(graph);
        UASSERT_SELFTEST(size_t, scheduled.size(), 3);
        UASSERT_SELFTEST(size_t, scheduled[0].threads.size(), threads);
        UASSERT_SELFTEST(size_t, scheduled[0].threads[0].size(), 2);
        for (size_t i = 1; i < scheduled[0].threads.size(); ++i)
            UASSERT_SELFTEST(size_t, scheduled[0].threads[i].size(), 0);

        UASSERT_SELFTEST(const ExecMTask*, scheduled[0].threads[0][0], t0);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[0].threads[0][1], t1);

        UASSERT_SELFTEST(size_t, scheduled[1].threads.size(), threads / 3);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[1].threads[0][0], t2);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[1].threads[0][1], t3);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[1].threads[1][0], t4);

        UASSERT_SELFTEST(size_t, scheduled[2].threads.size(), threads);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[2].threads[0][0], t5);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[2].threads[1][0], t6);

        UASSERT_SELFTEST(size_t, ThreadSchedule::mtaskState.size(), 7);

        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t0), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t1), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t2), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t3), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t4), 1);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t5), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t6), 1);

        // On its native thread, we see the actual end time for t0:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t0, 0), 1000);
        // On the other thread, we see a sandbagged end time which does not
        // exceed the t1 end time:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t0, 1), 1099);

        // Actual end time on native thread:
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t1, 0), 1100);
        // Sandbagged end time seen on thread 1.  Note it does not compound
        // with t0's sandbagged time; compounding caused trouble in
        // practice.
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t1, 1), 1130);

        // Wide task scheduling

        // Task does not depend on previous or future schedules
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t2, 0), 0);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[2], t2, 0), 0);

        // We allow sandbagging for hierarchical children tasks, this does not affect
        // wide task scheduling. When the next schedule is created it doesn't matter
        // anyway.
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 0), 1200);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 1), 1230);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 2), 1230);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 3), 1230);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 4), 1230);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t2, 5), 1230);

        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 0), 1300);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 1), 1330);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 2), 1330);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 3), 1330);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 4), 1330);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t3, 5), 1330);

        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 0), 1360);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 1), 1330);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 2), 1360);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 3), 1360);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 4), 1360);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t4, 5), 1360);

        for (AstNode* const nodep : mTaskBodyps) nodep->deleteTree();
        ThreadSchedule::mtaskState.clear();
    }
    static void selfTestHierFirst() {
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
        t0->threads(2);
        ExecMTask* const t1 = new ExecMTask{&graph, makeBody()};
        t1->cost(100);
        t1->priority(100);

        /*
                          0
                          |
                          1
        */
        new V3GraphEdge{&graph, t0, t1, 1};

        constexpr uint32_t threads = 2;
        PackThreads packer{threads,
                           3,  // Sandbag numerator
                           10};  // Sandbag denom

        const std::vector<ThreadSchedule> scheduled = packer.pack(graph);
        UASSERT_SELFTEST(size_t, scheduled.size(), 2);
        UASSERT_SELFTEST(size_t, scheduled[0].threads.size(), threads / 2);
        UASSERT_SELFTEST(size_t, scheduled[0].threads[0].size(), 1);
        for (size_t i = 1; i < scheduled[0].threads.size(); ++i)
            UASSERT_SELFTEST(size_t, scheduled[0].threads[i].size(), 0);

        UASSERT_SELFTEST(const ExecMTask*, scheduled[0].threads[0][0], t0);

        UASSERT_SELFTEST(size_t, scheduled[1].threads.size(), threads);
        UASSERT_SELFTEST(size_t, scheduled[1].threads[0].size(), 1);
        for (size_t i = 1; i < scheduled[1].threads.size(); ++i)
            UASSERT_SELFTEST(size_t, scheduled[1].threads[i].size(), 0);
        UASSERT_SELFTEST(const ExecMTask*, scheduled[1].threads[0][0], t1);

        UASSERT_SELFTEST(size_t, ThreadSchedule::mtaskState.size(), 2);

        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t0), 0);
        UASSERT_SELFTEST(uint32_t, ThreadSchedule::threadId(t1), 0);

        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[0], t0, 0), 1000);

        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t1, 0), 1100);
        UASSERT_SELFTEST(uint32_t, packer.completionTime(scheduled[1], t1, 1), 1130);

        for (AstNode* const nodep : mTaskBodyps) nodep->deleteTree();
        ThreadSchedule::mtaskState.clear();
    }

    static std::vector<ThreadSchedule> apply(V3Graph& mtaskGraph) {
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
            if (V3Config::containsMTaskProfileData()) {
                fl->v3warn(PROFOUTOFDATE, "Profile data for mtasks may be out of date. "
                                              << missingProfiles << " of " << totalEstimates
                                              << " mtasks had no data");
            }
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
        if (v3Global.opt.profExec()) {
            addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).threadScheduleWaitBegin();\n");
        }
        addStrStmt("vlSelf->" + name + +".waitUntilUpstreamDone(even_cycle);\n");
        if (v3Global.opt.profExec()) {
            addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).threadScheduleWaitEnd();\n");
        }
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
        if (schedule.threadId(nextp) != threadId && schedule.contains(nextp)) {
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
        const string name{"__Vthread__" + tag + "__s" + cvtToStr(schedule.id()) + "__t"
                          + cvtToStr(threadId)};
        AstCFunc* const funcp = new AstCFunc{fl, name, nullptr, "void"};
        modp->addStmtsp(funcp);
        funcps.push_back(funcp);
        funcp->isStatic(true);  // Uses void self pointer, so static and hand rolled
        funcp->isLoose(true);
        funcp->entryPoint(true);
        funcp->argTypes("void* voidSelf, bool even_cycle");

        // Setup vlSelf and vlSyms
        funcp->addStmtsp(new AstCStmt{fl, EmitCBase::voidSelfAssign(modp)});
        funcp->addStmtsp(new AstCStmt{fl, EmitCBase::symClassAssign()});

        // Invoke each mtask scheduled to this thread from the thread function
        for (const ExecMTask* const mtaskp : thread) {
            addMTaskToFunction(schedule, threadId, funcp, mtaskp);
        }

        // Unblock the fake "final" mtask when this thread is finished
        funcp->addStmtsp(new AstCStmt{fl, "vlSelf->__Vm_mtaskstate_final__"
                                              + cvtToStr(schedule.id()) + tag
                                              + ".signalUpstreamDone(even_cycle);\n"});
    }

    // Create the fake "final" mtask state variable
    AstBasicDType* const mtaskStateDtypep
        = v3Global.rootp()->typeTablep()->findBasicDType(fl, VBasicDTypeKwd::MTASKSTATE);
    AstVar* const varp
        = new AstVar{fl, VVarType::MODULETEMP,
                     "__Vm_mtaskstate_final__" + cvtToStr(schedule.id()) + tag, mtaskStateDtypep};
    varp->valuep(new AstConst(fl, funcps.size()));
    varp->protect(false);  // Do not protect as we still have references in AstText
    modp->addStmtsp(varp);

    return funcps;
}

void addThreadStartWrapper(AstExecGraph* const execGraphp) {
    // FileLine used for constructing nodes below
    FileLine* const fl = v3Global.rootp()->fileline();
    const string& tag = execGraphp->name();

    // Add thread function invocations to execGraph
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        execGraphp->addStmtsp(new AstCStmt{fl, stmt});
    };

    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).execGraphBegin();\n");
    }

    addStrStmt("vlSymsp->__Vm_even_cycle__" + tag + " = !vlSymsp->__Vm_even_cycle__" + tag
               + ";\n");

    if (!v3Global.opt.hierBlocks().empty()) addStrStmt("std::vector<size_t> indexes;\n");
}

void addThreadEndWrapper(AstExecGraph* const execGraphp) {
    // Add thread function invocations to execGraph
    const auto addStrStmt = [=](const string& stmt) -> void {  //
        FileLine* const flp = v3Global.rootp()->fileline();
        execGraphp->addStmtsp(new AstCStmt{flp, stmt});
    };

    addStrStmt("Verilated::mtaskId(0);\n");
    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).execGraphEnd();\n");
    }
}
void addThreadStartToExecGraph(AstExecGraph* const execGraphp,
                               const std::vector<AstCFunc*>& funcps, uint32_t scheduleId) {
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

    const uint32_t last = funcps.size() - 1;
    if (!v3Global.opt.hierBlocks().empty() && last > 0) {
        addStrStmt(
            "for (size_t i = 0; i < " + cvtToStr(last)
            + "; ++i) indexes.push_back(vlSymsp->__Vm_threadPoolp->assignWorkerIndex());\n");
    }
    uint32_t i = 0;
    for (AstCFunc* const funcp : funcps) {
        if (i != last) {
            // The first N-1 will run on the thread pool.
            if (v3Global.opt.hierChild() || !v3Global.opt.hierBlocks().empty()) {
                addTextStmt("vlSymsp->__Vm_threadPoolp->workerp(indexes[" + cvtToStr(i)
                            + "])->addTask(");
            } else {
                addTextStmt("vlSymsp->__Vm_threadPoolp->workerp(" + cvtToStr(i) + ")->addTask(");
            }
            execGraphp->addStmtsp(new AstAddrOfCFunc{fl, funcp});
            addTextStmt(", vlSelf, vlSymsp->__Vm_even_cycle__" + tag + ");\n");
        } else {
            // The last will run on the main thread.
            AstCCall* const callp = new AstCCall{fl, funcp};
            callp->dtypeSetVoid();
            callp->argTypes("vlSelf, vlSymsp->__Vm_even_cycle__" + tag);
            execGraphp->addStmtsp(callp->makeStmt());
        }
        ++i;
    }
    V3Stats::addStatSum("Optimizations, Thread schedule total tasks", i);

    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).threadScheduleWaitBegin();\n");
    }
    addStrStmt("vlSelf->__Vm_mtaskstate_final__" + std::to_string(scheduleId) + tag
               + ".waitUntilUpstreamDone(vlSymsp->__Vm_even_cycle__" + tag + ");\n");
    if (v3Global.opt.profExec()) {
        addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).threadScheduleWaitEnd();\n");
    }
    // Free all assigned worker indices in this section
    if (!v3Global.opt.hierBlocks().empty() && last > 0) {
        addStrStmt("vlSymsp->__Vm_threadPoolp->freeWorkerIndexes(indexes);\n");
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

        addStrStmt("static constexpr unsigned taskId = " + cvtToStr(mtaskp->id()) + ";\n");

        if (v3Global.opt.profExec()) {
            const string& predictStart = std::to_string(mtaskp->predictStart());
            if (v3Global.opt.hierChild()) {
                addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskBegin(taskId, " + predictStart
                           + ", \"" + v3Global.opt.topModule() + "\");\n");
            } else {
                addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskBegin(taskId, " + predictStart
                           + ");\n");
            }
        }

        // Set mtask ID in the run-time system
        addStrStmt("Verilated::mtaskId(taskId);\n");

        // Run body
        funcp->addStmtsp(mtaskBodyp->stmtsp()->unlinkFrBackWithNext());

        // Flush message queue
        addStrStmt("Verilated::endOfThreadMTask(vlSymsp->__Vm_evalMsgQp);\n");

        if (v3Global.opt.profExec()) {
            const string& predictCost = std::to_string(mtaskp->cost());
            addStrStmt("VL_EXEC_TRACE_ADD_RECORD(vlSymsp).mtaskEnd(" + predictCost + ");\n");
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
    // AstExecGraph into the AstCFunc created
    const std::vector<AstCFunc*>& funcps = createThreadFunctions(schedule, execGraphp->name());
    UASSERT(!funcps.empty(), "Non-empty ExecGraph yields no threads?");

    // Start the thread functions at the point this AstExecGraph is located in the tree.
    addThreadStartToExecGraph(execGraphp, funcps, schedule.id());
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

        if (dumpGraphLevel() >= 4) execGraphp->depGraphp()->dumpDotFilePrefixedAlways("pack");

        addThreadStartWrapper(execGraphp);

        // Schedule the mtasks: statically associate each mtask with a thread,
        // and determine the order in which each thread will run its mtasks.
        const std::vector<ThreadSchedule> packed = PackThreads::apply(*execGraphp->depGraphp());
        V3Stats::addStatSum("Optimizations, Thread schedule count",
                            static_cast<double>(packed.size()));

        // Wrap each MTask body into a CFunc for better profiling/debugging
        wrapMTaskBodies(execGraphp);

        for (const ThreadSchedule& schedule : packed) {
            // Replace the graph body with its multi-threaded implementation.
            implementExecGraph(execGraphp, schedule);
        }

        addThreadEndWrapper(execGraphp);
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
