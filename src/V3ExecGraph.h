// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AstExecGraph code construction
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3EXECGRAPH_H_
#define VERILATOR_V3EXECGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"

#include <atomic>

class AstNetlist;
class AstCFunc;
class AstExecGraph;
class AstNodeStmt;
class AstScope;

//*************************************************************************
// MTasks and graph structures

class ExecMTask final : public V3GraphVertex {
    VL_RTTI_IMPL(ExecMTask, V3GraphVertex)
private:
    const uint32_t m_id;  // Unique ID of this ExecMTask.
    static std::atomic<uint32_t> s_nextId;  // Next ID to use
    AstCFunc* const m_funcp;  // The function that contains the task body
    const std::string m_hashName;  // Hashed name based on body for profile-driven optimization
    // Predicted critical path from the start of this mtask to the ends of the graph that are
    // reachable from this mtask. In abstract time units.
    uint32_t m_priority = 0;
    // Predicted runtime of this mtask, in the same abstract time units as priority().
    uint32_t m_cost = 0;
    uint64_t m_predictStart = 0;  // Predicted start time of task
    int m_threads = 1;  // Threads used by this mtask
    VL_UNCOPYABLE(ExecMTask);

    static AstCFunc* createCFunc(AstExecGraph* execGraphp, AstScope* scopep, AstNodeStmt* stmtsp,
                                 uint32_t id);

public:
    ExecMTask(AstExecGraph* execGraphp, AstScope* scopep, AstNodeStmt* stmtsp) VL_MT_DISABLED;
    AstCFunc* funcp() const { return m_funcp; }
    uint32_t id() const VL_MT_SAFE { return m_id; }
    uint32_t priority() const { return m_priority; }
    void priority(uint32_t pri) { m_priority = pri; }
    uint32_t cost() const { return m_cost; }
    void cost(uint32_t cost) { m_cost = cost; }
    uint64_t predictStart() const { return m_predictStart; }
    void predictStart(uint64_t time) { m_predictStart = time; }
    string name() const override VL_MT_STABLE { return "mt"s + std::to_string(id()); }
    string hashName() const { return m_hashName; }
    void threads(int threads) { m_threads = threads; }
    int threads() const { return m_threads; }
    void dump(std::ostream& str) const;

    static uint32_t numUsedIds() VL_MT_SAFE { return s_nextId; }
};

inline std::ostream& operator<<(std::ostream& os, const ExecMTask& rhs) {
    rhs.dump(os);
    return os;
}

namespace V3ExecGraph {
void implement(AstNetlist*) VL_MT_DISABLED;

void selfTest() VL_MT_DISABLED;
}  //namespace V3ExecGraph

#endif  // Guard
