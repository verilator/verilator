// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's graph structures
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

#ifndef VERILATOR_V3PARTITIONGRAPH_H_
#define VERILATOR_V3PARTITIONGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"
#include "V3OrderGraph.h"

#include <list>

//*************************************************************************
// MTasks and graph structures

class AbstractMTask VL_NOT_FINAL : public V3GraphVertex {
public:
    explicit AbstractMTask(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    virtual ~AbstractMTask() override = default;
    virtual uint32_t id() const = 0;
    virtual uint32_t cost() const = 0;
};

class AbstractLogicMTask VL_NOT_FINAL : public AbstractMTask {
public:
    // TYPES
    using VxList = std::list<MTaskMoveVertex*>;
    // CONSTRUCTORS
    explicit AbstractLogicMTask(V3Graph* graphp)
        : AbstractMTask{graphp} {}
    virtual ~AbstractLogicMTask() override = default;
    // METHODS
    // Set of logic vertices in this mtask. Order is not significant.
    virtual const VxList* vertexListp() const = 0;
    virtual uint32_t id() const override = 0;  // Unique id of this mtask.
    virtual uint32_t cost() const override = 0;
};

class ExecMTask final : public AbstractMTask {
private:
    AstMTaskBody* const m_bodyp;  // Task body
    const uint32_t m_id;  // Unique id of this mtask.
    string m_hashName;  // Hashed name for profile-driven optimization
    uint32_t m_priority = 0;  // Predicted critical path from the start of
                              // this mtask to the ends of the graph that are reachable from this
                              // mtask. In abstract time units.
    uint32_t m_cost = 0;  // Predicted runtime of this mtask, in the same
                          // abstract time units as priority().
    uint64_t m_predictStart = 0;  // Predicted start time of task
    uint64_t m_profilerId = 0;  // VerilatedCounter number for profiling
    VL_UNCOPYABLE(ExecMTask);

public:
    ExecMTask(V3Graph* graphp, AstMTaskBody* bodyp, uint32_t id)
        : AbstractMTask{graphp}
        , m_bodyp{bodyp}
        , m_id{id} {}
    AstMTaskBody* bodyp() const { return m_bodyp; }
    virtual uint32_t id() const override { return m_id; }
    uint32_t priority() const { return m_priority; }
    void priority(uint32_t pri) { m_priority = pri; }
    virtual uint32_t cost() const override { return m_cost; }
    void cost(uint32_t cost) { m_cost = cost; }
    void predictStart(uint64_t time) { m_predictStart = time; }
    uint64_t predictStart() const { return m_predictStart; }
    void profilerId(uint64_t id) { m_profilerId = id; }
    uint64_t profilerId() const { return m_profilerId; }
    string cFuncName() const {
        // If this MTask maps to a C function, this should be the name
        return std::string{"__Vmtask"} + "__" + cvtToStr(m_id);
    }
    virtual string name() const override { return std::string{"mt"} + cvtToStr(id()); }
    string hashName() const { return m_hashName; }
    void hashName(const string& name) { m_hashName = name; }
    void dump(std::ostream& str) const {
        str << name() << "." << cvtToHex(this);
        if (priority() || cost()) str << " [pr=" << priority() << " c=" << cvtToStr(cost()) << "]";
    }
};
inline std::ostream& operator<<(std::ostream& os, const ExecMTask& rhs) {
    rhs.dump(os);
    return os;
}

#endif  // Guard
