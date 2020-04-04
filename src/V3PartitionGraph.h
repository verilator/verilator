// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's graph structures
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3PARTITIONGRAPH_H_
#define _V3PARTITIONGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"
#include "V3OrderGraph.h"

#include <list>

//*************************************************************************
// MTasks and graph structures

class AbstractMTask : public V3GraphVertex {
public:
    AbstractMTask(V3Graph* graphp) : V3GraphVertex(graphp) {}
    virtual ~AbstractMTask() {}
    virtual uint32_t id() const = 0;
    virtual uint32_t cost() const = 0;
};

class AbstractLogicMTask : public AbstractMTask {
public:
    // TYPES
    typedef std::list<MTaskMoveVertex*> VxList;
    // CONSTRUCTORS
    AbstractLogicMTask(V3Graph* graphp) : AbstractMTask(graphp) {}
    virtual ~AbstractLogicMTask() {}
    // METHODS
    // Set of logic vertices in this mtask. Order is not significant.
    virtual const VxList* vertexListp() const = 0;
    virtual uint32_t id() const = 0;  // Unique id of this mtask.
    virtual uint32_t cost() const = 0;
};

class ExecMTask : public AbstractMTask {
private:
    AstMTaskBody*       m_bodyp;     // Task body
    uint32_t            m_id;        // Unique id of this mtask.
    uint32_t            m_priority;  // Predicted critical path from the start of
    // this mtask to the ends of the graph that are reachable from this
    // mtask. In abstract time units.
    uint32_t            m_cost;      // Predicted runtime of this mtask, in the same
    // abstract time units as priority().
    uint32_t            m_thread;    // Thread for static (pack_mtasks) scheduling,
    // or 0xffffffff if not yet assigned.
    const ExecMTask*    m_packNextp;  // Next for static (pack_mtasks) scheduling
    bool                m_threadRoot;  // Is root thread
    VL_UNCOPYABLE(ExecMTask);
public:
    ExecMTask(V3Graph* graphp, AstMTaskBody* bodyp, uint32_t id)
        : AbstractMTask(graphp),
          m_bodyp(bodyp),
          m_id(id),
          m_priority(0),
          m_cost(0),
          m_thread(0xffffffff),
          m_packNextp(NULL),
          m_threadRoot(false) {}
    AstMTaskBody* bodyp() const { return m_bodyp; }
    virtual uint32_t id() const { return m_id; }
    uint32_t priority() const { return m_priority; }
    void priority(uint32_t pri) { m_priority = pri; }
    virtual uint32_t cost() const { return m_cost; }
    void cost(uint32_t cost) { m_cost = cost; }
    void thread(uint32_t thread) { m_thread = thread; }
    uint32_t thread() const { return m_thread; }
    void packNextp(const ExecMTask* nextp) { m_packNextp = nextp; }
    const ExecMTask* packNextp() const { return m_packNextp; }
    bool threadRoot() const { return m_threadRoot; }
    void threadRoot(bool threadRoot) { m_threadRoot = threadRoot; }
    string cFuncName() const {
        // If this MTask maps to a C function, this should be the name
        return string("__Vmtask")+"__"+cvtToStr(m_id);
    }
    string name() const { return string("mt")+cvtToStr(id()); }
    void dump(std::ostream& str) const {
        str <<name()<<"."<<cvtToHex(this);
        if (priority() || cost()) str <<" [pr="<<priority()<<" c="<<cvtToStr(cost())<<"]";
        if (thread() != 0xffffffff) str <<" th="<<thread();
        if (threadRoot()) str <<" [ROOT]";
        if (packNextp()) str <<" nx="<<packNextp()->name();
    }
};
inline std::ostream& operator<<(std::ostream& os, const ExecMTask& rhs) {
    rhs.dump(os); return os; }

#endif  // Guard
