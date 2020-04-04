// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's logic to mtask partitioner
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

#ifndef _V3PARTITION_H_
#define _V3PARTITION_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"
#include "V3OrderGraph.h"

#include <list>

class LogicMTask;
typedef vl_unordered_map<const MTaskMoveVertex*, LogicMTask*> Vx2MTaskMap;

//*************************************************************************
/// V3Partition takes the fine-grained logic graph from V3Order and
/// collapses it into a coarse-grained graph of AbstractLogicMTask's, each
/// of which contains of set of the logic nodes from the fine-grained
/// graph.

class V3Partition {
    // MEMBERS
    V3Graph* m_fineDepsGraphp;  // Fine-grained dependency graph
public:
    // CONSTRUCTORS
    explicit V3Partition(V3Graph* fineDepsGraphp)
        : m_fineDepsGraphp(fineDepsGraphp) {}
    ~V3Partition() {}

    // METHODS

    // Fill in the provided empty graph with AbstractLogicMTask's and their
    // interdependencies.
    void go(V3Graph* mtasksp);

    static void selfTest();

    // Print out a hash of the shape of graphp.  Only needed to debug the
    // origin of some nondeterminism; otherwise this is pretty useless.
    static void hashGraphDebug(const V3Graph* graphp, const char* debugName);

    // Print debug stats about graphp whose nodes must be AbstractMTask's.
    static void debugMTaskGraphStats(const V3Graph* graphp, const string& stage);

    // Operate on the final ExecMTask graph, immediately prior to code
    // generation time.
    static void finalize();
private:
    static void finalizeCosts(V3Graph* execMTaskGraphp);
    static void setupMTaskDeps(V3Graph* mtasksp, const Vx2MTaskMap* vx2mtaskp);

    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(V3Partition);
};

//*************************************************************************
// Map a pointer into a id, for e.g. nodep to mtask mappings

class PartPtrIdMap {
private:
    // TYPES
    typedef vl_unordered_map <const void*, vluint64_t> PtrMap;
    // MEMBERS
    mutable vluint64_t m_nextId;
    mutable PtrMap m_id;
public:
    // CONSTRUCTORS
    PartPtrIdMap() : m_nextId(0) {}
    // METHODS
    vluint64_t findId(const void* ptrp) const {
        PtrMap::const_iterator it = m_id.find(ptrp);
        if (it != m_id.end()) return it->second;
        m_id[ptrp] = m_nextId;
        return m_nextId++;
    }
};

#endif  // Guard
