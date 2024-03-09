// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Threading's logic to mtask partitioner
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

#ifndef VERILATOR_V3PARTITION_H_
#define VERILATOR_V3PARTITION_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"
#include "V3OrderGraph.h"
#include "V3ThreadSafety.h"

#include <list>
#include <unordered_map>

class LogicMTask;

//*************************************************************************
/// V3Partition takes the fine-grained logic graph from V3Order and
/// collapses it into a coarse-grained graph of AbstractLogicMTask's, each
/// of which contains of set of the logic nodes from the fine-grained
/// graph.

class V3Partition final {
    // MEMBERS
    const OrderGraph* const m_orderGraphp;  // The OrderGraph
    const V3Graph* const m_fineDepsGraphp;  // Fine-grained dependency graph

    LogicMTask* m_entryMTaskp = nullptr;  // Singular source vertex of the dependency graph
    LogicMTask* m_exitMTaskp = nullptr;  // Singular sink vertex of the dependency graph

public:
    // CONSTRUCTORS
    explicit V3Partition(const OrderGraph* orderGraphp, const V3Graph* fineDepsGraphp)
        : m_orderGraphp{orderGraphp}
        , m_fineDepsGraphp{fineDepsGraphp} {}
    ~V3Partition() = default;

    // METHODS

    // Fill in the provided empty graph with AbstractLogicMTask's and their
    // interdependencies.
    void go(V3Graph* mtasksp) VL_MT_DISABLED;

    static void selfTest() VL_MT_DISABLED;
    static void selfTestNormalizeCosts() VL_MT_DISABLED;

    // Print out a hash of the shape of graphp.  Only needed to debug the
    // origin of some nondeterminism; otherwise this is pretty useless.
    static void hashGraphDebug(const V3Graph* graphp, const char* debugName) VL_MT_DISABLED;

    // Print debug stats about graphp whose nodes must be AbstractMTask's.
    static void debugMTaskGraphStats(const V3Graph* graphp, const string& stage) VL_MT_DISABLED;

    // Operate on the final ExecMTask graph, immediately prior to code
    // generation time.
    static void finalize(AstNetlist* netlistp) VL_MT_DISABLED;

private:
    uint32_t setupMTaskDeps(V3Graph* mtasksp) VL_MT_DISABLED;

    VL_UNCOPYABLE(V3Partition);
};

#endif  // Guard
