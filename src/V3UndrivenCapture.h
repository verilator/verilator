// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Capture task/function write summaries for undriven checks
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

#ifndef VERILATOR_V3UNDRIVENCAPTURE_H_
#define VERILATOR_V3UNDRIVENCAPTURE_H_

#include "config_build.h"

#include "V3Ast.h"

#include <unordered_map>
#include <vector>

class AstNetlist;

class V3UndrivenCapture final {
public:
    using FTask = const AstNodeFTask*;
    using Var = AstVar*;

    // DFS computation state for writeSummary propagation.
    // UNVISITED: write summary not computed yet
    // VISITING: currently computing on the call stack - used to detect cycles
    // DONE: write summary computed
    enum class State : uint8_t { UNVISITED, VISITING, DONE };

    struct FTaskInfo final {
        // Variables written directly in this task/function body.
        std::vector<Var> directWrites;
        // Direct resolved callees from this task/function body.
        std::vector<FTask> callees;
        // 'write through write' writeSummary for the given task/function.  Meaning ultimately everything that this function/task writes to.
        std::vector<Var> writeSummary;
        // state for writeSummary computation.
        State state = State::UNVISITED;
    };

    // Enable writeSummary computation.  If disabled, then the existing V3Undriven behaviour is used.
    static bool enableWriteSummary;

private:
    // Per-task/function capture info keyed by resolved AstNodeFTask* identity (FTask = function or task).  This is our 'graph' of tasks/functions.  Each node has a list of direct callees and a list of variables written in the function body.  There are methods to remove duplicates otherwise this could explode.
    std::unordered_map<FTask, FTaskInfo> m_info;

    // Sort and remove duplicates from a vector of variables.  This is called after a task/function write summary is computed.  writeSummary can accumulate duplicates if a variable is written in multiple tasks/functions.
    static void sortUniqueVars(std::vector<Var>& vec);
    // Sort and remove duplicates from a vector of callees.  The visitor can record the same callee multiple times (multiple call sites, branches, etc).
    static void sortUniqueFTasks(std::vector<FTask>& vec);

    // Collect direct writes and call edges for all tasks/functions.  Run one time when UndrivenCapture is created.  This runs the visitor over the tree.
    void gather(AstNetlist* netlistp);
    // Compute (and cache) 'write through write' writeSummary for the given task/function.
    const std::vector<Var>& computeWriteSummary(FTask taskp);

public:
    // Build capture database and precompute writeSummary for all discovered tasks/functions.
    explicit V3UndrivenCapture(AstNetlist* netlistp);

    // Lookup task/function capture info (nullptr if unknown).  This is currently only used for the debug helper.
    const FTaskInfo* find(FTask taskp) const;
    // Get write through write through write, etc (call chain) writeSummary for a task/function (creates empty entry if needed).  This returns a vector of variables that a particular task/function writes to, including all variables written by functions called by this task/function, and so on.
    const std::vector<Var>& writeSummary(FTask taskp);

    // used by the capture visitor to record information about tasks/functions and their statements and callees.
    // noteTask() makes sure there is an entry for the given taskp.
    void noteTask(FTask taskp);
    // inside the body of taskp there is a write to variable varp
    void noteDirectWrite(FTask taskp, Var varp);
    // inside the body of callerp there is a call to calleep, this is needed so we can create a summary that includes all variables written by functions called by this task/function, and so on.
    void noteCallEdge(FTask callerp, FTask calleep);

    // dump one task's summary for debugging.  leaving this in, in case need to debug future functionality.
    void debugDumpTask(FTask taskp, int level = 9) const;
};

#endif  // VERILATOR_V3UNDRIVENCAPTURE_H_
