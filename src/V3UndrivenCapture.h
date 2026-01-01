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

//*************************************************************************
//
// Capture task/function write summaries for multidriven checks.
// Per-task/function capture info keyed by resolved AstNodeFTask*
// identity (FTask = function or task).  This is a 'graph' of
// tasks/functions.  Each node has a list of direct callees and
// a list of variables written in the function body.  There
// are methods to dedup after walking the tree. V3Undriven then uses
// the writeSummary for multidriven checks - i.e. it treats writes (side
// effects) inside subroutines as part of the caller's process.
//*************************************************************************

#ifndef VERILATOR_V3UNDRIVENCAPTURE_H_
#define VERILATOR_V3UNDRIVENCAPTURE_H_

#include "config_build.h"

#include "V3Ast.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

class AstNetlist;

class V3UndrivenCapture final {
public:
    // DFS computation state for writeSummary propagation.
    enum class State : uint8_t {
        UNVISITED,  // Write summary not computed yet
        VISITING,  // Currently computing on the call stack - used to detect cycles
        DONE  // Write summary computed
    };

    struct FTaskInfo final {
        // Variables written directly in this task/function body (iteration order)
        std::vector<AstVar*> directWrites;
        // Direct resolved callees from this task/function body (iteration order)
        std::vector<const AstNodeFTask*> callees;
        // 'Write through write' writeSummary for the given task/function.  Meaning ultimately
        // everything that this function/task writes to.
        std::vector<AstVar*> writeSummary;
        // State for writeSummary computation.
        State state = State::UNVISITED;
        // Test if already recorded a callee.  Used to 'filter' on insert
        // versus sorting at the end.
        std::unordered_set<const AstNodeFTask*> calleesSet;
        // Test if already recorded a direct write.  Used to 'filter' on
        // insert versus sorting at the end.
        std::unordered_set<AstVar*> directWritesSet;
    };

private:
    // Per-task/function capture info keyed by resolved AstNodeFTask* identity (FTask = function or
    // task).  The 'graph' of tasks/functions.  Each node has a list of direct callees and
    // a list of variables written in the function body.  There are methods to remove duplicates
    // otherwise this could explode.
    std::unordered_map<const AstNodeFTask*, FTaskInfo> m_info;

    // Collect direct writes and call edges for all tasks/functions.  Run one time when
    // UndrivenCapture is created.  This runs the visitor over the tree.
    void gather(AstNetlist* netlistp);
    // Compute (and cache) 'write through write' writeSummary for the given task/function.
    const std::vector<AstVar*>& computeWriteSummary(const AstNodeFTask* taskp);

public:
    // Build capture database and precompute writeSummary for all discovered tasks/functions.
    explicit V3UndrivenCapture(AstNetlist* netlistp);

    // Get write through write through write, etc (call chain) writeSummary for a task/function
    // (creates empty entry if needed).  This returns a vector of variables that a particular
    // task/function writes to, including all variables written by functions called by this
    // task/function, and so on.
    const std::vector<AstVar*>& writeSummary(const AstNodeFTask* taskp);

    // Used by the capture visitor to record information about tasks/functions and their statements
    // and callees. noteTask() makes sure there is an entry for the given taskp.
    void noteTask(const AstNodeFTask* taskp);
    // Inside the body of taskp there is a write to variable varp
    void noteDirectWrite(const AstNodeFTask* taskp, AstVar* varp);
    // Inside the body of callerp there is a call to calleep, this is needed so we can create a
    // summary that includes all variables written by functions called by this task/function, and
    // so on.
    void noteCallEdge(const AstNodeFTask* callerp, const AstNodeFTask* calleep);
};

#endif  // VERILATOR_V3UNDRIVENCAPTURE_H_
