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
    enum class State : uint8_t { UNVISITED, VISITING, DONE };

    struct FTaskInfo final {
        // Variables written directly in this task/function body.
        std::vector<Var> directWrites;
        // Direct resolved callees from this task/function body.
        std::vector<FTask> callees;
        // Transitive "may write" summary: directWrites plus all callees' summaries.
        std::vector<Var> writeSummary;
        // Memoization state for writeSummary computation.
        State state = State::UNVISITED;
    };

    static bool enableWriteSummary;

private:
    // Per-task/function capture info keyed by resolved AstNodeFTask* identity.
    std::unordered_map<FTask, FTaskInfo> m_info;

    // Sort and remove duplicates from a vector of variables.
    static void sortUniqueVars(std::vector<Var>& vec);
    // Sort and remove duplicates from a vector of callees.
    static void sortUniqueFTasks(std::vector<FTask>& vec);

    // Collect direct writes and call edges for all tasks/functions.
    void gather(AstNetlist* netlistp);
    // Compute (and memoize) transitive writeSummary for the given task/function.
    const std::vector<Var>& computeWriteSummary(FTask taskp);

public:
    // Build capture database and precompute writeSummary for all discovered tasks/functions.
    explicit V3UndrivenCapture(AstNetlist* netlistp);

    // Lookup task/function capture info (nullptr if unknown).
    const FTaskInfo* find(FTask taskp) const;
    // Get transitive writeSummary for a task/function (creates empty entry if needed).
    const std::vector<Var>& writeSummary(FTask taskp);

    // Ensure an entry exists for a task/function without computing its writeSummary.
    void ensureEntry(FTask taskp);

    // Optional: dump one task's summary (for debug bring-up). You can omit if you prefer.
    void debugDumpTask(FTask taskp, int level = 9) const;
};

#endif  // VERILATOR_V3UNDRIVENCAPTURE_H_