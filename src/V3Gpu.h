// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: GPU model partitioning and resident mode
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3GPU_H_
#define VERILATOR_V3GPU_H_

#include "config_build.h"
#include "verilatedos.h"

#include <string>
#include <vector>

class AstCFunc;
class AstNetlist;
class AstNode;
class AstNodeModule;
class AstVar;

class V3GpuCapture final {
public:
    static std::vector<AstVar*> vars(const AstNode* stmtp) VL_MT_DISABLED;
    static std::string memberName(const AstVar* varp) VL_MT_DISABLED;
};

struct V3GpuGroup final {
    int m_id = 0;  // Group number
    AstCFunc* m_launchp = nullptr;  // Host function that launches the kernels
    AstCFunc* m_bodyp = nullptr;  // Device function run by the kernel
    std::vector<std::vector<AstCFunc*>> m_levels;  // Device tasks per graph level
    std::vector<std::vector<AstCFunc*>> m_hostLevels;  // Host tasks per graph level
};

struct V3GpuResidentGraph final {
    std::vector<std::vector<AstCFunc*>> m_levels;  // Tasks per level
    std::vector<AstCFunc*> m_order;  // Tasks in topological order
    std::vector<std::vector<int>> m_preds;  // Per task: indices of its predecessors
};

struct V3GpuResident final {
    bool m_enabled = false;  // Resident mode is used
    AstCFunc* m_icop = nullptr;  // 'ico' region function
    AstCFunc* m_actp = nullptr;  // 'act' region function
    AstCFunc* m_inactp = nullptr;  // 'inact' region function
    AstCFunc* m_nbap = nullptr;  // 'nba' region function
    AstCFunc* m_obsp = nullptr;  // 'obs' region function
    AstCFunc* m_reactp = nullptr;  // 'react' region function
    AstCFunc* m_samplep = nullptr;  // Sampling at the start of a time step
    AstCFunc* m_postponedp = nullptr;  // Postponed region function
    AstVar* m_suspp = nullptr;  // Task graph a region suspended for
    std::vector<V3GpuResidentGraph> m_graphs;  // Task graphs run by the regions
};

struct V3GpuReplay final {
    int m_id = 0;  // Record identifier
    AstCFunc* m_funcp = nullptr;  // Host function that replays the record
};

class V3Gpu final {
public:
    static void analyze(AstNetlist* nodep) VL_MT_DISABLED;
    static void partition(AstNetlist* nodep) VL_MT_DISABLED;
    static bool isDeviceFunc(const AstCFunc* funcp) VL_MT_DISABLED;
    static bool isKernelBody(const AstCFunc* funcp) VL_MT_DISABLED;
    static const std::vector<AstCFunc*>& deviceFuncs() VL_MT_DISABLED;
    static const std::vector<V3GpuGroup>& groups() VL_MT_DISABLED;
    static const std::vector<V3GpuReplay>& replays() VL_MT_DISABLED;
    static int replayId(const AstNode* stmtp) VL_MT_DISABLED;
    static AstNodeModule* modulep() VL_MT_DISABLED;
    static bool isMember(const AstVar* varp) VL_MT_DISABLED;
    static bool isHostMember(const AstVar* varp) VL_MT_DISABLED;
    static bool isGpuDpi(const AstCFunc* funcp) VL_MT_DISABLED;
    static std::string dpiName(const AstCFunc* funcp) VL_MT_DISABLED;
    static bool isGpuNoopStmt(const AstNode* nodep) VL_MT_DISABLED;
    static bool isGpuAssertCtlExpr(const AstNode* nodep) VL_MT_DISABLED;
    static std::string gpuAssertCtlText(const AstNode* nodep) VL_MT_DISABLED;
    static bool lowerTiming(AstNetlist* nodep) VL_MT_DISABLED;
    static void residentPrepare(AstNetlist* nodep) VL_MT_DISABLED;
    static void residentPartition(AstNetlist* nodep) VL_MT_DISABLED;
    static bool residentMode() VL_MT_DISABLED;
    static const V3GpuResident& resident() VL_MT_DISABLED;
    static bool isResidentGraphPoint(const AstNode* nodep, int& graph, int& label) VL_MT_DISABLED;
    static AstVar* residentGraphPc(const AstNode* nodep) VL_MT_DISABLED;
    static bool isResidentStmt(const AstNode* nodep) VL_MT_DISABLED;
    static std::string deviceCExprText(const AstNode* nodep) VL_MT_DISABLED;
    static std::string deviceCStmtText(const AstNode* nodep, bool& known) VL_MT_DISABLED;
    static AstVar* timingFinishVarp() VL_MT_DISABLED;
    static AstVar* timingFatalVarp() VL_MT_DISABLED;
    static const std::vector<std::string>& fatalMessages() VL_MT_DISABLED;
    static AstVar* timingOverflowVarp() VL_MT_DISABLED;
    static AstVar* timingTbaseVarp() VL_MT_DISABLED;
    static AstCFunc* timingNextTimeFuncp() VL_MT_DISABLED;
    static bool timingLowered() VL_MT_DISABLED;
    static AstCFunc* eventsPendingFuncp() VL_MT_DISABLED;
    static AstCFunc* nextTimeSlotFuncp() VL_MT_DISABLED;
    static bool isTimingNowExpr(const AstNode* nodep) VL_MT_DISABLED;
    static bool isTimingFinishExpr(const AstNode* nodep) VL_MT_DISABLED;
    static bool isTimingDeviceStmt(const AstNode* nodep) VL_MT_DISABLED;
    static std::string kernelBodyIfdef() { return "VL_GPU_KERNEL_BODY_NEVER_DEFINED"; }
};

#endif
