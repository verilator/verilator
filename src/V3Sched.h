// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
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

#ifndef VERILATOR_V3SCHED_H_
#define VERILATOR_V3SCHED_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"

#include <functional>
#include <unordered_map>
#include <utility>
#include <vector>

class SenExprBuilder;

//============================================================================

namespace V3Sched {

//============================================================================
// Throughout scheduling, we need to keep hold of AstActive nodes, together with the AstScope that
// they are under. LogicByScope is simply a vector of such pairs, with some additional convenience
// methods.
struct LogicByScope final : public std::vector<std::pair<AstScope*, AstActive*>> {
    // Add logic
    void add(AstScope* scopep, AstSenTree* senTreep, AstNode* logicp) {
        UASSERT_OBJ(!logicp->backp(), logicp, "Already linked");
        if (empty() || back().first != scopep || back().second->sentreep() != senTreep) {
            emplace_back(scopep, new AstActive{logicp->fileline(), "", senTreep});
        }
        back().second->addStmtsp(logicp);
    };

    // Create copy, with the AstActives cloned
    LogicByScope clone() const {
        LogicByScope result;
        for (const auto& pair : *this) {
            result.emplace_back(pair.first, pair.second->cloneTree(false));
        }
        return result;
    }

    // Delete actives (they should all be empty)
    void deleteActives() {
        for (const auto& pair : *this) {
            AstActive* const activep = pair.second;
            if (v3Global.opt.debugCheck()) {
                for (AstNode* nodep = activep->stmtsp(); nodep; nodep = nodep->nextp()) {
                    AstNodeProcedure* const procp = VN_CAST(nodep, NodeProcedure);
                    UASSERT_OBJ(procp && !procp->stmtsp(), activep, "Leftover logic");
                }
            }
            if (activep->backp()) activep->unlinkFrBack();
            activep->deleteTree();
        }
        clear();
    };

    void foreachLogic(const std::function<void(AstNode*)>& f) const {
        for (const auto& pair : *this) {
            for (AstNode* nodep = pair.second->stmtsp(); nodep; nodep = nodep->nextp()) f(nodep);
        }
    }
};

// Logic in the design is classified based on what can trigger its execution.
// For details see the internals documentation.
struct LogicClasses final {
    LogicByScope m_static;  // Static variable initializers
    LogicByScope m_initial;  // initial blocks
    LogicByScope m_final;  // final blocks
    LogicByScope m_comb;  // Combinational logic (logic with implicit sensitivities)
    LogicByScope m_clocked;  // Clocked (or sequential) logic (logic with explicit sensitivities)
    LogicByScope m_hybrid;  // Hybrid logic (combinational logic with some explicit sensitivities)
    LogicByScope m_postponed;  // Postponed logic ($strobe)
    LogicByScope m_observed;  // Observed logic (contains AstAlwaysObserved)
    LogicByScope m_reactive;  // Reactive logic (contains AstAlwaysReactive)

    LogicClasses() = default;
    VL_UNCOPYABLE(LogicClasses);
    LogicClasses(LogicClasses&&) = default;
    LogicClasses& operator=(LogicClasses&&) = default;
};

// Combinational (including hybrid) logic, and clocked logic in partitioned to compute all clock
// signals in the 'act' region. For details see the internals documentation.
struct LogicRegions final {
    LogicByScope m_pre;  // AstAlwaysPre logic in 'act' region
    LogicByScope m_act;  // 'act' region logic
    LogicByScope m_nba;  // 'nba' region logic
    LogicByScope m_obs;  // AstAlwaysObserved logic in 'obs' region
    LogicByScope m_react;  // AstAlwaysReactive logic in 're' region

    LogicRegions() = default;
    VL_UNCOPYABLE(LogicRegions);
    LogicRegions(LogicRegions&&) = default;
    LogicRegions& operator=(LogicRegions&&) = default;
};

// Combinational (including hybrid) logic is replicated into the various scheduling regions.
// For details see the internals documentation.
struct LogicReplicas final {
    LogicByScope m_ico;  // Logic replicated into the 'ico' (Input Combinational) region
    LogicByScope m_act;  // Logic replicated into the 'act' region
    LogicByScope m_nba;  // Logic replicated into the 'nba' region
    LogicByScope m_obs;  // Logic replicated into the 'obs' region
    LogicByScope m_react;  // Logic replicated into the 're' region

    LogicReplicas() = default;
    VL_UNCOPYABLE(LogicReplicas);
    LogicReplicas(LogicReplicas&&) = default;
    LogicReplicas& operator=(LogicReplicas&&) = default;
};

// A TriggerKit holds all the components related to a trigger vector
class TriggerKit final {
    // Triggers are storead as an UnpackedArray with a fixed word size
    static constexpr uint32_t WORD_SIZE_LOG2 = 6;  // 64-bits / VL_QUADSIZE
    static constexpr uint32_t WORD_SIZE = 1 << WORD_SIZE_LOG2;

    const std::string m_name;  // TriggerKit name
    const bool m_slow;  // TriggerKit is for schedulign 'slow' code
    const uint32_t m_nWords;  // Number of word in trigger vector

    // Data type of a single trigger word
    AstNodeDType* m_wordDTypep;
    // Data type of a trigger vector
    AstNodeDType* m_trigDTypep;
    // The AstVarScope representing the trigger vector
    AstVarScope* m_vscp;
    // The AstCFunc that computes the current active triggers
    AstCFunc* m_compp;
    // The AstCFunc that dumps the current active triggers
    AstCFunc* m_dumpp;
    // The AstCFunc testing if a trigger vector has any bits set - create lazily
    mutable AstCFunc* m_anySetp = nullptr;
    // The AstCFunc setting a tigger vector to (_ & ~_) of 2 other trigger vectors - create lazily
    mutable AstCFunc* m_andNotp = nullptr;
    // The AstCFunc setting bits in a trigger vector that are set in another - create lazily
    mutable AstCFunc* m_orIntop = nullptr;
    // The AstCFunc setting a trigger vector to all zeroes - create lazily
    mutable AstCFunc* m_clearp = nullptr;

    // The map from input sensitivity list to trigger sensitivity list
    std::unordered_map<const AstSenTree*, AstSenTree*> m_map;

    // Methods to lazy construct functions processing trigger vectors
    AstCFunc* createAndNotFunc() const;
    AstCFunc* createAnySetFunc() const;
    AstCFunc* createClearFunc() const;
    AstCFunc* createOrIntoFunc() const;

    TriggerKit(const std::string& name, bool slow, uint32_t nWords);
    VL_UNCOPYABLE(TriggerKit);
    TriggerKit& operator=(TriggerKit&&) = delete;

public:
    // Move constructible
    TriggerKit(TriggerKit&&) = default;
    ~TriggerKit() = default;

    // Utility for extra trigger allocation
    class ExtraTriggers final {
        friend class TriggerKit;
        std::vector<string> m_descriptions;  // Human readable description of extra triggers

    public:
        ExtraTriggers() = default;
        ~ExtraTriggers() = default;

        uint32_t allocate(const string& description) {
            m_descriptions.push_back(description);
            return m_descriptions.size() - 1;
        }
        uint32_t size() const { return m_descriptions.size(); }
    };

    // Create a TriggerKit for the given AstSenTree vector
    static TriggerKit create(AstNetlist* netlistp,  //
                             AstCFunc* const initFuncp,  //
                             SenExprBuilder& senExprBuilder,  //
                             const std::vector<const AstSenTree*>& senTreeps,  //
                             const string& name,  //
                             const ExtraTriggers& extraTriggers,  //
                             bool slow);

    // ACCESSORS
    AstVarScope* vscp() const { return m_vscp; }
    AstCFunc* compp() const { return m_compp; }
    AstCFunc* dumpp() const { return m_dumpp; }
    const std::unordered_map<const AstSenTree*, AstSenTree*>& map() const { return m_map; }

    // Helpers for code generation - lazy construct relevant functions
    AstNodeStmt* newAndNotCall(AstVarScope* op, AstVarScope* ap, AstVarScope* bp) const;
    AstNodeExpr* newAnySetCall(AstVarScope* vscp) const;
    AstNodeStmt* newClearCall(AstVarScope* vscp) const;
    AstNodeStmt* newOrIntoCall(AstVarScope* op, AstVarScope* ip) const;
    // Helpers for code generation
    AstNodeStmt* newCompCall() const;
    AstNodeStmt* newDumpCall(AstVarScope* vscp, const std::string& tag, bool debugOnly) const;

    // Create an AstSenTree that is sensitive to the given trigger indices
    AstSenTree* newTriggerSenTree(AstVarScope* vscp, const std::vector<uint32_t>& indices) const;

    // Set then extra trigger bit at 'index' to the value of 'vscp', then set 'vscp' to 0
    void addExtraTriggerAssignment(AstVarScope* vscp, uint32_t index) const;
};

// Everything needed for combining timing with static scheduling.
class TimingKit final {
    AstCFunc* m_resumeFuncp = nullptr;  // Global timing resume function
    AstCFunc* m_commitFuncp = nullptr;  // Global timing commit function

    // Additional var sensitivities for V3Order
    std::map<const AstVarScope*, std::set<AstSenTree*>> m_externalDomains;

public:
    LogicByScope m_lbs;  // Actives that resume timing schedulers
    AstNodeStmt* m_postUpdates = nullptr;  // Post updates for the trigger eval function

    // Remaps external domains using the specified trigger map
    std::map<const AstVarScope*, std::vector<AstSenTree*>> remapDomains(
        const std::unordered_map<const AstSenTree*, AstSenTree*>& trigMap) const VL_MT_DISABLED;
    // Creates a timing resume call (if needed, else returns null)
    AstCCall* createResume(AstNetlist* const netlistp) VL_MT_DISABLED;
    // Creates a timing commit call (if needed, else returns null)
    AstCCall* createCommit(AstNetlist* const netlistp) VL_MT_DISABLED;

    TimingKit() = default;
    TimingKit(LogicByScope&& lbs, AstNodeStmt* postUpdates,
              std::map<const AstVarScope*, std::set<AstSenTree*>>&& externalDomains)
        : m_externalDomains{externalDomains}
        , m_lbs{lbs}
        , m_postUpdates{postUpdates} {}
    VL_UNCOPYABLE(TimingKit);
    TimingKit(TimingKit&&) = default;
    TimingKit& operator=(TimingKit&&) = default;
};

class VirtIfaceTriggers final {
    // Represents a specific member in a virtual interface
    struct IfaceMember final {
        const AstIface* m_ifacep;  // Interface type
        const AstVar* m_memberp;  // Member variable

        // TODO: sorting by pointer is non-deterministic
        bool operator<(const IfaceMember& other) const {
            if (m_ifacep != other.m_ifacep) return m_ifacep < other.m_ifacep;
            return m_memberp < other.m_memberp;
        }
    };

public:
    using IfaceSensMap = std::map<const AstIface*, AstSenTree*>;
    using IfaceMemberSensMap = std::map<IfaceMember, AstSenTree*>;

    std::vector<std::pair<const AstIface*, AstVarScope*>> m_ifaceTriggers;
    std::vector<std::pair<IfaceMember, AstVarScope*>> m_memberTriggers;

    void addIfaceTrigger(const AstIface* ifacep, AstVarScope* vscp) {
        m_ifaceTriggers.emplace_back(ifacep, vscp);
    }
    void addMemberTrigger(const AstIface* ifacep, const AstVar* memberp, AstVarScope* vscp) {
        m_memberTriggers.emplace_back(IfaceMember{ifacep, memberp}, vscp);
    }

    AstVarScope* findMemberTrigger(const AstIface* ifacep, const AstVar* memberp) const {
        for (const auto& pair : m_memberTriggers) {
            const IfaceMember& item = pair.first;
            if (item.m_ifacep == ifacep && item.m_memberp == memberp) return pair.second;
        }
        return nullptr;
    }

    IfaceMemberSensMap makeMemberToSensMap(const TriggerKit& trigKit, uint32_t vifTriggerIndex,
                                           AstVarScope* trigVscp) const;

    IfaceSensMap makeIfaceToSensMap(const TriggerKit& trigKit, uint32_t vifTriggerIndex,
                                    AstVarScope* trigVscp) const;

    VL_UNCOPYABLE(VirtIfaceTriggers);
    VirtIfaceTriggers() = default;
    VirtIfaceTriggers(VirtIfaceTriggers&&) = default;
    VirtIfaceTriggers& operator=(VirtIfaceTriggers&&) = default;
};

// Creates trigger vars for signals driven via virtual interfaces
VirtIfaceTriggers makeVirtIfaceTriggers(AstNetlist* nodep) VL_MT_DISABLED;

// Creates the timing kit and marks variables written by suspendables
TimingKit prepareTiming(AstNetlist* const netlistp) VL_MT_DISABLED;

// Transforms fork sub-statements into separate functions
void transformForks(AstNetlist* const netlistp) VL_MT_DISABLED;

// Top level entry point to scheduling
void schedule(AstNetlist*) VL_MT_DISABLED;

// Sub-steps
LogicByScope breakCycles(AstNetlist* netlistp,
                         const LogicByScope& combinationalLogic) VL_MT_DISABLED;
LogicRegions partition(LogicByScope& clockedLogic, LogicByScope& combinationalLogic,
                       LogicByScope& hybridLogic) VL_MT_DISABLED;
LogicReplicas replicateLogic(LogicRegions&) VL_MT_DISABLED;

// Utility functions used by various steps in scheduling
namespace util {
// Create a new top level entry point
AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow);
// Create a new sub function (not an entry point)
AstCFunc* makeSubFunction(AstNetlist* netlistp, const string& name, bool slow);
// Create statement that sets the given 'vscp' to 'val'
AstNodeStmt* setVar(AstVarScope* vscp, uint32_t val);
// Create statement that increments the given 'vscp' by one
AstNodeStmt* incrementVar(AstVarScope* vscp);
// Create statement that calls the given 'void' returning function
AstNodeStmt* callVoidFunc(AstCFunc* funcp);
// Create statement that checks counterp' to see if the eval loop iteration limit is reached
AstNodeStmt* checkIterationLimit(AstNetlist* netlistp, const string& name, AstVarScope* counterp,
                                 AstNodeStmt* dumpCallp);
// Create statement that pushed a --prof-exec section
AstNodeStmt* profExecSectionPush(FileLine* flp, const string& section);
// Create statement that pops a --prof-exec section
AstNodeStmt* profExecSectionPop(FileLine* flp);
// Split large function according to --output-split-cfuncs
void splitCheck(AstCFunc* ofuncp);
// Build an AstIf conditional on the given SenTree being triggered
AstIf* createIfFromSenTree(AstSenTree* senTreep);
}  // namespace util

}  // namespace V3Sched

#endif  // Guard
