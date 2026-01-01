// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
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

// A TriggerKit holds all the components related to a scheduling region triggers
//
// Each piece of code is executed when some trigger bits are set. There is no
// code after scheduling which is not conditional on at least one trigger bit.
//
// There are 3 different kinds of triggers
// 1. "Sense" triggers, which correspond to a unique SenItem in the design
// 2. "Extra" triggers, which represent non SenItem based conditions
// 3. "Pre" triggers, which are only used in the 'act' region. These are a copy
//    of some of the "Sense" triggers but only ever fire during one evaluation
//    of the 'act' loop. They are used for executing AlwaysPre block that
//    reside in the 'act' region. (AlwaysPre in 'nba' use the "Sense" triggers.)
//
// All trigger bits are stored in an unpacked array of fixed sized words, which
// is informally referred to in various places as the "trigger vector".
// There is only one trigger vector for each eval loop (~scheduling region).
//
// The organization of the trigger vector (array) is shown here, LSB on the
// right, MSB on the left. There are 4 main sections:
//
// | <- bit N-1                                                                         bit 0 -> |
// +--------------------+----------------+----------------------------------+--------------------+
// | Pre triggers       | Extra triggers | Sense triggers                   | Pre Sense triggers |
// +--------------------+----------------+----------------------------------+--------------------+
// |        'pre'       |                                 'vec'                                  |
//
// The section labelled "Pre Sense triggers" contains regular "Sense" triggers
// that are also duplicated in the "Pre triggers" section the first time they
// fire.
//
// The "Sense triggers" section contains the rest of the "Sense" triggers that
// do not need a copy in "Pre triggers".
//
// The "Sense triggers" and "Pre Sense triggers" together contain all "Sense"
// triggers described in point 1 above. "Extra triggers" contains the
// non-SenItem based additional conditions described in point 2, and the
// "Per triggers" section contains the "Pre" triggers described in point 3.
//
// All 4 sections in the trigger vector are padded to contain a whole word
// worth of bits (padding bits are always zero). Any one of the 4 sections
// can be empty, but "Pre triggers" and "Pre Sense triggers" are always the
// same size.
//
// The portion holding the Sense triggers and Extra triggers is referred to
// in various places as the 'vec' part, and is also informally referred to as
// the trigger vector.
//
// The portion holding the Pre trigger is named 'pre'
//
// The combination of 'pre' + 'vec' is the "extended trigger vector" referred
// to as 'ext' in various places.
//
// In realistic designs there are often no "Pre" triggers, and only a few
// "Extra" triggers, with "Sense" triggers taking up the bulk of the bits.
//
class TriggerKit final {
    // Triggers are storead as an UnpackedArray with a fixed word size
    static constexpr uint32_t WORD_SIZE_LOG2 = 6;  // 64-bits / VL_QUADSIZE
    static constexpr uint32_t WORD_SIZE = 1 << WORD_SIZE_LOG2;

    const std::string m_name;  // TriggerKit name
    const bool m_slow;  // TriggerKit is for schedulign 'slow' code
    const uint32_t m_nSenseWords;  // Number of words for Sense triggers
    const uint32_t m_nExtraWords;  // Number of words for Extra triggers
    const uint32_t m_nPreWords;  // Number of words for 'pre' part
    const uint32_t m_nVecWords = m_nSenseWords + m_nExtraWords;  // Number of words in 'vec' part

    // Data type of a single trigger word
    AstNodeDType* m_wordDTypep = nullptr;
    // Data type of a trigger vector holding one copy of all triggers
    AstUnpackArrayDType* m_trigVecDTypep = nullptr;
    // Data type of an extended trigger vector holding one copy of all triggers
    // + additional copy of 'pre' triggers
    AstUnpackArrayDType* m_trigExtDTypep = nullptr;
    // The AstVarScope representing the extended trigger vector
    AstVarScope* m_vscp = nullptr;
    // The AstCFunc that computes the current active triggers
    AstCFunc* m_compp = nullptr;
    // The AstCFunc that dumps a trigger vector
    AstCFunc* m_dumpp = nullptr;
    // The AstCFunc that dumps an exended trigger vector - create lazily
    mutable AstCFunc* m_dumpExtp = nullptr;
    // The AstCFunc testing if a trigger vector has any bits set - create lazily
    mutable AstCFunc* m_anySetVecp = nullptr;
    mutable AstCFunc* m_anySetExtp = nullptr;
    // The AstCFunc setting bits in a trigger vector that are set in another - create lazily
    mutable AstCFunc* m_orIntoVecp = nullptr;
    mutable AstCFunc* m_orIntoExtp = nullptr;
    // The AstCFunc setting a trigger vector to all zeroes - create lazily
    mutable AstCFunc* m_clearp = nullptr;

    // The map from 'pre' input SenTree to trigger SenTree
    std::unordered_map<const AstSenTree*, AstSenTree*> m_mapPre;
    // The map from other input SenTree to trigger SenTree
    std::unordered_map<const AstSenTree*, AstSenTree*> m_mapVec;

    // Methods to lazy construct functions processing trigger vectors
    AstCFunc* createDumpExtFunc() const;
    AstCFunc* createAnySetFunc(AstUnpackArrayDType* const dtypep) const;
    AstCFunc* createClearFunc() const;
    AstCFunc* createOrIntoFunc(AstUnpackArrayDType* const iDtypep) const;

    // Create an AstSenTree that is sensitive to the given trigger indices
    AstSenTree* newTriggerSenTree(AstVarScope* vscp, const std::vector<uint32_t>& indices) const;

    TriggerKit(const std::string& name, bool slow, uint32_t nSenseWords, uint32_t nExtraWords,
               uint32_t nPreWords);
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
                             const std::vector<const AstSenTree*>& preTreeps,  //
                             const std::vector<const AstSenTree*>& senTreeps,  //
                             const string& name,  //
                             const ExtraTriggers& extraTriggers,  //
                             bool slow);

    // ACCESSORS
    AstVarScope* vscp() const { return m_vscp; }
    AstCFunc* compp() const { return m_compp; }
    const std::unordered_map<const AstSenTree*, AstSenTree*>& mapPre() const { return m_mapPre; }
    const std::unordered_map<const AstSenTree*, AstSenTree*>& mapVec() const { return m_mapVec; }

    // Helpers for code generation - lazy construct relevant functions
    AstNodeStmt* newAndNotCall(AstVarScope* op, AstVarScope* ap, AstVarScope* bp) const;
    AstNodeExpr* newAnySetCall(AstVarScope* vscp) const;
    AstNodeStmt* newClearCall(AstVarScope* vscp) const;
    AstNodeStmt* newOrIntoCall(AstVarScope* op, AstVarScope* ip) const;
    // Helpers for code generation
    AstNodeStmt* newCompCall(AstVarScope* vscp = nullptr) const;
    AstNodeStmt* newDumpCall(AstVarScope* vscp, const std::string& tag, bool debugOnly) const;
    // Create a new (non-extended) trigger vector - might return nullptr if there are no triggers
    AstVarScope* newTrigVec(const std::string& name) const;

    // Create an AstSenTree that is sensitive to the given Extra trigger
    AstSenTree* newExtraTriggerSenTree(AstVarScope* vscp, uint32_t index) const;

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
// Split large function according to --output-split-cfuncs
void splitCheck(AstCFunc* ofuncp);
// Build an AstIf conditional on the given SenTree being triggered
AstIf* createIfFromSenTree(AstSenTree* senTreep);
}  // namespace util

}  // namespace V3Sched

#endif  // Guard
