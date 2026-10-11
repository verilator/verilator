// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Functional coverage implementation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// FUNCTIONAL COVERAGE TRANSFORMATIONS:
//      For each covergroup (AstClass with isCovergroup()):
//          For each coverpoint (AstCoverpoint):
//              Generate member variable for VerilatedCoverpoint
//              Generate initialization in constructor
//              Generate sample code in sample() method
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Covergroup.h"

#include "V3Const.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3MemberMap.h"
#include "V3UniqueNames.h"

#include <bitset>
#include <cmath>
#include <deque>
#include <set>
#include <tuple>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Embedded covergroup assignment validation; and in the same pass over the netlist, the
// type_option variables through which SystemVerilog may set type_option.merge_instances

class CovergroupAssignValidVisitor final : public VNVisitorConst {
    VMemberMap m_memberMap;
    std::map<const AstVar*, const AstNodeFTask*>
        m_constructors;  // Implicit instance -> constructor
    std::set<const AstVar*> m_mergeableTypeOptions;  // See mergeableTypeOptions()
    const AstNodeFTask* m_ftaskp = nullptr;
    bool m_collecting = true;
    bool m_valid = true;

    void visit(AstClass* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nullptr;
        if (m_collecting) {
            const AstNodeFTask* const constructorp
                = VN_CAST(m_memberMap.findMember(nodep, "new"), NodeFTask);
            for (const AstNode* itemp = nodep->membersp(); itemp; itemp = itemp->nextp()) {
                const AstVar* const varp = VN_CAST(itemp, Var);
                // Only the implicit instance is restricted, not explicitly typed aliases.
                if (!varp || !varp->isClassMember() || varp->isDeclTyped()) continue;
                const AstClassRefDType* const refp
                    = VN_CAST(varp->dtypep()->skipRefp(), ClassRefDType);
                if (refp && refp->classp()->covergroupEnclosingClassp() == nodep) {
                    m_constructors.emplace(varp, constructorp);
                }
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        m_ftaskp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        if (!m_collecting) {
            const AstVar* varp = nullptr;
            if (const AstNodeVarRef* const refp = VN_CAST(nodep->lhsp(), NodeVarRef)) {
                varp = refp->varp();
            } else if (const AstMemberSel* const selp = VN_CAST(nodep->lhsp(), MemberSel)) {
                varp = selp->varp();
            }
            const auto it = m_constructors.find(varp);
            if (it != m_constructors.end() && (!m_ftaskp || m_ftaskp != it->second)) {
                m_valid = false;
                nodep->v3error("Embedded covergroup variable "
                               << varp->prettyNameQ()
                               << " may only be assigned in the enclosing class's 'new' method "
                                  "(IEEE 1800-2023 19.4).");
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        // Type options may be set at any time (IEEE 1800-2023 19.7.1), so SystemVerilog may set
        // type_option.merge_instances with any use of a type_option but a read of another
        // member, as not every write is marked yet (std::randomize)
        if (m_collecting && nodep->varp()->name() == "type_option") {
            const AstStructSel* const selp = VN_CAST(nodep->backp(), StructSel);
            if (!selp || selp->fromp() != nodep || selp->name() == "merge_instances"
                || !nodep->access().isReadOnly()) {
                m_mergeableTypeOptions.insert(nodep->varp());
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit CovergroupAssignValidVisitor(AstNetlist* nodep) {
        // Uses can precede their enclosing class in the tree.
        iterateConst(nodep);
        m_collecting = false;
        if (!m_constructors.empty()) iterateConst(nodep);
    }
    bool valid() const { return m_valid; }
    // type_option variables through which SystemVerilog may set type_option.merge_instances, so
    // that covergroups are tested with optionVar(true)
    const std::set<const AstVar*>& mergeableTypeOptions() const { return m_mergeableTypeOptions; }
};

//######################################################################
// Covergroup expression validation visitor

class CovergroupExprValidVisitor final : public VNVisitor {
    const std::set<const AstVar*>& m_sampleMembers;
    const std::set<const AstVar*>& m_constructorRefMembers;
    bool m_inCoverageExpression = false;
    bool m_sampleFormalAllowed = false;

    void scanSampleExpression(AstNode* nodep) {
        if (!nodep) return;
        VL_RESTORER(m_sampleFormalAllowed);
        m_sampleFormalAllowed = true;
        iterateAndNextNull(nodep);
    }

    void scanCoverageExpression(AstNode* nodep) {
        if (!nodep) return;
        VL_RESTORER(m_inCoverageExpression);
        m_inCoverageExpression = true;
        iterateAndNextNull(nodep);
    }

    void visit(AstCoverpoint* nodep) override {
        scanSampleExpression(nodep->exprp());
        scanSampleExpression(nodep->iffp());
        iterateAndNextNull(nodep->binsp());
        iterateAndNextNull(nodep->optionsp());
    }
    void visit(AstCoverCross* nodep) override {
        iterateAndNextNull(nodep->itemsp());
        scanSampleExpression(nodep->iffp());
        iterateAndNextNull(nodep->optionsp());
        iterateAndNextNull(nodep->binsp());
    }
    void visit(AstCoverCrossBin* nodep) override {
        iterateAndNextNull(nodep->selectp());
        scanSampleExpression(nodep->iffp());
    }
    void visit(AstCoverBinsof* nodep) override { scanCoverageExpression(nodep->rangesp()); }
    void visit(AstCoverBin* nodep) override {
        scanCoverageExpression(nodep->rangesp());
        scanSampleExpression(nodep->iffp());
        scanCoverageExpression(nodep->arraySizep());
        scanCoverageExpression(nodep->transp());
    }
    void visit(AstVarRef* nodep) override {
        if (!m_sampleFormalAllowed && m_sampleMembers.count(nodep->varp())) {
            nodep->v3error("Covergroup sample formal argument "
                           << nodep->varp()->prettyNameQ()
                           << " may only be used in a coverpoint or conditional guard "
                              "expression (IEEE 1800-2023 19.8.1).");
        }
        if (m_inCoverageExpression && m_constructorRefMembers.count(nodep->varp())) {
            nodep->v3error("Ref covergroup constructor formal argument "
                           << nodep->varp()->prettyNameQ()
                           << " may not be used in a covergroup expression "
                              "(IEEE 1800-2023 19.5).");
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (m_inCoverageExpression && nodep->taskp()) {
            bool invalidDirection = false;
            for (AstNode* stmtp = nodep->taskp()->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                const AstVar* const varp = VN_CAST(stmtp, Var);
                if (varp && varp->isIO() && varp->isWritable()) {
                    invalidDirection = true;
                    break;
                }
            }
            if (invalidDirection) {
                nodep->v3error("Function " << nodep->taskp()->prettyNameQ()
                                           << " called in a covergroup expression has an "
                                              "output, inout, or non-const ref argument "
                                              "(IEEE 1800-2023 19.5).");
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    CovergroupExprValidVisitor(const std::set<const AstVar*>& sampleMembers,
                               const std::set<const AstVar*>& constructorRefMembers)
        : m_sampleMembers{sampleMembers}
        , m_constructorRefMembers{constructorRefMembers} {}
    void scan(AstNode* nodep) { iterate(nodep); }
};

//######################################################################
// Bins of one declaration whose values are computed rather than listed: bin k covers
// [m_lo + k * m_stride, m_lo + (k + 1) * m_stride - 1], and the last bin extends to m_hi.  An
// array bin element is a run of single-value bins; automatic bins partition the coverpoint
// domain.  Bounds are coverpoint values at FunctionalCoverageVisitor::runWidth(),
// sign-extended like a CrossValueRange's.

class BinRun final {
public:
    // MEMBERS
    uint32_t m_count;  // Number of bins
    V3Number m_lo;  // Lowest value of the first bin
    V3Number m_stride;  // Number of values of each bin but the last
    V3Number m_hi;  // Highest value of the last bin
    bool m_empty = false;  // A single bin without a value of the coverpoint type
    uint32_t m_declared = 0;  // Runtime index of the first bin, once generated

    // CONSTRUCTORS
    BinRun(AstNode* nodep, int width, uint32_t count)
        : m_count{count}
        , m_lo{nodep, width}
        , m_stride{nodep, width, 1}
        , m_hi{nodep, width} {}
};

//######################################################################
// Functional coverage visitor

class FunctionalCoverageVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //  AstCoverpoint::user1p()  -> AstVar*.  Previous-value variable for transition bins
    //  AstCoverpoint::user2()   -> bool.  Had a bins declaration ignored, so no automatic bins
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    std::set<AstCoverpoint*>
        m_runtimePoints;  // Points needing value metadata and live-bin mapping
    std::set<AstCoverCross*> m_runtimeCrosses;  // Crosses over finalized live-bin dimensions
    std::map<AstVar*, AstVar*> m_excludedVars;  // Sample-time state-exclusion flags
    AstClass* m_covergroupp = nullptr;  // Current covergroup being processed
    AstNodeModule* m_unitp = nullptr;  // Design unit declaring the current class, outside classes
    AstClass* m_enclosingClassp = nullptr;  // Class lexically enclosing the covergroup, if any
    AstVar* m_embeddedVarp = nullptr;  // Embedded covergroup member of m_enclosingClassp, if any
    std::string m_covergroupName;  // Current covergroup's type name, see covergroupTypeName()
    AstFunc* m_sampleFuncp = nullptr;  // Current sample() function
    AstIf* m_cpGuardp = nullptr;  // Current coverpoint's iff guard, holding its sampling
    AstFunc* m_constructorp = nullptr;  // Current constructor
    std::vector<AstCoverpoint*> m_coverpoints;  // Coverpoints in current covergroup
    std::map<std::string, AstCoverpoint*> m_coverpointMap;  // Name -> coverpoint for fast lookup
    std::vector<AstCoverCross*> m_coverCrosses;  // Cross coverage items in current covergroup
    std::vector<AstCgOptionAssign*> m_cgOptions;  // Covergroup-level options, before lowering
    uint32_t m_cgTypeWeight = 1;  // The covergroup's type_option.weight, a constant
    bool m_cgMergeInstances = false;  // The covergroup's type_option.merge_instances, a constant
    // The covergroup's type_option.merge_instances is, or SystemVerilog may make it, true
    bool m_cgMayMerge = false;
    // type_option members through which SystemVerilog may set type_option.merge_instances,
    // see CovergroupAssignValidVisitor::mergeableTypeOptions()
    const std::set<const AstVar*>& m_mergeableTypeOptions;

    struct EmbeddedEventTrigger final {
        FileLine* eventFl;  // Clocking-event source location
        AstVar* baseVarp;  // Base enclosing-class member in the event expression
        AstVar* memberVarp;  // Selected member in a 'base.member' expression, or nullptr
        VEdgeType edgeType;  // Clocking-event edge qualifier
        AstVar* prevVarp;  // Member containing the previous event value, or nullptr
        EmbeddedEventTrigger(FileLine* eventFl, AstVar* baseVarp, AstVar* memberVarp,
                             VEdgeType edgeType)
            : eventFl{eventFl}
            , baseVarp{baseVarp}
            , memberVarp{memberVarp}
            , edgeType{edgeType}
            , prevVarp{nullptr} {}
    };

    std::set<std::string> m_crossedCpNames;  // Coverpoints referenced by a cross
    std::map<std::string, AstVar*> m_cpVarMap;  // Coverpoint name -> its VlCoverpoint member
    struct BinRuns final {
        std::vector<BinRun> runs;  // Runs of an array or automatic bins declaration, in order
        uint32_t count = 0;  // Bins across all runs
        bool unsupported = false;  // Too many bins, or invalid: the declaration is ignored
        // The value of each bin, which names it, of a wildcard array; else the bins are indexed
        std::vector<std::string> values;
        // Too many values of an ignore or illegal wildcard array, which is then one bin
        bool single = false;
    };
    struct CrossBinValues final {
        AstCoverBin* binp;  // Declaration owning this Normal bin
        AstNodeExpr* valuep;  // Individual array-bin value, or nullptr for a scalar bin
        const BinRun* runp = nullptr;  // Run computing the bin's values, if any
        uint32_t element = 0;  // Index of the bin within runp
    };
    struct BinSpan final {
        uint32_t first = 0;  // First Normal index of the bin declaration
        uint32_t count = 0;  // Number of Normal bins of the declaration
        uint32_t declared = 0;  // First runtime bin index, across all bin kinds
        int32_t sized = -1;  // Index of the sized array, placed at construction; or -1
    };
    struct CoverpointBins final {
        uint32_t total = 0;  // Number of Normal bins
        AstNodeExpr* exprp = nullptr;  // Sampled expression, for the value domain
        bool crossed = false;  // Feeds a cross, which needs 'values'
        std::vector<CrossBinValues> values;  // Values in runtime Normal-bin index order
        std::unordered_map<std::string, BinSpan> spans;  // Declared bin name -> index span
        BinSpan implicitAuto{0, 0, 0};  // Implicit automatic bins, each named 'auto_<i>'
        std::deque<BinRun> runs;  // Runs 'values' refers to
    };
    std::map<AstVar*, CoverpointBins> m_cpBins;  // Runtime coverpoint -> binsof index ranges
    // Names of the bins declarations each coverpoint ignored, which binsof selects as no bins
    std::map<const AstCoverpoint*, std::vector<std::string>> m_droppedBins;
    // Prefixes of the constructor temporaries of constructed bins, as coverpoint and bin names
    // alone may repeat: coverpoint 'a_' bins 'b', and coverpoint 'a' bins '_b'
    V3UniqueNames m_sizedNames{"__Vsized"};
    std::vector<AstNodeExpr*> m_detachedValues;  // Array-bin values m_cpBins refers to
    std::set<AstCoverCross*>
        m_droppedCrosses;  // Crosses with a bare-variable item: drop (COVERIGN)
    std::map<uint32_t, AstCoverpointDType*> m_cpDTypes;  // Hit-list bound -> interned dtype
    using CrossShape = std::tuple<uint32_t, uint32_t, uint32_t, uint32_t, uint64_t, bool>;
    std::map<CrossShape, AstCoverCrossDType*> m_cxDTypes;
    AstVar* m_cgInstVarp = nullptr;  // __Vcg_inst handle member of the current covergroup

    VMemberMap m_memberMap;  // Member names cached for fast lookup

    // METHODS
    // The covergroup's 'option' or static 'type_option' member (V3LinkParse creates both)
    AstVar* optionVar(bool typeOption) {
        AstVar* const varp = VN_AS(
            m_memberMap.findMember(m_covergroupp, typeOption ? "type_option" : "option"), Var);
        UASSERT_OBJ(varp, m_covergroupp, "Covergroup missing option member");
        return varp;
    }

    // 'option.<member>' or 'type_option.<member>', per optionVarp
    AstStructSel* newOptionSel(FileLine* fl, AstVar* optionVarp, const std::string& member,
                               VAccess access) {
        const AstMemberDType* const memberp
            = VN_AS(m_memberMap.findMember(optionVarp->dtypep()->skipRefp(), member), MemberDType);
        UASSERT_OBJ(memberp, optionVarp, "Coverage option structure missing '" << member << "'");
        AstNodeExpr* const fromp = optionVarp->lifetime().isStatic()
                                       ? new AstVarRef{fl, optionVarp, access}
                                       : memberRef(fl, optionVarp, access);
        AstStructSel* const selp = new AstStructSel{fl, fromp, member};
        selp->dtypep(memberp->subDTypep()->skipRefToEnump());
        selp->didWidth(true);
        return selp;
    }

    // Store the covergroup-level options (IEEE 1800-2023 19.7) where SystemVerilog and the
    // runtime read them.  The instance options, option.weight and option.get_inst_coverage,
    // are evaluated by the constructor, as are the other instance options; the type options,
    // type_option.weight and type_option.merge_instances, are constant, and initialize the
    // static member.  Without its own type_option.merge_instances, a covergroup has the
    // default of --coverage-merge-instances.
    void lowerCovergroupOptions() {
        bool mergeSet = false;  // The covergroup sets type_option.merge_instances
        for (AstCgOptionAssign* const optp : m_cgOptions) {
            FileLine* const fl = optp->fileline();
            // V3Width left the type options constant, and type_option.weight non-negative
            const AstConst* const constp = VN_CAST(optp->valuep(), Const);
            std::string member = "weight";
            if (optp->optType() == VCoverOptionType::MERGE_INSTANCES) {
                member = "merge_instances";
                m_cgMergeInstances = !constp->num().isEqZero();
                mergeSet = true;
            } else if (optp->optType() == VCoverOptionType::GET_INST_COVERAGE) {
                member = "get_inst_coverage";
            } else {
                UASSERT_OBJ(optp->optType() == VCoverOptionType::WEIGHT, optp,
                            "Unexpected covergroup option reaching V3Covergroup");
                if (optp->typeOption()) m_cgTypeWeight = constp->toUInt();
            }
            AstAssign* const assignp = new AstAssign{
                fl, newOptionSel(fl, optionVar(optp->typeOption()), member, VAccess::WRITE),
                optp->valuep()->unlinkFrBack()};
            if (optp->typeOption()) {
                m_covergroupp->addMembersp(new AstInitialStatic{fl, assignp});
                VL_DO_DANGLING(pushDeletep(optp->unlinkFrBack()), optp);
            } else {
                optp->replaceWith(assignp);
                VL_DO_DANGLING(pushDeletep(optp), optp);
            }
        }
        m_cgOptions.clear();
        if (!mergeSet && v3Global.opt.coverageMergeInstances()) {
            FileLine* const fl = m_covergroupp->fileline();
            m_covergroupp->addMembersp(new AstInitialStatic{
                fl, new AstAssign{
                        fl, newOptionSel(fl, optionVar(true), "merge_instances", VAccess::WRITE),
                        new AstConst{fl, AstConst::BitTrue{}}}});
            m_cgMergeInstances = true;
        }
        m_cgMayMerge = m_cgMergeInstances || m_mergeableTypeOptions.count(optionVar(true));
    }

    // The weight of an item in the coverage database, which merges the instances: its
    // type_option.weight if the covergroup merges them too (IEEE 1800-2023 19.11.3); else its
    // option.weight if a constant, and so of every instance; else its type_option.weight
    uint32_t itemDatabaseWeight(AstNode* optionsp) const {
        const AstNodeExpr* weightp = nullptr;  // The option.weight in effect
        uint32_t typeWeight = 1;
        for (AstNode* nodep = optionsp; nodep; nodep = nodep->nextp()) {
            const AstCoverOption* const optp = VN_AS(nodep, CoverOption);
            if (!(optp->optType() == VCoverOptionType::WEIGHT)) continue;
            // V3Width left type_option.weight a non-negative constant
            if (optp->typeOption()) {
                typeWeight = VN_AS(optp->valuep(), Const)->toUInt();
            } else {
                weightp = optp->valuep();
            }
        }
        if (m_cgMergeInstances) return typeWeight;
        if (!weightp) return 1;
        if (const AstConst* const constp = VN_CAST(weightp, Const)) return constp->toUInt();
        return typeWeight;
    }

    // Configure an item's option.weight, its weight in instance coverage (IEEE 1800-2023
    // 19.11), and, if the covergroup may merge its instances, its type_option.weight, its
    // weight in type coverage then (19.11.3).
    void generateItemWeight(FileLine* fl, AstVar* itemVarp, AstNode* optionsp) {
        for (AstNode* nodep = optionsp; nodep; nodep = nodep->nextp()) {
            const AstCoverOption* const optp = VN_AS(nodep, CoverOption);
            if (!(optp->optType() == VCoverOptionType::WEIGHT)) continue;
            if (!optp->typeOption()) {
                m_constructorp->addStmtsp(
                    itemCall(fl, itemVarp, VCMethod::COVERGROUP_WEIGHT,
                             {optp->valuep()->cloneTree(false), fileLineDebug(optp->fileline())})
                        ->makeStmt());
            } else if (m_cgMayMerge) {
                // V3Width left type_option.weight a non-negative constant
                m_constructorp->addStmtsp(itemCall(fl, itemVarp, VCMethod::COVERGROUP_TYPE_WEIGHT,
                                                   {optp->valuep()->cloneTree(false)})
                                              ->makeStmt());
            }
        }
    }

    void processCovergroup() {
        UINFO(4, "Processing covergroup: " << m_covergroupp->name() << " with "
                                           << m_coverpoints.size() << " coverpoints and "
                                           << m_coverCrosses.size() << " crosses");

        m_crossedCpNames.clear();
        m_cpVarMap.clear();
        m_cpBins.clear();
        m_droppedBins.clear();
        m_sizedNames.reset();
        m_runtimePoints.clear();
        m_runtimeCrosses.clear();
        m_excludedVars.clear();
        m_droppedCrosses.clear();
        m_cgInstVarp = nullptr;
        m_cgTypeWeight = 1;
        m_cgMergeInstances = false;
        m_cgMayMerge = false;

        lowerCovergroupOptions();

        // Scan every cross item to record the coverpoints it references (the cross dimensions)
        // and to flag any cross naming a bare variable -- a would-be implicit coverpoint, which
        // Verilator does not synthesize.  An unresolvable item drops only that one cross (with a
        // COVERIGN in generateCrossCode), leaving the rest of the covergroup intact.
        for (AstCoverCross* crossp : m_coverCrosses) {
            for (AstNode* itemp = crossp->itemsp(); itemp; itemp = itemp->nextp()) {
                const AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
                if (refp->exprp()) continue;  // hierarchical ref: dropped in generateCrossCode
                if (m_coverpointMap.find(refp->name()) == m_coverpointMap.end()) {
                    m_droppedCrosses.insert(crossp);  // bare variable: drop this cross only
                } else {
                    m_crossedCpNames.insert(refp->name());
                }
            }
        }

        std::vector<AstNode*> pending;
        std::map<AstCoverpoint*, std::vector<AstCoverCross*>> consumers;
        std::map<AstCoverCross*, std::vector<AstCoverpoint*>> inputs;
        for (AstCoverpoint* const cpp : m_coverpoints) {
            checkBinNames(cpp);
            checkConstructedBins(cpp);
            if (!cpp->exprp()->dtypep()->skipRefp()->isIntegralOrPacked()) continue;
            // Bins without values leave the report (IEEE 1800-2023 19.11.1), exclusions or not.
            // Constructed bins get their values when the covergroup is constructed.
            if (!coverpointHasStateExclusions(cpp) && !coverpointHasEmptyBins(cpp)
                && !coverpointHasConstructedBins(cpp)) {
                continue;
            }
            m_runtimePoints.insert(cpp);
            pending.push_back(cpp);
        }
        for (AstCoverCross* const crossp : m_coverCrosses) {
            if (m_droppedCrosses.count(crossp)) continue;
            for (AstNode* itemp = crossp->itemsp(); itemp; itemp = itemp->nextp()) {
                const AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
                if (refp->exprp()) continue;
                const auto point = m_coverpointMap.find(refp->name());
                if (point != m_coverpointMap.end()) {
                    consumers[point->second].push_back(crossp);
                    inputs[crossp].push_back(point->second);
                }
            }
        }
        for (size_t next = 0; next < pending.size(); ++next) {
            if (AstCoverpoint* const pointp = VN_CAST(pending[next], Coverpoint)) {
                for (AstCoverCross* const crossp : consumers[pointp]) {
                    if (m_runtimeCrosses.emplace(crossp).second) pending.push_back(crossp);
                }
            } else {
                for (AstCoverpoint* const pointp : inputs[VN_AS(pending[next], CoverCross)]) {
                    if (pointp->exprp()->dtypep()->skipRefp()->isIntegralOrPacked()
                        && m_runtimePoints.emplace(pointp).second) {
                        pending.push_back(pointp);
                    }
                }
            }
        }

        // The instance node owns this instance's coverpoint/cross runtimes, so it must exist
        // before any of them is created.  Emitted first, ahead of both generate loops.
        generateInstanceAttach();

        // For each coverpoint, generate sampling code
        for (AstCoverpoint* cpp : m_coverpoints) generateCoverpointCode(cpp);

        // For each cross, generate sampling code
        for (AstCoverCross* crossp : m_coverCrosses) generateCrossCode(crossp);

        // Every cross has been built, so runtime points only need their exclusions from here.
        for (AstCoverpoint* const cpp : m_coverpoints) {
            if (!m_runtimePoints.count(cpp)) continue;
            m_constructorp->addStmtsp(itemCall(cpp->fileline(), m_cpVarMap.at(cpp->name()),
                                               VCMethod::COVERGROUP_VALUE_RELEASE)
                                          ->makeStmt());
        }
        for (AstNodeExpr* valuep : m_detachedValues) VL_DO_DANGLING(pushDeletep(valuep), valuep);
        m_detachedValues.clear();

        // Generate coverage computation code (even for empty covergroups).  Bin registration
        // with the coverage database is handled per coverpoint/cross by their runtime
        // registerBins() calls (emitted in generateCoverpoint/generateCross).
        generateCoverageComputationCode();
    }

    static constexpr size_t VALUE_LIST_ENTRIES = 256;  // Metadata entries per constructor call

    // The number of bins a constant array size requests: -1 if it is negative, and saturated
    // above the largest limit
    static int64_t binsCount(const AstConst* constp) {
        const V3Number& num = constp->num();
        if (constp->isSigned() && num.isNegative()) return -1;
        return num.mostSetBitP1() > 32 ? INT64_MAX : static_cast<int64_t>(num.toUQuad());
    }

    // The number of bins requested by a valid 'bins auto[N]', or 0
    static uint32_t autoBinsRequested(const AstCoverBin* binp) {
        const AstConst* const constp = VN_CAST(binp->arraySizep(), Const);
        if (!constp) return 0;
        const int64_t count = binsCount(constp);
        return count < 1 || count > v3Global.opt.coverageMaxBins() ? 0
                                                                   : static_cast<uint32_t>(count);
    }

    // True for a 'bins auto[N]' declaration, or the implicit automatic bins of a coverpoint
    static bool isAutoBins(const AstCoverBin* binp) {
        return binp->binsType() == VCoverBinsType::BINS_AUTO
               || binp->binsType() == VCoverBinsType::BINS_AUTO_IMPLICIT;
    }

    // True for a sized array of bins, 'bins b[N] = {...}', whose values an integral coverpoint
    // distributes over N bins when the covergroup is constructed (IEEE 1800-2023 19.5.1)
    static bool isSizedArray(const AstCoverBin* binp) {
        return binp->arraySizep() && !isAutoBins(binp);
    }

    // The 'with' filter of a bin, if any (IEEE 1800-2023 19.5.1.1)
    static AstCoverWith* binWith(const AstCoverBin* binp) {
        return VN_CAST(binp->rangesp(), CoverWith);
    }

    // True for bins whose values the covergroup constructor computes: a sized array, or bins of
    // the values a 'with' filter keeps
    static bool isConstructedBins(const AstCoverBin* binp) {
        return isSizedArray(binp) || binWith(binp);
    }

    // The range list of a bin's values, or of the candidates of its 'with' filter; null for all
    // of the coverpoint's values, which a filter of the coverpoint's name has
    static AstNode* binRangesp(const AstCoverBin* binp) {
        const AstCoverWith* const withp = binWith(binp);
        if (!withp) return binp->rangesp();
        return VN_IS(withp->subp(), CoverpointRef) ? nullptr : withp->subp();
    }

    // Report and delete a bins declaration of a name that another of its coverpoint has
    void checkBinNames(AstCoverpoint* coverpointp) {
        std::set<std::string> names;
        for (AstNode* nodep = coverpointp->binsp(); nodep;) {
            AstCoverBin* const binp = VN_AS(nodep, CoverBin);
            nodep = nodep->nextp();
            if (names.emplace(binp->name()).second) continue;
            binp->v3error("Duplicate bin " << binp->prettyNameQ() << " in coverpoint "
                                           << coverpointp->prettyNameQ()
                                           << " (IEEE 1800-2023 3.13)");
            VL_DO_DANGLING(pushDeletep(binp->unlinkFrBack()), binp);
        }
    }

    // Delete an ignored bins declaration, which binsof then selects as no bins
    void dropBins(const AstCoverpoint* coverpointp, AstCoverBin* binp) {
        m_droppedBins[coverpointp].push_back(binp->name());
        VL_DO_DANGLING(pushDeletep(binp->unlinkFrBack()), binp);
    }

    // Check the size of a sized array of bins, which drops an invalid array.  A real coverpoint's
    // are unsupported, and treated as arrays of a bin per value.  False unless it stays sized.
    bool checkBinsArraySize(const AstCoverpoint* coverpointp, AstCoverBin* binp, bool integral) {
        AstNodeExpr* const sizep = binp->arraySizep();
        const AstConst* const constp = VN_CAST(sizep, Const);
        if (VN_IS(sizep, Unbounded)) {  // A parameter of '$'; see bins_orBraE
            binp->v3error("Bins array size must be integral, not '$' (IEEE 1800-2023 19.5.1)");
        } else if (!sizep->dtypep()->skipRefp()->isIntegralOrPacked()) {
            sizep->v3error("Bins array size must be integral (IEEE 1800-2023 19.5.1)");
        } else if (constp && (constp->num().isFourState() || binsCount(constp) < 1)) {
            sizep->v3error("Bins array size must be >= 1, got "
                           << (constp->num().isFourState() ? constp->num().ascii(false)
                                                           : constp->num().toDecimalS())
                           << " (IEEE 1800-2023 19.5.1)");
        } else if (!integral) {
            binp->v3warn(COVERIGN, "Unsupported: 'bins' explicit array size of a real "
                                   "coverpoint (treated as '[]')");
            VL_DO_DANGLING(pushDeletep(sizep->unlinkFrBack()), sizep);
            return false;
        } else {
            return true;
        }
        dropBins(coverpointp, binp);
        return false;
    }

    // Check the bins of a coverpoint whose values the constructor computes, dropping invalid
    // ones.  A wildcard array of too many ranges of values is ignored, or if ignore or illegal,
    // treated as one bin; filtering too many ranges of values ignores the bins.
    void checkConstructedBins(AstCoverpoint* coverpointp) {
        const bool integral = coverpointp->exprp()->dtypep()->skipRefp()->isIntegralOrPacked();
        for (AstNode* nodep = coverpointp->binsp(); nodep;) {
            AstCoverBin* const binp = VN_AS(nodep, CoverBin);
            nodep = nodep->nextp();
            if (!isConstructedBins(binp)) continue;
            if (isSizedArray(binp) && !checkBinsArraySize(coverpointp, binp, integral)) continue;
            if (!binp->isWildcard()
                || sizedWildcardRuns(binp, coverpointp->exprp())
                       <= v3Global.opt.coverageMaxBins()) {
                if (binWith(binp) && withCandidatesOver(binp, coverpointp->exprp())) {
                    binp->v3warn(COVERIGN, "Unsupported: 'with' filter of more than 2**32 "
                                           "candidate values; bin "
                                               << binp->prettyNameQ() << " ignored");
                    if (binp->binsType().binIsNormal()) coverpointp->user2(true);
                    dropBins(coverpointp, binp);
                }
                continue;
            }
            // An ignore or illegal array still excludes or checks its values, as one bin
            const bool single = !binp->binsType().binIsNormal() && !binWith(binp);
            binp->v3warn(COVERIGN,
                         "Unsupported: " << (binWith(binp) ? "'with' filter of wildcard '"
                                                           : "sized wildcard array '")
                                         << binp->binsType().verilogKwd()
                                         << "' of more than --coverage-max-bins of "
                                         << v3Global.opt.coverageMaxBins()
                                         << " ranges of values; bin " << binp->prettyNameQ()
                                         << (single ? " treated as one bin" : " ignored") << "\n"
                                         << binp->warnMore()
                                         << "... Suggest a larger --coverage-max-bins");
            if (single) {
                AstNodeExpr* const sizep = binp->arraySizep();
                VL_DO_DANGLING(pushDeletep(sizep->unlinkFrBack()), sizep);
                binp->isArray(false);
                continue;
            }
            if (binp->binsType().binIsNormal()) coverpointp->user2(true);
            dropBins(coverpointp, binp);
        }
    }

    // True if a 'with' filter would be evaluated for more than 2**32 candidate values, known
    // now for the coverpoint's name, or for a range list of constants: each is evaluated once
    // but for an array 'b[N]', which keeps their order and duplicates (see withBegin())
    static bool withCandidatesOver(AstCoverBin* binp, AstNodeExpr* exprp) {
        const int width = runWidth(exprp);
        std::vector<std::pair<V3Number, V3Number>> runs;
        if (!binRangesp(binp)) runs = coverpointValues(binp, exprp);
        const auto constant
            = [](const AstNode* nodep) { return VN_IS(nodep, Const) || VN_IS(nodep, Unbounded); };
        for (AstNode* rangep = binRangesp(binp); rangep; rangep = rangep->nextp()) {
            const AstInsideRange* const irp = VN_CAST(rangep, InsideRange);
            // Else known when constructed
            if (irp ? !constant(irp->lhsp()) || !constant(irp->rhsp()) : !VN_IS(rangep, Const)) {
                return false;
            }
            CrossValueRange range{rangep, resolveWidth(rangep, exprp)};
            if (!resolveValue(rangep, exprp, true, binp->isWildcard(), range)
                || crossRangeEmpty(range)) {
                continue;
            }
            std::vector<std::pair<V3Number, V3Number>> found{{range.lo, range.hi}};
            if (range.wildcard) {  // checkConstructedBins bounded the runs
                found.clear();
                crossRangeRuns(range, v3Global.opt.coverageMaxBins(), found);
            }
            for (const std::pair<V3Number, V3Number>& run : found) {
                runs.emplace_back(V3Number{rangep, width, run.first},
                                  V3Number{rangep, width, run.second});
            }
        }
        if (!isSizedArray(binp)) {  // The union of the values
            std::sort(runs.begin(), runs.end(), [](const auto& lhs, const auto& rhs) {
                return crossValueLess(lhs.first, rhs.first);
            });
            std::vector<std::pair<V3Number, V3Number>> merged;
            for (const std::pair<V3Number, V3Number>& run : runs) {
                if (merged.empty() || crossValueLess(merged.back().second, run.first)) {
                    merged.push_back(run);
                } else if (crossValueLess(merged.back().second, run.second)) {
                    merged.back().second = run.second;
                }
            }
            runs = std::move(merged);
        }
        uint64_t count = 0;
        for (const std::pair<V3Number, V3Number>& run : runs) {
            V3Number span{exprp, width};
            span.opSub(run.second, run.first);
            if (span.mostSetBitP1() > 32) return true;  // More than 2**32 values
            count += span.toUQuad() + 1;
            if (count > (uint64_t{1} << 32)) return true;
        }
        return false;
    }

    // The ranges of values the wildcard patterns of a sized wildcard array, or of a 'with'
    // filter's candidates, give, counted up to more than --coverage-max-bins
    static size_t sizedWildcardRuns(const AstCoverBin* binp, AstNodeExpr* exprp) {
        std::vector<std::pair<V3Number, V3Number>> runs;
        for (AstNode* rangep = binRangesp(binp); rangep; rangep = rangep->nextp()) {
            if (!VN_IS(rangep, Const)) continue;  // A range, or a value known at construction
            CrossValueRange range{rangep, resolveWidth(rangep, exprp)};
            if (resolveValue(rangep, exprp, true, true, range) && !crossRangeEmpty(range)) {
                crossRangeRuns(range, v3Global.opt.coverageMaxBins(), runs);
            }
        }
        return runs.size();
    }

    // Check the automatic bins declarations of a coverpoint.  Each stays one declaration, which
    // generates as a partition of the coverpoint domain (see autoBinRuns).
    void checkAutomaticBins(AstCoverpoint* coverpointp, const AstNodeExpr* exprp) {
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            if (cbinp->binsType() != VCoverBinsType::BINS_AUTO) continue;
            const AstConst* const constp = VN_CAST(cbinp->arraySizep(), Const);
            if (!constp) {
                cbinp->v3error("Automatic bins array size must be a constant");
            } else if (binsCount(constp) < 1) {
                cbinp->v3error("Automatic bins array size must be >= 1, got "
                               << constp->num().toDecimalS());
            } else if (binsCount(constp) > v3Global.opt.coverageMaxBins()) {
                cbinp->v3error("Automatic bins array size of "
                               << constp->num().toDecimalU() << " exceeds limit of "
                               << v3Global.opt.coverageMaxBins() << '\n'
                               << cbinp->warnMore() << "... Suggest a larger --coverage-max-bins");
            } else if (!exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
                cbinp->v3error("Automatic bins are not allowed on a coverpoint of a non-integral "
                               "expression (IEEE 1800-2023 19.5.3).");
            }
        }
    }

    // Extract all coverpoint option values in a single pass.
    // atLeastOut: option.at_least (default 1)
    // autoBinMaxOut: option.auto_bin_max (coverpoint overrides covergroup, default 64)
    void extractCoverpointOptions(AstCoverpoint* coverpointp, int& atLeastOut,
                                  int& autoBinMaxOut) {
        atLeastOut = 1;
        autoBinMaxOut = -1;  // -1 = not set at coverpoint level
        for (AstNode* optionp = coverpointp->optionsp(); optionp; optionp = optionp->nextp()) {
            AstCoverOption* const optp = VN_AS(optionp, CoverOption);
            // Weights may be non-constant; generateItemWeight() handles them
            if (optp->optType() == VCoverOptionType::WEIGHT) continue;
            AstConst* const constp = VN_CAST(optp->valuep(), Const);
            if (!constp) {
                optp->valuep()->v3warn(COVERIGN, "Ignoring unsupported: non-constant 'option."
                                                     << optp->optType().ascii()
                                                     << "'; using default value");
                continue;
            }
            if (optp->optType() == VCoverOptionType::AT_LEAST) {
                atLeastOut = constp->toSInt();
            } else {
                // V3LinkParse only converts at_least/auto_bin_max/weight coverpoint options
                // into AstCoverOption (others are dropped there), so this is the only
                // alternative.
                UASSERT_OBJ(optp->optType() == VCoverOptionType::AUTO_BIN_MAX, optp,
                            "Unexpected coverpoint option type reaching V3Covergroup");
                autoBinMaxOut = constp->toSInt();
            }
        }
        // Fall back to covergroup-level auto_bin_max if not set at coverpoint level
        if (autoBinMaxOut < 0) {
            if (m_covergroupp->cgAutoBinMax() >= 0) {
                autoBinMaxOut = m_covergroupp->cgAutoBinMax();
            } else {
                autoBinMaxOut = 64;  // Default per IEEE 1800-2023 Table 19-1
            }
        }
    }

    // IEEE 1800-2023 19.5.2: an enum coverpoint has one automatic bin per enumeration value
    void createEnumAutoBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp,
                            const AstEnumDType* enump) {
        FileLine* const fl = coverpointp->fileline();
        for (const AstEnumItem* itemp = enump->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            AstConst* const lop = newValueConst(fl, VN_AS(itemp->valuep(), Const)->num(), exprp);
            AstInsideRange* const rangep = new AstInsideRange{fl, lop, lop->cloneTree(false)};
            rangep->dtypeFrom(exprp);
            coverpointp->addBinsp(
                new AstCoverBin{fl, "auto[" + itemp->name() + "]", rangep, false, false});
        }
    }

    // IEEE 1800-2023 19.5.3/19.11.1: partition first, then apply exclusions.  The partition is one
    // automatic bins declaration, generated as a run like 'bins auto[N]' but numbering its bins.
    void createImplicitAutoBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp, int autoBinMax) {
        if (coverpointp->user2()) return;  // Declared bins, ignored, leave no bins
        for (AstNode* nodep = coverpointp->binsp(); nodep; nodep = nodep->nextp()) {
            const VCoverBinsType kind = VN_AS(nodep, CoverBin)->binsType();
            if (kind != VCoverBinsType::BINS_IGNORE && kind != VCoverBinsType::BINS_ILLEGAL)
                return;
        }
        if (const AstEnumDType* const enump
            = VN_CAST(exprp->dtypep()->skipRefToEnump(), EnumDType)) {
            createEnumAutoBins(coverpointp, exprp, enump);
            return;
        }
        const int width = exprp->width();
        uint32_t count = width < 31 ? std::min<uint32_t>(uint32_t{1} << width, autoBinMax)
                                    : static_cast<uint32_t>(autoBinMax);
        if (!count) return;
        if (!exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
            coverpointp->v3error("Coverpoint of a non-integral expression requires explicit bins "
                                 "(IEEE 1800-2023 19.5.3).");
            return;
        }
        if (count > v3Global.opt.coverageMaxBins()) {
            coverpointp->v3warn(COVERIGN, "Unsupported: more than "
                                              << v3Global.opt.coverageMaxBins()
                                              << " automatic bins from 'option.auto_bin_max'; "
                                                 "using "
                                              << v3Global.opt.coverageMaxBins() << ".\n"
                                              << coverpointp->warnMore()
                                              << "... Suggest a larger --coverage-max-bins");
            count = v3Global.opt.coverageMaxBins();
        }
        FileLine* const fl = coverpointp->fileline();
        coverpointp->addBinsp(new AstCoverBin{fl, "auto", new AstConst{fl, count},
                                              VCoverBinsType::BINS_AUTO_IMPLICIT});
    }

    // Sanitize generated names to be valid C++ identifiers
    static string sanitizeGeneratedName(string name) {
        std::replace(name.begin(), name.end(), '[', '_');
        std::replace(name.begin(), name.end(), ']', '_');
        return name;
    }

    // Capture an iff guard in a function-local temporary so it is evaluated once per sample()
    AstVarRef* captureIffToTemp(AstNodeExpr* iffp, const string& tempName) {
        FileLine* const fl = iffp->fileline();
        AstVar* const iffVarp
            = new AstVar{fl, VVarType::BLOCKTEMP, tempName, iffp->findBitDType()};
        iffVarp->funcLocal(true);
        m_sampleFuncp->addStmtsp(iffVarp);
        iffp->unlinkFrBack();
        m_sampleFuncp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, iffVarp, VAccess::WRITE}, iffp});
        return new AstVarRef{fl, iffVarp, VAccess::READ};
    }

    // Add a statement sampling the current coverpoint to sample(), under its iff guard if any
    void addSampleStmt(AstNode* stmtp) {
        if (m_cpGuardp) {
            m_cpGuardp->addThensp(stmtp);
        } else {
            m_sampleFuncp->addStmtsp(stmtp);
        }
    }

    // Create previous value variable for transition tracking
    AstVar* createPrevValueVar(AstCoverpoint* coverpointp, AstNodeExpr* exprp) {
        // Check if already created
        if (AstVar* const prevVarp = VN_CAST(coverpointp->user1p(), Var)) return prevVarp;

        // Create variable to store previous sampled value
        const string varName = "__Vprev_" + coverpointp->name();
        AstVar* prevVarp
            = new AstVar{coverpointp->fileline(), VVarType::MEMBER, varName, exprp->dtypep()};
        m_covergroupp->addMembersp(prevVarp);

        UINFO(4, "    Created previous value variable: " << varName);

        // Initialize to zero in constructor
        AstNodeExpr* const initExprp
            = new AstConst{prevVarp->fileline(), AstConst::WidthedValue{}, prevVarp->width(), 0};
        AstNodeStmt* const initStmtp = new AstAssign{
            prevVarp->fileline(), new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::WRITE},
            initExprp};
        m_constructorp->addStmtsp(initStmtp);

        coverpointp->user1p(prevVarp);
        return prevVarp;
    }

    // Create state position variable for multi-value transition bins
    // Tracks position in sequence: 0=not started, 1=seen first item, etc.
    AstVar* createSequenceStateVar(AstCoverpoint* coverpointp, AstCoverBin* binp) {
        // Create variable to track sequence position
        const string varName = "__Vseqpos_" + coverpointp->name() + "_" + binp->name();
        // Use 8-bit integer for state position (sequences rarely > 255 items)
        AstVar* stateVarp
            = new AstVar{binp->fileline(), VVarType::MEMBER, varName, VFlagLogicPacked{}, 8};
        m_covergroupp->addMembersp(stateVarp);

        UINFO(4, "    Created sequence state variable: " << varName);

        // Initialize to 0 (not started) in constructor
        AstNodeStmt* const initStmtp = new AstAssign{
            stateVarp->fileline(), new AstVarRef{stateVarp->fileline(), stateVarp, VAccess::WRITE},
            new AstConst{stateVarp->fileline(), AstConst::WidthedValue{}, 8, 0}};
        m_constructorp->addStmtsp(initStmtp);

        return stateVarp;
    }

    void generateCoverpointCode(AstCoverpoint* coverpointp) {
        UINFO(4, "  Generating code for coverpoint: " << coverpointp->name());

        // Get the coverpoint expression
        AstNodeExpr* exprp = coverpointp->exprp();

        // Check automatic bins before processing
        checkAutomaticBins(coverpointp, exprp);

        // Extract all coverpoint options in a single pass
        int atLeastValue;
        int autoBinMax;
        extractCoverpointOptions(coverpointp, atLeastValue, autoBinMax);
        UINFO(6, "    Coverpoint at_least = " << atLeastValue << " auto_bin_max = " << autoBinMax);

        // Create implicit automatic bins if no regular bins exist
        createImplicitAutoBins(coverpointp, exprp, autoBinMax);

        // A false iff guard disables sampling of the coverpoint (IEEE 1800-2023 19.5), so
        // neither is its expression evaluated, nor are its bins or transition state updated
        VL_RESTORER(m_cpGuardp);
        if (AstNodeExpr* const iffp = coverpointp->iffp()) {
            m_cpGuardp = new AstIf{iffp->fileline(), iffp->unlinkFrBack()};
        }

        AstVar* const valueVarp = new AstVar{
            coverpointp->fileline(), VVarType::BLOCKTEMP,
            "__VcpValue_" + sanitizeGeneratedName(coverpointp->name()), exprp->dtypep()};
        valueVarp->funcLocal(true);
        m_sampleFuncp->addStmtsp(valueVarp);
        exprp->unlinkFrBack();
        addSampleStmt(new AstAssign{
            coverpointp->fileline(),
            new AstVarRef{coverpointp->fileline(), valueVarp, VAccess::WRITE}, exprp});
        coverpointp->exprp(new AstVarRef{coverpointp->fileline(), valueVarp, VAccess::READ});
        exprp = coverpointp->exprp();

        // Every coverpoint routes through the VlCoverpoint runtime.  Transition coverpoints are
        // included: their per-value matching is still generated as a state machine in sample()
        // (see generateCoverpoint), but the bin hit is recorded in the runtime bin
        // rather than a bare counter.
        generateCoverpoint(coverpointp, exprp, atLeastValue);
        // Sampling follows what generateCoverpoint added unguarded, such as clearing the hit list
        if (m_cpGuardp) m_sampleFuncp->addStmtsp(m_cpGuardp);
    }

    // Build the condition under which a default bin matches: NOT(OR of all normal bins).
    AstNodeExpr* buildDefaultCondition(AstCoverpoint* coverpointp, AstNodeExpr* exprp,
                                       FileLine* fl) {
        AstNodeExpr* anyBinMatchp = nullptr;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            if (cbinp->binsType() == VCoverBinsType::BINS_DEFAULT
                || cbinp->binsType() == VCoverBinsType::BINS_IGNORE
                || cbinp->binsType() == VCoverBinsType::BINS_ILLEGAL)
                continue;
            // The values of constructed bins are known at construction; see emitSizedSample
            if (isConstructedBins(cbinp)) continue;
            if (isAutoBins(cbinp)) {
                // Automatic bins partition the whole domain, leaving no default value
                if (anyBinMatchp) VL_DO_DANGLING(pushDeletep(anyBinMatchp), anyBinMatchp);
                return new AstConst{fl, AstConst::BitFalse{}};
            }
            AstNodeExpr* const binCondp = buildBinCondition(cbinp, exprp);
            UASSERT_OBJ(binCondp, cbinp,
                        "buildBinCondition returned nullptr for non-ignore/non-illegal bin");
            anyBinMatchp = anyBinMatchp ? new AstOr{fl, anyBinMatchp, binCondp} : binCondp;
        }
        return anyBinMatchp ? static_cast<AstNodeExpr*>(new AstNot{fl, anyBinMatchp})
                            : static_cast<AstNodeExpr*>(new AstConst{fl, AstConst::BitTrue{}});
    }

    //====================================================================
    // VlCoverpoint conversion

    static bool coverpointHasStateExclusions(const AstCoverpoint* coverpointp) {
        for (const AstNode* nodep = coverpointp->binsp(); nodep; nodep = nodep->nextp()) {
            const AstCoverBin* const binp = VN_AS(nodep, CoverBin);
            if (!binp->transp() && binp->rangesp()
                && (binp->binsType() == VCoverBinsType::BINS_IGNORE
                    || binp->binsType() == VCoverBinsType::BINS_ILLEGAL)) {
                return true;
            }
        }
        return false;
    }

    static bool coverpointHasConstructedBins(const AstCoverpoint* coverpointp) {
        for (const AstNode* nodep = coverpointp->binsp(); nodep; nodep = nodep->nextp()) {
            if (isConstructedBins(VN_AS(nodep, CoverBin))) return true;
        }
        return false;
    }

    // True if a Normal state bin, or an array-bin element, has no value of the coverpoint's
    // type (IEEE 1800-2023 19.5.7).  Array ranges enumerate in-type values, so cannot vanish.
    static bool coverpointHasEmptyBins(const AstCoverpoint* coverpointp) {
        AstNodeExpr* const exprp = coverpointp->exprp();
        for (AstNode* nodep = coverpointp->binsp(); nodep; nodep = nodep->nextp()) {
            const AstCoverBin* const binp = VN_AS(nodep, CoverBin);
            if (!binp->binsType().binIsNormal() || binp->transp() || !binp->rangesp()) continue;
            // A wildcard array has a bin for each value its elements match, so none empty, and
            // the constructor creates no bin without values of a 'with' filter
            if ((binp->isArray() && binp->isWildcard()) || binWith(binp)) continue;
            bool empty = true;
            for (AstNode* valuep = binp->rangesp(); valuep; valuep = valuep->nextp()) {
                if (binp->isArray() && VN_IS(valuep, InsideRange)) continue;
                CrossValueRange range{valuep, resolveWidth(valuep, exprp)};
                const bool none = resolveValue(valuep, exprp, true, binp->isWildcard(), range)
                                  && crossRangeEmpty(range);
                if (binp->isArray() && none) return true;
                empty &= none;
            }
            if (empty && !binp->isArray()) return true;
        }
        return false;
    }

    // True if a coverpoint has any transition bin.  Used to decide whether sample() emits the
    // end-of-sample previous-value update that transition matching needs.
    static bool coverpointHasTransition(AstCoverpoint* coverpointp) {
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            if (VN_AS(binp, CoverBin)->transp()) return true;
        }
        return false;
    }

    // The interned AstBasicDType for one of the covergroup runtime keywords.
    static AstBasicDType* basicDType(FileLine* fl, VBasicDTypeKwd kwd) {
        return v3Global.rootp()->typeTablep()->findBasicDType(fl, kwd);
    }

    // Get (or create) the coverpoint dtype for a hit-list bound, interned so each distinct bound
    // yields one node.
    AstCoverpointDType* coverpointDType(FileLine* fl, uint32_t hitBound) {
        AstCoverpointDType*& typep = m_cpDTypes[hitBound];
        if (!typep) {
            typep = new AstCoverpointDType{fl, hitBound};
            v3Global.rootp()->typeTablep()->addTypesp(typep);
        }
        return typep;
    }

    // The key of the covergroup's type in the coverage registry, which get_coverage() queries
    std::string covergroupProtectedName() const {
        return VIdProtect::protectWordsIf(m_covergroupName, v3Global.opt.protectIds());
    }

    // The name of the covergroup's type, which keys the coverage registry and database: as
    // $typename names it (IEEE 1800-2023 20.6.1), so apart for covergroups of distinct scopes and
    // specializations, and alike in each Verilator run of a hierarchical design.  As design units
    // of distinct libraries may share a name, one of a library other than the default is prefixed
    // by its library, as '%l' prints it (IEEE 1800-2023 33.4).
    std::string covergroupTypeName() const {
        UASSERT_OBJ(m_unitp, m_covergroupp, "Covergroup declared outside of a design unit");
        const std::string& libname = m_unitp->libname();
        const std::string name = m_covergroupp->dtypeName(true);
        return libname == "work" ? name : libname + "." + name;
    }

    // Emit the covergroup's instance handle member and the constructor statement that creates
    // its node in the per-context coverage registry.  Runs before any coverpoint or cross is
    // generated, so their runtimes can be added to the node as they are created.
    void generateInstanceAttach() {
        FileLine* const fl = m_covergroupp->fileline();
        // V3LinkParse synthesizes a 'new' for every covergroup; the item generators below already
        // rely on that, and this attach runs even for a covergroup with no coverpoints at all.
        UASSERT_OBJ(m_constructorp, m_covergroupp, "Covergroup missing synthesized constructor");
        m_cgInstVarp = new AstVar{fl, VVarType::MEMBER, "__Vcg_inst",
                                  basicDType(fl, VBasicDTypeKwd::COVERGROUP_INSTHANDLE)};
        m_covergroupp->addMembersp(m_cgInstVarp);

        m_constructorp->addStmtsp(
            itemCall(fl, m_cgInstVarp, VCMethod::COVERGROUP_ATTACH,
                     {ctext(fl, "vlSymsp->_vm_contextp__->covergroupRegistryp()"
                                "->newCovergroupInst("
                                    + quoted(covergroupProtectedName())
                                    + (m_cgMayMerge ? ", true" : ", false") + ")")},
                     /*usePtr=*/false)
                ->makeStmt());
        // The node reads option.weight in place, so procedural assignments take effect
        AstCExpr* const weightAddrp = new AstCExpr{fl, "&"};
        weightAddrp->add(newOptionSel(fl, optionVar(false), "weight", VAccess::READ));
        m_constructorp->addStmtsp(itemCall(fl, m_cgInstVarp, VCMethod::COVERGROUP_LEND_WEIGHT,
                                           {weightAddrp, fileLineDebug(fl)}, /*usePtr=*/false)
                                      ->makeStmt());
    }

    // A '__Vcg_inst.p()-><method>()' call on the covergroup's instance node
    AstCMethodHard* instanceCall(FileLine* fl, VCMethod method) {
        // '__Vcg_inst.p()' -- a value handle, so '.' not '->'
        AstCMethodHard* const instp
            = new AstCMethodHard{fl, memberRef(fl, m_cgInstVarp), VCMethod::COVERGROUP_INST_P};
        instp->usePtr(false);
        instp->dtypeSetVoid();  // Opaque receiver; only ever the 'fromp' of the call below
        AstCMethodHard* const callp = new AstCMethodHard{fl, instp, method};
        callp->usePtr(true);
        return callp;
    }

    // Emit 'this->__Vcp_x = this->__Vcg_inst.p()->addCoverpoint<K>();' (or addCross), which
    // creates the item runtime in the instance node and borrows a pointer to it.
    AstAssign* makeItemCreate(FileLine* fl, AstVar* itemVarp, VCMethod method) {
        AstCMethodHard* const createp = instanceCall(fl, method);
        createp->dtypep(itemVarp->dtypep());
        return new AstAssign{fl, memberRef(fl, itemVarp, VAccess::WRITE), createp};
    }

    // Constant bounds of one rangesp() element (an InsideRange or a single Const).  Each bound is
    // the raw AST node -- an AstConst or an AstUnbounded ('$') -- with the const/unbounded view
    // derived on demand, so there is one source of truth per bound.  After a successful
    // constRangeBounds() neither node is null; a single Const has both bounds aliasing one node.
    struct RangeBounds final {
        AstNode* loNodep = nullptr;  // low bound: AstConst or AstUnbounded
        AstNode* hiNodep = nullptr;  // high bound: AstConst or AstUnbounded
        bool loUnbounded() const { return VN_IS(loNodep, Unbounded); }
        bool hiUnbounded() const { return VN_IS(hiNodep, Unbounded); }
        AstConst* loConstp() const { return VN_CAST(loNodep, Const); }
        AstConst* hiConstp() const { return VN_CAST(hiNodep, Const); }
    };

    // Decode one rangesp() element into its constant bounds.  Returns false if rp is neither an
    // InsideRange nor a single Const, or if a present bound is non-constant or 4-state.  '$'
    // bounds are left as AstUnbounded (not resolved) -- the caller applies its own policy.
    // Centralizes the InsideRange/Const/Unbounded decode shared by the hit-list-bound paths.
    static bool constRangeBounds(AstNode* rp, RangeBounds& rb) {
        if (AstInsideRange* const irp = VN_CAST(rp, InsideRange)) {
            rb.loNodep = irp->lhsp();
            rb.hiNodep = irp->rhsp();
        } else if (AstConst* const cp = VN_CAST(rp, Const)) {
            rb.loNodep = rb.hiNodep = cp;
        } else {
            return false;
        }
        // Each bound must be a constant unless it is '$'; reject non-const and 4-state.
        AstConst* const lc = rb.loConstp();
        AstConst* const hc = rb.hiConstp();
        if ((!lc && !rb.loUnbounded()) || (!hc && !rb.hiUnbounded())) return false;
        if ((lc && lc->num().isFourState()) || (hc && hc->num().isFourState())) return false;
        return true;
    }

    // Collect the covered value intervals of a single (non-array) Normal bin.  Returns false
    // if any range isn't a constant/open InsideRange or single Const (e.g. wildcard, non-const).
    static bool extractRangeIntervals(AstCoverBin* cbinp, uint64_t maxVal,
                                      std::vector<std::pair<uint64_t, uint64_t>>& out) {
        if (!cbinp->rangesp()) return false;
        for (AstNode* rp = cbinp->rangesp(); rp; rp = rp->nextp()) {
            RangeBounds rb;
            if (!constRangeBounds(rp, rb)) return false;
            if ((rb.loConstp() && rb.loConstp()->width() > 64)
                || (rb.hiConstp() && rb.hiConstp()->width() > 64)) {
                return false;  // Use the safe slot-count bound for wide values.
            }
            const uint64_t lo = rb.loUnbounded() ? 0 : rb.loConstp()->toUQuad();
            const uint64_t hi = rb.hiUnbounded() ? maxVal : rb.hiConstp()->toUQuad();
            if (lo > hi) return false;
            out.emplace_back(lo, hi);
        }
        return true;
    }

    // Append one Normal bin's cross-slot interval-sets to `bins` and bump `slotCount` by an upper
    // bound of the bin's slots holding one value.  Returns false if any part isn't statically
    // enumerable (the caller then falls back to the always-safe slot count).  A non-array bin
    // is one slot covering the union of its intervals; the bins of an array element or of an
    // automatic bins declaration hold disjoint values, so the element or declaration counts once.
    bool appendBinCrossSlots(AstCoverBin* cbinp, uint64_t maxVal, AstNodeExpr* exprp,
                             std::vector<std::vector<std::pair<uint64_t, uint64_t>>>& bins,
                             int& slotCount) {
        if (isAutoBins(cbinp)) {
            ++slotCount;
            bins.push_back({{0, maxVal}});
            return exprp->width() <= 64;
        }
        if (binWith(cbinp)) {
            // A value is in one bin of a filter's, but of a sized array, in one for each range
            // list element holding it; the coverpoint's name is one element
            int elements = 0;
            for (const AstNode* rp = binRangesp(cbinp); rp && isSizedArray(cbinp);
                 rp = rp->nextp()) {
                ++elements;
            }
            slotCount += std::max(1, elements);
            return false;
        }
        if (cbinp->isArray() && cbinp->isWildcard() && !cbinp->arraySizep()) {
            // A value is in at most one bin of a wildcard array: one slot covering its values.
            // Signed values are sign-extended, not unsigned intervals (see computeHitListBound)
            ++slotCount;
            if (exprp->isSigned() || exprp->width() > 64) return false;
            const BinRuns runs = wildcardBinRuns(cbinp, exprp, false);
            if (runs.unsupported) return false;
            std::vector<std::pair<uint64_t, uint64_t>> ivs;
            for (const BinRun& run : runs.runs) {
                ivs.emplace_back(run.m_lo.toUQuad(), run.m_hi.toUQuad());
            }
            bins.push_back(std::move(ivs));
            return true;
        }
        if (cbinp->isArray()) return appendArrayBinCrossSlots(cbinp, exprp, bins, slotCount);
        // Non-array bin: one slot covering the union of its intervals.
        ++slotCount;
        std::vector<std::pair<uint64_t, uint64_t>> ivs;
        if (cbinp->isWildcard() || !extractRangeIntervals(cbinp, maxVal, ivs)) return false;
        bins.push_back(std::move(ivs));
        return true;
    }

    // Append the cross slots of an array Normal bin: each element is a slot covering its
    // values, as at most one of its single-value bins holds a value.  An element holds the
    // values arrayBinRuns() gives it: those of the coverpoint type (IEEE 1800-2023 19.5.7).
    // Elements of a signed coverpoint, non-constant elements, and elements with values beyond
    // 64 bits can't be enumerated, so they count one slot but lose exactness.  Returns false if
    // any element wasn't enumerable to exact values.
    bool appendArrayBinCrossSlots(AstCoverBin* cbinp, AstNodeExpr* exprp,
                                  std::vector<std::vector<std::pair<uint64_t, uint64_t>>>& bins,
                                  int& slotCount) {
        // Signed values resolve sign-extended, not as unsigned intervals, and wildcard patterns
        // are not intervals
        bool exact = !exprp->isSigned() && !cbinp->isWildcard();
        for (AstNode* rp = cbinp->rangesp(); rp; rp = rp->nextp()) {
            ++slotCount;
            RangeBounds rb;
            CrossValueRange range{rp, resolveWidth(rp, exprp)};
            if (!exact || !constRangeBounds(rp, rb)
                || !resolveValue(rp, exprp, true, false, range)) {
                exact = false;
                continue;
            }
            if (crossRangeEmpty(range)) continue;  // Its bin, if any, holds no value
            if (range.hi.mostSetBitP1() > 64) {
                exact = false;
                continue;
            }
            bins.push_back({{range.lo.toUQuad(), range.hi.toUQuad()}});
        }
        return exact;
    }

    // Compute the hit-list bound for a coverpoint: the maximum number of Normal
    // bins one sample value can match.  Non-cross-fed coverpoints don't feed a cross, so
    // their hit list is unused -> 1.  Otherwise compute the exact max bin overlap; fall back
    // to the (always-safe) Normal-slot count when any bin isn't statically analyzable.
    int computeHitListBound(AstCoverpoint* coverpointp, AstNodeExpr* exprp, bool crossFed) {
        if (!crossFed) return 1;
        const int width = exprp->width();
        const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
        // One entry per Normal bin (cross slot): its covered intervals.
        std::vector<std::vector<std::pair<uint64_t, uint64_t>>> bins;
        int slotCount = 0;  // == runtime m_normal; the safe fallback bound
        // Unsigned intervals cannot establish overlap between differently sized signed values.
        bool exact = !exprp->isSigned();
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            if (!cbinp->binsType().binIsNormal())
                continue;  // ignore/illegal/default: not hit-listed
            if (!appendBinCrossSlots(cbinp, maxVal, exprp, bins, slotCount)) exact = false;
        }
        if (!exact) return std::max(1, slotCount);
        if (bins.empty()) return 1;
        // Max overlap occurs at some interval start; count covering bins at each lo.
        std::vector<uint64_t> pts;
        for (const auto& b : bins)
            for (const auto& iv : b) pts.push_back(iv.first);
        std::sort(pts.begin(), pts.end());
        pts.erase(std::unique(pts.begin(), pts.end()), pts.end());
        int maxOverlap = 1;
        for (const uint64_t p : pts) {
            int cnt = 0;
            for (const auto& b : bins) {
                for (const auto& iv : b) {
                    if (iv.first <= p && p <= iv.second) {
                        ++cnt;
                        break;  // count each bin at most once
                    }
                }
            }
            if (cnt > maxOverlap) maxOverlap = cnt;
        }
        return maxOverlap;
    }

    // A 'this->m_member' reference for embedding in an AstCStmt
    AstVarRef* memberRef(FileLine* fl, AstVar* varp, VAccess access = VAccess::READ) {
        AstVarRef* const refp = new AstVarRef{fl, varp, access};
        refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        return refp;
    }

    // A 'this->m_member-><method>(args...)' call on one member.  usePtr is false only for
    // __Vcg_inst, which is a value handle; the item members are borrowed pointers into the
    // instance node.  Numeric arguments are AstConst; the rest are C++ text that has no AST
    // form (see ctext).
    AstCMethodHard* itemCall(FileLine* fl, AstVar* varp, VCMethod method,
                             const std::vector<AstNodeExpr*>& args = {}, bool usePtr = true) {
        AstCMethodHard* const callp = new AstCMethodHard{fl, memberRef(fl, varp), method};
        for (AstNodeExpr* const argp : args) callp->addPinsp(argp);
        callp->usePtr(usePtr);
        callp->dtypeSetVoid();
        return callp;
    }

    // An unsigned integer argument.
    static AstConst* cnum(FileLine* fl, uint32_t value) { return new AstConst{fl, value}; }

    // A literal C++ argument with no AST equivalent: a 'const char*' string literal (an SV
    // string AstConst emits '"..."s', a std::string temporary the runtime cannot borrow), a
    // VlCovBinKind enum token, a constant selection-word initializer list, a VlFileLineDebug, or
    // a '__V' temporary declared by the enclosing AstCStmt.
    static AstCExpr* ctext(FileLine* fl, const std::string& text) {
        return new AstCExpr{fl, text};
    }

    // A C++ string literal.  Escapes control characters as the emitter does elsewhere -- bin
    // names and filenames reach the generated code verbatim when --protect-ids is off, and an
    // SV escaped identifier may hold a quote or backslash.
    static std::string quoted(const std::string& text) {
        return "\"" + V3OutFormatter::quoteNameControls(text) + "\"";
    }

    // A 'VlFileLineDebug' argument: where the runtime reports an error about fl's construct
    static AstCExpr* fileLineDebug(FileLine* fl) {
        const std::string filename
            = VIdProtect::protectIf(fl->filename(), v3Global.opt.protectIds());
        return ctext(fl, "VlFileLineDebug{" + quoted(filename) + ", "
                             + std::to_string(fl->lineno()) + "}");
    }

    // Check that an element of an array bin (bins b[] = {values/ranges}) is a two-state
    // constant value or range; false if not, after reporting it if 'report'.
    static bool checkArrayBinElement(AstCoverBin* arrayBinp, AstNode* rangep, bool report = true) {
        if (const AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
            const AstConst* const minp = VN_CAST(irp->lhsp(), Const);
            const AstConst* const maxp = VN_CAST(irp->rhsp(), Const);
            if ((!minp && !VN_IS(irp->lhsp(), Unbounded))
                || (!maxp && !VN_IS(irp->rhsp(), Unbounded))) {
                if (report) {
                    arrayBinp->v3error("Non-constant expression in array bins range; "
                                       "range bounds must be constants (IEEE 1800-2023 19.5)");
                }
                return false;
            }
            if ((minp && minp->num().isFourState()) || (maxp && maxp->num().isFourState())) {
                if (report) {
                    arrayBinp->v3error("Four-state (x/z) value in array bins range bound; "
                                       "range bounds must be two-state constants");
                }
                return false;
            }
        } else if (!VN_IS(rangep, Const)) {
            if (report) {
                arrayBinp->v3error("Non-constant expression in array bins value list; "
                                   "values must be constants (IEEE 1800-2023 19.5)");
            }
            return false;
        }
        return true;
    }

    // Individual equality targets of an array bin (bins b[] = {values/ranges}) of a real
    // coverpoint, in order; integral coverpoints generate array bins as runs (see arrayBinRuns).
    // An open-ended bound ('$', AstUnbounded) resolves to the coverpoint domain: '[lo:$]'
    // covers [lo:maxVal] and '[$:hi]' covers [0:hi].  One target is produced per value; ranges
    // whose resolved size would exceed --coverage-max-real-bins (e.g. an open '[lo:$]') are
    // unsupported -- emits COVERIGN, sets unsupportedOut, yields nothing.
    std::vector<AstNodeExpr*> extractArrayValues(AstCoverBin* arrayBinp, AstNodeExpr* exprp,
                                                 bool& unsupportedOut) {
        unsupportedOut = false;
        const int width = exprp->width();
        const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
        std::vector<AstNodeExpr*> values;
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            rangep = V3Const::constifyEdit(rangep);
            if (!checkArrayBinElement(arrayBinp, rangep)) return values;
            if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                const bool loUnb = VN_IS(irp->lhsp(), Unbounded);
                const bool hiUnb = VN_IS(irp->rhsp(), Unbounded);
                const uint64_t lo = loUnb ? 0 : VN_AS(irp->lhsp(), Const)->toUQuad();
                const uint64_t hi = hiUnb ? maxVal : VN_AS(irp->rhsp(), Const)->toUQuad();
                if (hi < lo) continue;  // empty range contributes no bins
                // Guard against a '$'-bounded or otherwise huge range exploding the bin count.
                const uint64_t span = hi - lo;  // == valueCount - 1 (no overflow: hi >= lo)
                if (span >= v3Global.opt.coverageMaxRealBins()
                    || values.size() + span + 1 > v3Global.opt.coverageMaxRealBins()) {
                    arrayBinp->v3warn(COVERIGN,
                                      "Unsupported: array 'bins' of a real coverpoint "
                                      "covering more than "
                                          << v3Global.opt.coverageMaxRealBins() << " values; bin "
                                          << arrayBinp->prettyNameQ() << " ignored.\n"
                                          << arrayBinp->warnMore()
                                          << "... Suggest a larger --coverage-max-real-bins");
                    unsupportedOut = true;
                    for (AstNodeExpr* const vp : values) VL_DO_DANGLING(pushDeletep(vp), vp);
                    values.clear();
                    return values;
                }
                for (uint64_t v = lo; v <= hi; ++v)
                    values.push_back(new AstConst{irp->fileline(), AstConst::WidthedValue{}, width,
                                                  static_cast<uint32_t>(v)});
            } else {
                values.push_back(VN_AS(rangep->cloneTree(false), NodeExpr));
            }
        }
        return values;
    }

    static int runWidth(const AstNodeExpr* exprp) { return exprp->width() + 1; }

    // Automatic bins partition the coverpoint domain in value order (IEEE 1800-2023 19.5.3): N
    // bins, capped at the number of values, each hold 2^width / N values, and the last bin also
    // holds the remainder.  False for an invalid declaration, already reported.
    bool autoBinRuns(AstCoverBin* binp, AstNodeExpr* exprp, BinRuns& out) {
        const uint32_t requested = autoBinsRequested(binp);
        if (!requested || !exprp->dtypep()->skipRefp()->isIntegralOrPacked()) return false;
        const int width = exprp->width();
        const int arithmeticWidth = runWidth(exprp);
        const uint32_t count
            = width < 32
                  ? static_cast<uint32_t>(std::min<uint64_t>(uint64_t{1} << width, requested))
                  : requested;
        BinRun run{binp, arithmeticWidth, count};
        V3Number total{binp, arithmeticWidth};
        total.setBit(width, 1);
        run.m_stride.opDiv(total, V3Number{binp, arithmeticWidth, count});
        const CrossValueRange domain
            = crossValueDomain(binp, width, exprp->isSigned(), arithmeticWidth);
        run.m_lo = domain.lo;
        run.m_hi = domain.hi;
        out.runs.push_back(std::move(run));
        out.count = count;
        return true;
    }

    // The elements of an array bin (bins b[] = {values/ranges}), in order, as runs of
    // single-value bins.  A range holds the values of the coverpoint type it contains (IEEE
    // 1800-2023 19.5.7), while a singleton names a bin even without such a value.  Errors on a
    // non-constant element.  More than --coverage-max-bins bins (e.g. an open '[lo:$]' range over
    // a wide coverpoint) are unsupported -- emits COVERIGN, and sets unsupported.
    BinRuns arrayBinRuns(AstCoverBin* arrayBinp, AstNodeExpr* exprp) {
        BinRuns out;
        const int width = runWidth(exprp);
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            rangep = V3Const::constifyEdit(rangep);
            if (!checkArrayBinElement(arrayBinp, rangep)) return out;
            const AstInsideRange* const irp = VN_CAST(rangep, InsideRange);
            CrossValueRange range{rangep, resolveWidth(rangep, exprp)};
            bool empty = true;
            if (!resolveValue(rangep, exprp, true, false, range)) {
                rangep->v3warn(E_UNSUPPORTED, "Unsupported: non-integral value in a coverage bin "
                                              "of an integral coverpoint.");
            } else {
                empty = crossRangeEmpty(range);
            }
            if (empty && irp) continue;  // A range without values contributes no bins
            BinRun run{rangep, width, 1};
            run.m_empty = empty;
            uint64_t count = 1;
            if (!empty) {
                run.m_lo.opAssign(range.lo);
                run.m_hi.opAssign(range.hi);
                V3Number span{rangep, width};
                span.opSub(run.m_hi, run.m_lo);
                // Wider spans exceed any limit
                count = span.mostSetBitP1() > 32 ? UINT64_MAX : span.toUQuad() + 1;
            }
            if (count > v3Global.opt.coverageMaxBins() - out.count) {
                arrayBinp->v3warn(COVERIGN, "Unsupported: array 'bins' covering more than "
                                                << v3Global.opt.coverageMaxBins()
                                                << " values (e.g. an open '[lo:$]' range over "
                                                   "a wide coverpoint); bin "
                                                << arrayBinp->prettyNameQ() << " ignored\n"
                                                << arrayBinp->warnMore()
                                                << "... Suggest a larger --coverage-max-bins");
                out.runs.clear();
                out.count = 0;
                out.unsupported = true;
                return out;
            }
            run.m_count = static_cast<uint32_t>(count);
            out.count += run.m_count;
            out.runs.push_back(std::move(run));
        }
        return out;
    }

    // The bins of a wildcard array (wildcard bins b[] = {...}): one for each coverpoint value
    // an element matches (IEEE 1800-2023 19.5.4, 19.5.7), in value order, and named by the value
    // (19.5.1), as runs of single-value bins.  Errors on a non-constant element.  More than
    // --coverage-max-bins values are unsupported -- emits COVERIGN, and sets unsupported, and for
    // an ignore or illegal array, single.  'report' false omits these diagnostics.
    static BinRuns wildcardBinRuns(AstCoverBin* arrayBinp, AstNodeExpr* exprp, bool report) {
        BinRuns out;
        const int width = runWidth(exprp);
        const V3Number one{arrayBinp, width, 1};
        // Disjoint runs of the values, in value order, each value once
        std::vector<std::pair<V3Number, V3Number>> spans;
        uint64_t count = 0;  // Values of 'spans'
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            rangep = V3Const::constifyEdit(rangep);
            if (!checkArrayBinElement(arrayBinp, rangep, report)) {
                out.unsupported = true;
                return out;
            }
            CrossValueRange range{rangep, resolveWidth(rangep, exprp)};
            if (!resolveValue(rangep, exprp, true, true, range)) {
                if (report) {
                    rangep->v3warn(E_UNSUPPORTED, "Unsupported: non-integral value in a "
                                                  "coverage bin of an integral coverpoint.");
                }
                continue;
            }
            if (crossRangeEmpty(range)) continue;
            std::vector<std::pair<V3Number, V3Number>> found;
            crossRangeRuns(range, v3Global.opt.coverageMaxBins(), found);
            for (const std::pair<V3Number, V3Number>& run : found) {
                // Coverpoint values, sign-extended in both widths
                spans.emplace_back(V3Number{rangep, width, run.first},
                                   V3Number{rangep, width, run.second});
            }
            std::sort(spans.begin(), spans.end(), [](const auto& lhs, const auto& rhs) {
                return crossValueLess(lhs.first, rhs.first);
            });
            std::vector<std::pair<V3Number, V3Number>> merged;
            for (const std::pair<V3Number, V3Number>& span : spans) {
                // Adjacent or overlapping values join a run; 'first - 1' cannot overflow
                V3Number before{rangep, width};
                before.opSub(span.first, one);
                if (merged.empty() || crossValueLess(merged.back().second, before)) {
                    merged.push_back(span);
                } else if (crossValueLess(merged.back().second, span.second)) {
                    merged.back().second = span.second;
                }
            }
            count = 0;
            for (const std::pair<V3Number, V3Number>& span : merged) {
                V3Number size{rangep, width};
                size.opSub(span.second, span.first);
                // Beyond 2^32 values exceed any limit
                count += size.mostSetBitP1() > 32 ? uint64_t{1} << 33 : size.toUQuad() + 1;
                if (count > v3Global.opt.coverageMaxBins()) break;
            }
            spans = std::move(merged);
            if (count > v3Global.opt.coverageMaxBins()) {
                // An ignore or illegal array still excludes or checks its values, as one bin
                out.single = !arrayBinp->binsType().binIsNormal();
                if (report) {
                    arrayBinp->v3warn(
                        COVERIGN, "Unsupported: wildcard array '"
                                      << arrayBinp->binsType().verilogKwd()
                                      << "' of more than --coverage-max-bins of "
                                      << v3Global.opt.coverageMaxBins() << " values; bin "
                                      << arrayBinp->prettyNameQ()
                                      << (out.single ? " treated as one bin" : " ignored") << "\n"
                                      << arrayBinp->warnMore()
                                      << "... Suggest a larger --coverage-max-bins");
                }
                out.unsupported = true;
                return out;
            }
        }
        for (const std::pair<V3Number, V3Number>& span : spans) {
            out.runs.emplace_back(arrayBinp, width, 0);
            BinRun& run = out.runs.back();
            run.m_lo = span.first;
            run.m_hi = span.second;
            // A bin for each value, named by it in the coverpoint's type
            V3Number value = span.first;
            while (true) {
                const V3Number typed{arrayBinp, exprp->width(), value};
                out.values.push_back(exprp->isSigned() ? typed.toDecimalS() : typed.toDecimalU());
                ++run.m_count;
                if (value.isCaseEq(span.second)) break;
                V3Number next{arrayBinp, width};
                value = next.opAdd(value, one);
            }
        }
        out.count = static_cast<uint32_t>(count);
        return out;
    }

    // The runs of an automatic bins declaration, or of an array bin of an integral coverpoint.
    // False for other bins, which do not generate as runs, including a wildcard array then one
    // bin (see BinRuns::single).
    bool binRunsFor(AstCoverBin* binp, AstNodeExpr* exprp, BinRuns& out) {
        if (isAutoBins(binp)) {
            if (!autoBinRuns(binp, exprp, out)) out.unsupported = true;
            return true;
        }
        if (binp->isArray() && binp->isWildcard()) {
            if (!exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
                AstNodeExpr* const falsep = wildcardTypeError(binp, exprp);
                VL_DO_DANGLING(pushDeletep(falsep), falsep);
                out.unsupported = true;
            } else {
                out = wildcardBinRuns(binp, exprp, true);
                if (out.single) {
                    binp->isArray(false);  // Generates as one bin
                    return false;
                }
            }
            return true;
        }
        if (!binp->isArray() || binp->transp() || binp->isWildcard()
            || !exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
            return false;
        }
        out = arrayBinRuns(binp, exprp);
        return true;
    }

    // Emit a 'this->m_cp->addSingleNamer/addArrayNamer(...)' statement for one bin whose first
    // runtime bin index is 'declared'; or with 'valueNames', those naming each bin of an array
    AstNodeStmt* makeNamer(AstVar* cpVarp, AstCoverBin* binp, int64_t count, uint32_t declared,
                           const std::vector<AstNodeExpr*>& values = {},
                           const std::vector<std::string>& valueNames = {}) {
        FileLine* const fl = binp->fileline();
        CoverpointBins& bins = m_cpBins.at(cpVarp);
        const uint32_t normalCount
            = binp->binsType().binIsNormal() ? static_cast<uint32_t>(count < 0 ? 1 : count) : 0;
        const BinSpan span{bins.total, normalCount, declared};
        if (binp->binsType() == VCoverBinsType::BINS_AUTO_IMPLICIT) {
            bins.implicitAuto = span;  // Selected by bin, see implicitAutoBinSpan
        } else {
            bins.spans.emplace(binp->name(), span);
        }
        bins.total += normalCount;
        for (uint32_t i = 0; bins.crossed && i < normalCount; ++i) {
            bins.values.push_back({binp, values.empty() ? nullptr : values[i]});
        }
        // Under --protect-ids the filename and bin name flow into the coverage database
        // verbatim, so obfuscate them exactly as line/toggle coverage points are (whole-
        // unit filename, per-word bin name).  A no-op when --protect-ids is off.
        const bool prot = v3Global.opt.protectIds();
        const bool single = count < 0;
        if (!valueNames.empty()) {
            // A bin of a wildcard array is named by its value (IEEE 1800-2023 19.5.1)
            AstNodeStmt* stmtsp = nullptr;
            for (const std::string& value : valueNames) {
                const std::string name
                    = VIdProtect::protectWordsIf(binp->name(), prot) + "[" + value + "]";
                stmtsp = AstNode::addNext(
                    stmtsp,
                    itemCall(fl, cpVarp, VCMethod::COVERGROUP_ADD_SINGLE_NAMER,
                             {ctext(fl, binp->binsType().binSetEnum()), ctext(fl, quoted(name)),
                              ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), prot))),
                              cnum(fl, static_cast<uint32_t>(fl->lineno())),
                              cnum(fl, static_cast<uint32_t>(fl->firstColumn()))})
                        ->makeStmt());
            }
            return stmtsp;
        }
        std::vector<AstNodeExpr*> args{ctext(fl, binp->binsType().binSetEnum())};
        if (!single) args.push_back(cnum(fl, static_cast<uint32_t>(count)));  // value array bin
        args.push_back(ctext(fl, quoted(VIdProtect::protectWordsIf(binp->name(), prot))));
        args.push_back(ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), prot))));
        args.push_back(cnum(fl, static_cast<uint32_t>(fl->lineno())));
        args.push_back(cnum(fl, static_cast<uint32_t>(fl->firstColumn())));
        return itemCall(fl, cpVarp,
                        single ? VCMethod::COVERGROUP_ADD_SINGLE_NAMER
                        : binp->binsType() == VCoverBinsType::BINS_AUTO_IMPLICIT
                            ? VCMethod::COVERGROUP_ADD_NUMBERED_NAMER
                            : VCMethod::COVERGROUP_ADD_ARRAY_NAMER,
                        args)
            ->makeStmt();
    }

    // Emit 'if (iff && cond) m_cp.incrementBin(idx);' (or recordHit, + illegal action) in sample()
    // Where a bin's hit is recorded in the runtime VlCoverpoint member.
    struct ConvBinTarget final {
        AstVar* cpVarp;  // the __Vcp_<coverpoint> member
        uint32_t idx;  // bin index within that coverpoint
        bool isNormal;  // Normal -> incrementBin (count + cross hit list); else recordHit (count)
    };

    // Emit 'this->m_cp.incrementBin(idx);' (Normal) or '.recordHit(idx);'
    // (ignore/illegal/default).
    AstNodeStmt* makeRuntimeBinHit(FileLine* fl, AstVar* cpVarp, AstNodeExpr* idxp,
                                   bool isNormal) {
        return itemCall(fl, cpVarp,
                        isNormal ? VCMethod::COVERGROUP_INCREMENT_BIN
                                 : VCMethod::COVERGROUP_RECORD_HIT,
                        {idxp})
            ->makeStmt();
    }
    AstNodeStmt* makeRuntimeBinHit(FileLine* fl, const ConvBinTarget& tgt) {
        return makeRuntimeBinHit(fl, tgt.cpVarp, cnum(fl, static_cast<uint32_t>(tgt.idx)),
                                 tgt.isNormal);
    }

    // The condition under which a bin counts a sample: condp, and the bin's iff, and for a
    // Normal or default state bin, that the value is not excluded
    AstNodeExpr* binCondition(AstCoverBin* binp, AstVar* cpVarp, AstNodeExpr* condp) {
        FileLine* const fl = binp->fileline();
        if (binp->iffp()) condp = new AstLogAnd{fl, binp->iffp()->cloneTree(false), condp};
        const auto excluded = m_excludedVars.find(cpVarp);
        if (excluded != m_excludedVars.end() && !binp->transp()
            && (binp->binsType().binIsNormal()
                || binp->binsType() == VCoverBinsType::BINS_DEFAULT)) {
            condp = new AstLogAnd{
                fl, new AstNot{fl, new AstVarRef{fl, excluded->second, VAccess::READ}}, condp};
        }
        return condp;
    }

    void emitConvHitIf(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                       AstNodeExpr* idxp, AstNodeExpr* condp) {
        FileLine* const fl = binp->fileline();
        AstNode* actionp = makeRuntimeBinHit(fl, cpVarp, idxp, binp->binsType().binIsNormal());
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            actionp->addNext(makeIllegalBinAction(fl, "Illegal bin " + binp->prettyNameQ()
                                                          + " hit in coverpoint "
                                                          + coverpointp->prettyNameQ()));
        }
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for coverpoint");
        addSampleStmt(new AstIf{fl, binCondition(binp, cpVarp, condp), actionp, nullptr});
    }

    // Emit the sample() code of sized array 'sized': count the value in its bins holding it when
    // enabled, as other bins are, and for default bins note in matchedp whether any holds it
    void emitSizedSample(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                         AstNodeExpr* exprp, uint32_t sized, AstVar* matchedp) {
        FileLine* const fl = binp->fileline();
        AstNodeExpr* enabledp = binCondition(binp, cpVarp, new AstConst{fl, AstConst::BitTrue{}});
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for coverpoint");
        const bool illegal = binp->binsType() == VCoverBinsType::BINS_ILLEGAL;
        if (illegal) {
            // The illegal action reads the condition too, which is evaluated once, as the guard
            // may have side effects
            AstVar* const varp
                = new AstVar{fl, VVarType::BLOCKTEMP,
                             "__VcpEnabled_" + sanitizeGeneratedName(coverpointp->name()) + "_"
                                 + cvtToStr(sized),
                             binp->findBitDType()};
            varp->funcLocal(true);
            m_sampleFuncp->addStmtsp(varp);
            addSampleStmt(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, enabledp});
            enabledp = new AstVarRef{fl, varp, VAccess::READ};
        }
        AstCMethodHard* const callp
            = itemCall(fl, cpVarp,
                       exprp->isWide() ? VCMethod::COVERGROUP_SIZED_SAMPLE_W
                                       : VCMethod::COVERGROUP_SIZED_SAMPLE,
                       {cnum(fl, sized), exprp->cloneTree(false), enabledp});
        callp->dtypeSetBit();
        if (illegal) {
            addSampleStmt(new AstIf{fl, new AstLogAnd{fl, callp, enabledp->cloneTree(false)},
                                    makeIllegalBinAction(fl, "Illegal bin " + binp->prettyNameQ()
                                                                 + " hit in coverpoint "
                                                                 + coverpointp->prettyNameQ())});
        } else if (matchedp && binp->binsType().binIsNormal()) {
            addSampleStmt(
                new AstAssign{fl, new AstVarRef{fl, matchedp, VAccess::WRITE},
                              new AstOr{fl, new AstVarRef{fl, matchedp, VAccess::READ}, callp}});
        } else {
            addSampleStmt(callp->makeStmt());
        }
    }

    // A variable local to the constructor
    AstVar* constructorTemp(FileLine* fl, const string& name, AstNodeDType* dtypep) {
        AstVar* const varp = new AstVar{fl, VVarType::BLOCKTEMP, name, dtypep};
        varp->funcLocal(true);
        m_constructorp->addStmtsp(varp);
        return varp;
    }

    // Truncate or extend, as its signedness sets, a value to a type
    static AstNodeExpr* resizeValue(AstNodeExpr* valuep, AstNodeDType* dtypep) {
        FileLine* const fl = valuep->fileline();
        if (valuep->width() > dtypep->width()) {
            valuep = new AstSel{fl, valuep, 0, dtypep->width()};
        } else if (valuep->width() < dtypep->width()) {
            valuep = valuep->isSigned()
                         ? static_cast<AstNodeExpr*>(new AstExtendS{fl, valuep, dtypep->width()})
                         : new AstExtend{fl, valuep, dtypep->width()};
        }
        valuep->dtypep(dtypep);
        return valuep;
    }

    // The values of a coverpoint, which its name denotes (IEEE 1800-2023 19.5.1.1), as runs in
    // value order: an enumerated type's values (6.19), else all values of its type.  Bounds
    // are at runWidth(), sign-extended like a CrossValueRange's.
    static std::vector<std::pair<V3Number, V3Number>> coverpointValues(AstNode* nodep,
                                                                       AstNodeExpr* exprp) {
        const int width = runWidth(exprp);
        std::vector<std::pair<V3Number, V3Number>> runs;
        const AstEnumDType* const enump = VN_CAST(exprp->dtypep()->skipRefToEnump(), EnumDType);
        if (!enump) {
            const CrossValueRange domain
                = crossValueDomain(nodep, exprp->width(), exprp->isSigned(), width);
            runs.emplace_back(domain.lo, domain.hi);
            return runs;
        }
        std::vector<V3Number> values;
        for (const AstEnumItem* itemp = enump->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            const V3Number& num = VN_AS(itemp->valuep(), Const)->num();
            if (num.isFourState()) continue;  // Not a coverpoint value (19.5.7)
            values.emplace_back(nodep, width);
            if (exprp->isSigned()) {
                values.back().opExtendS(num, num.width());
            } else {
                values.back().opAssign(num);
            }
        }
        std::sort(values.begin(), values.end(), crossValueLess);
        const V3Number one{nodep, width, 1};
        for (const V3Number& value : values) {
            V3Number next{nodep, width};
            if (!runs.empty() && next.opAdd(runs.back().second, one).isCaseEq(value)) {
                runs.back().second = value;
            } else {
                runs.emplace_back(value, value);
            }
        }
        return runs;
    }

    // Emit the constructor code building the bins 'binp' whose values it computes: the values of
    // each element that are coverpoint values (IEEE 1800-2023 19.5.7), those a 'with' filter
    // keeps (19.5.1.1), then its bins
    void generateConstructedBins(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                                 AstNodeExpr* exprp) {
        FileLine* const fl = binp->fileline();
        const string prefix
            = m_sizedNames.get(sanitizeGeneratedName(coverpointp->name() + "__" + binp->name()));
        AstVar* countp = nullptr;
        if (AstNodeExpr* const sizep = binp->arraySizep()) {
            countp = constructorTemp(fl, prefix + "_count", sizep->dtypep());
            m_constructorp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, countp, VAccess::WRITE},
                                                    sizep->cloneTree(false)});
        }
        AstCoverWith* const withp = binWith(binp);
        if (withp && !binRangesp(binp)) {  // The coverpoint's name: all of its values
            for (const std::pair<V3Number, V3Number>& run : coverpointValues(binp, exprp)) {
                m_constructorp->addStmtsp(itemCall(fl, cpVarp,
                                                   exprp->isWide()
                                                       ? VCMethod::COVERGROUP_SIZED_RANGE_W
                                                       : VCMethod::COVERGROUP_SIZED_RANGE,
                                                   {newValueConst(fl, run.first, exprp),
                                                    newValueConst(fl, run.second, exprp)})
                                              ->makeStmt());
            }
        }
        uint32_t element = 0;
        for (AstNode* rangep = binRangesp(binp); rangep; rangep = rangep->nextp()) {
            if (VN_IS(rangep, Unbounded)) {  // A parameter of '$'
                binp->v3error("Bins value may not be '$', which may only bound a range "
                              "(IEEE 1800-2023 6.20.7)");
                continue;
            }
            generateSizedElement(cpVarp, binp, rangep, exprp, prefix + "_" + cvtToStr(element++));
        }
        if (withp) generateWithFilter(binp, withp, cpVarp, exprp, prefix);
        AstNodeExpr* countValuep;
        AstNodeExpr* positivep;
        if (countp) {
            const auto countRef = [&]() { return new AstVarRef{fl, countp, VAccess::READ}; };
            AstConst* const zerop = new AstConst{fl, AstConst::DTyped{}, countp->dtypep()};
            positivep = countp->isSigned()
                            ? static_cast<AstNodeExpr*>(new AstGtS{fl, countRef(), zerop})
                            : new AstNeq{fl, countRef(), zerop};
            // Saturate a count wider than 64 bits: min(N, T) is unchanged, or over any limit
            countValuep = resizeValue(countRef(), countp->findUInt64DType());
            if (countp->width() > VL_QUADSIZE) {
                countValuep = new AstCond{
                    fl,
                    new AstRedOr{fl, new AstSel{fl, countRef(), VL_QUADSIZE,
                                                countp->width() - VL_QUADSIZE}},
                    new AstConst{fl, AstConst::Unsized64{}, std::numeric_limits<uint64_t>::max()},
                    countValuep};
                countValuep->dtypeSetUInt64();
            }
        } else {  // Of a filter's scalar bin, or bin per value
            countValuep = new AstConst{fl, AstConst::Unsized64{}, 1};
            positivep = new AstConst{fl, AstConst::BitTrue{}};
        }
        std::vector<AstNodeExpr*> args{ctext(fl, binp->binsType().binSetEnum()), countValuep,
                                       positivep};
        // A filter's bins have the limit it began with
        if (!withp) args.push_back(cnum(fl, v3Global.opt.coverageMaxBins()));
        const bool prot = v3Global.opt.protectIds();
        args.push_back(ctext(fl, quoted(VIdProtect::protectWordsIf(binp->name(), prot))));
        args.push_back(ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), prot))));
        args.push_back(cnum(fl, static_cast<uint32_t>(fl->lineno())));
        args.push_back(cnum(fl, static_cast<uint32_t>(fl->firstColumn())));
        m_constructorp->addStmtsp(
            itemCall(fl, cpVarp,
                     withp ? VCMethod::COVERGROUP_WITH_FINISH : VCMethod::COVERGROUP_SIZED_FINISH,
                     args)
                ->makeStmt());
    }

    // Emit the constructor code evaluating the 'with' filter of 'binp' for each of its candidate
    // values, which sizedRange() added, passing the runs of values it keeps (IEEE 1800-2023
    // 19.5.1.1).  The filter is evaluated in a loop, whose code does not grow with the elements:
    //   withBegin(grouping, limit);
    //   more = 1;
    //   while (withNext()) {
    //       value = withLo(); last = withHi(); run = 0;
    //       while (true) {
    //           item = value;
    //           if (filter) { if (!run) { first = value; run = 1; } }
    //           else if (run) { more = withRun(first, value - 1); run = 0; }
    //           if (!more || value == last) break;
    //           ++value;
    //       }
    //       if (run) more = withRun(first, last);
    //   }
    void generateWithFilter(AstCoverBin* binp, AstCoverWith* withp, AstVar* cpVarp,
                            AstNodeExpr* exprp, const string& prefix) {
        FileLine* const fl = withp->fileline();
        const bool wide = exprp->isWide();
        const string grouping = !binp->isArray()     ? "Single"
                                : binp->arraySizep() ? "Fixed"
                                                     : "Values";
        m_constructorp->addStmtsp(itemCall(fl, cpVarp, VCMethod::COVERGROUP_WITH_BEGIN,
                                           {ctext(fl, "VlCovBinGrouping::" + grouping),
                                            cnum(fl, v3Global.opt.coverageMaxBins())})
                                      ->makeStmt());
        // The candidates count in the coverpoint's width, and the filter reads each as 'item',
        // of the coverpoint's type, so that a filter changing 'item' cannot change the loop
        AstNodeDType* const valueDTypep
            = exprp->findLogicDType(exprp->width(), exprp->width(),
                                    exprp->isSigned() ? VSigning::SIGNED : VSigning::UNSIGNED);
        AstVar* const valuep = constructorTemp(fl, prefix + "_value", valueDTypep);
        AstVar* const lastp = constructorTemp(fl, prefix + "_last", valueDTypep);
        AstVar* const firstp = constructorTemp(fl, prefix + "_first", valueDTypep);
        AstVar* const runp = constructorTemp(fl, prefix + "_run", binp->findBitDType());
        AstVar* const morep = constructorTemp(fl, prefix + "_more", binp->findBitDType());
        AstVar* const itemp = withp->itemp()->unlinkFrBack();
        itemp->name(prefix + "_item");
        m_constructorp->addStmtsp(itemp);
        const auto ref = [&](AstVar* varp) { return new AstVarRef{fl, varp, VAccess::READ}; };
        const auto assign = [&](AstVar* varp, AstNodeExpr* rhsp) -> AstNode* {
            return new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, rhsp};
        };
        const auto flag = [&](AstVar* varp, bool value) {
            return assign(varp, value ? new AstConst{fl, AstConst::BitTrue{}}
                                      : new AstConst{fl, AstConst::BitFalse{}});
        };
        const auto bound = [&](VCMethod narrow, VCMethod wideMethod, AstVar* varp) -> AstNode* {
            if (wide) {
                return itemCall(fl, cpVarp, wideMethod, {new AstVarRef{fl, varp, VAccess::WRITE}})
                    ->makeStmt();
            }
            AstCMethodHard* const callp = itemCall(fl, cpVarp, narrow);
            callp->dtypeSetUInt64();
            return assign(varp, resizeValue(callp, valueDTypep));
        };
        const auto keep = [&](AstNodeExpr* lop, AstNodeExpr* hip) {
            AstCMethodHard* const callp = itemCall(
                fl, cpVarp, wide ? VCMethod::COVERGROUP_WITH_RUN_W : VCMethod::COVERGROUP_WITH_RUN,
                {lop, hip});
            callp->dtypeSetBit();
            return assign(morep, callp);
        };
        const auto step = [&](bool up) {
            AstConst* const onep = new AstConst{fl, AstConst::WidthedValue{}, exprp->width(), 1};
            AstNodeExpr* const stepp
                = up ? static_cast<AstNodeExpr*>(new AstAdd{fl, ref(valuep), onep})
                     : new AstSub{fl, ref(valuep), onep};
            stepp->dtypep(valueDTypep);
            return stepp;
        };
        AstLoop* const innerp = new AstLoop{fl};
        innerp->addStmtsp(assign(itemp, ref(valuep)));
        innerp->addStmtsp(new AstIf{
            fl, withp->filterp()->unlinkFrBack(),
            new AstIf{fl, new AstNot{fl, ref(runp)},
                      assign(firstp, ref(valuep))->addNext(flag(runp, true))},
            new AstIf{fl, ref(runp), keep(ref(firstp), step(false))->addNext(flag(runp, false))}});
        innerp->addStmtsp(new AstLoopTest{
            fl, innerp, new AstLogAnd{fl, ref(morep), new AstNeq{fl, ref(valuep), ref(lastp)}}});
        innerp->addStmtsp(assign(valuep, step(true)));
        AstLoop* const outerp = new AstLoop{fl};
        AstCMethodHard* const nextp = itemCall(fl, cpVarp, VCMethod::COVERGROUP_WITH_NEXT);
        nextp->dtypeSetBit();
        outerp->addStmtsp(new AstLoopTest{fl, outerp, nextp});
        outerp->addStmtsp(
            bound(VCMethod::COVERGROUP_WITH_LO, VCMethod::COVERGROUP_WITH_LO_W, valuep));
        outerp->addStmtsp(
            bound(VCMethod::COVERGROUP_WITH_HI, VCMethod::COVERGROUP_WITH_HI_W, lastp));
        outerp->addStmtsp(flag(runp, false));
        outerp->addStmtsp(innerp);
        outerp->addStmtsp(new AstIf{fl, ref(runp), keep(ref(firstp), ref(lastp))});
        m_constructorp->addStmtsp(flag(morep, true));
        m_constructorp->addStmtsp(outerp);
    }

    // Emit 'sizedRange(lo, hi)' for the coverpoint values of an element of bins 'binp', whose
    // values the constructor computes: resolved now if constant, else when constructed by
    // clipping to the coverpoint's values.  A wildcard pattern's values give a range for each
    // run of them.  'prefix' names its temporaries.
    void generateSizedElement(AstVar* cpVarp, const AstCoverBin* binp, AstNode* rangep,
                              AstNodeExpr* exprp, const string& prefix) {
        FileLine* const fl = rangep->fileline();
        const VCMethod method = exprp->isWide() ? VCMethod::COVERGROUP_SIZED_RANGE_W
                                                : VCMethod::COVERGROUP_SIZED_RANGE;
        const AstInsideRange* const irp = VN_CAST(rangep, InsideRange);
        AstNodeExpr* const lowp = irp ? irp->lhsp() : VN_AS(rangep, NodeExpr);
        AstNodeExpr* const highp = irp ? irp->rhsp() : nullptr;
        const auto unbounded
            = [](const AstNodeExpr* boundp) { return !boundp || VN_IS(boundp, Unbounded); };
        const auto constant
            = [&](const AstNodeExpr* boundp) { return unbounded(boundp) || VN_IS(boundp, Const); };
        const auto integral = [&](const AstNodeExpr* boundp) {
            return unbounded(boundp) || boundp->dtypep()->skipRefp()->isIntegralOrPacked();
        };
        if (constant(lowp) && constant(highp)) {
            const auto fourState = [](const AstNodeExpr* boundp) {
                const AstConst* const constp = VN_CAST(boundp, Const);
                return constp && constp->num().isFourState();
            };
            if (irp && (fourState(lowp) || fourState(highp))) {
                rangep->v3error("Four-state (x/z) value in "
                                << (binp->isArray() ? "array bins" : "bin")
                                << " range bound; range bounds must be two-state constants");
                return;
            }
            CrossValueRange range{rangep, resolveWidth(rangep, exprp)};
            if (!resolveValue(rangep, exprp, true, binp->isWildcard(), range)) {
                rangep->v3warn(E_UNSUPPORTED, "Unsupported: non-integral value in a coverage bin "
                                              "of an integral coverpoint.");
            } else if (!crossRangeEmpty(range)) {
                std::vector<std::pair<V3Number, V3Number>> runs{{range.lo, range.hi}};
                if (range.wildcard) {  // checkConstructedBins bounded the runs
                    runs.clear();
                    crossRangeRuns(range, v3Global.opt.coverageMaxBins(), runs);
                }
                for (const std::pair<V3Number, V3Number>& run : runs) {
                    m_constructorp->addStmtsp(itemCall(fl, cpVarp, method,
                                                       {newValueConst(fl, run.first, exprp),
                                                        newValueConst(fl, run.second, exprp)})
                                                  ->makeStmt());
                }
            }
            return;
        }
        if (!integral(lowp) || !integral(highp)) {
            rangep->v3warn(E_UNSUPPORTED, "Unsupported: non-integral value in a coverage bin "
                                          "of an integral coverpoint.");
            return;
        }
        // Compare values and the coverpoint's domain signed, in a width holding all of them
        const auto boundWidth
            = [&](const AstNodeExpr* boundp) { return unbounded(boundp) ? 0 : boundp->width(); };
        const int width = std::max({exprp->width(), boundWidth(lowp), boundWidth(highp)}) + 1;
        const CrossValueRange domain
            = crossValueDomain(rangep, exprp->width(), exprp->isSigned(), width);
        AstVar* const lop = constructorTemp(fl, prefix + "_lo", exprp->dtypep());
        lop->dtypeSetLogicSized(width, VSigning::SIGNED);
        AstVar* const hip = constructorTemp(fl, prefix + "_hi", lop->dtypep());
        const auto bound = [&](AstNodeExpr* boundp, const V3Number& limit) -> AstNodeExpr* {
            if (unbounded(boundp)) {
                AstConst* const limitp = new AstConst{fl, limit};
                limitp->dtypeFrom(lop);
                return limitp;
            }
            AstNodeExpr* valuep = boundp->cloneTree(false);
            // A value no wider than a signed coverpoint has its type (see crossRangeBound)
            if (exprp->isSigned() && boundp->width() <= exprp->width()) {
                valuep = resizeValue(valuep, exprp->dtypep());
            }
            return resizeValue(valuep, lop->dtypep());
        };
        const auto ref = [&](AstVar* varp, VAccess access = VAccess::READ) {
            return new AstVarRef{fl, varp, access};
        };
        m_constructorp->addStmtsp(
            new AstAssign{fl, ref(lop, VAccess::WRITE), bound(lowp, domain.lo)});
        m_constructorp->addStmtsp(
            new AstAssign{fl, ref(hip, VAccess::WRITE), irp ? bound(highp, domain.hi) : ref(lop)});
        AstConst* const minp = new AstConst{fl, domain.lo};
        AstConst* const maxp = new AstConst{fl, domain.hi};
        minp->dtypeFrom(lop);
        maxp->dtypeFrom(lop);
        AstCond* const lowerp
            = new AstCond{fl, new AstLtS{fl, ref(lop), minp}, minp->cloneTree(false), ref(lop)};
        AstCond* const upperp
            = new AstCond{fl, new AstGtS{fl, ref(hip), maxp}, maxp->cloneTree(false), ref(hip)};
        lowerp->dtypeFrom(lop);
        upperp->dtypeFrom(lop);
        m_constructorp->addStmtsp(new AstAssign{fl, ref(lop, VAccess::WRITE), lowerp});
        m_constructorp->addStmtsp(new AstAssign{fl, ref(hip, VAccess::WRITE), upperp});
        m_constructorp->addStmtsp(new AstIf{fl, new AstLteS{fl, ref(lop), ref(hip)},
                                            itemCall(fl, cpVarp, method,
                                                     {resizeValue(ref(lop), exprp->dtypep()),
                                                      resizeValue(ref(hip), exprp->dtypep())})
                                                ->makeStmt()});
    }

    // The runtime index of the bin of a run holding the coverpoint value, which is in the run:
    // declared + (value - lo) / stride, capped at the last bin, which holds any remainder.
    static AstNodeExpr* runBinIndex(FileLine* fl, AstNodeExpr* exprp, const BinRun& run) {
        if (run.m_count == 1) return cnum(fl, run.m_declared);
        const int width = exprp->width();
        // A run spans at most 2^width values, so offsets in it are unsigned width-bit numbers
        AstNodeExpr* indexp
            = new AstSub{fl, exprp->cloneTree(false), newValueConst(fl, run.m_lo, exprp)};
        indexp->dtypeSetLogicSized(width, VSigning::UNSIGNED);
        V3Number stride{fl, width, 0};
        stride.opAssign(run.m_stride);
        if (stride.countOnes() != 1) {
            indexp = new AstDiv{fl, indexp, new AstConst{fl, stride}};
        } else if (!stride.isEqOne()) {
            indexp = new AstShiftR{fl, indexp, new AstConst{fl, stride.mostSetBitP1() - 1}};
        }
        // Compare the run's values with those of count bins of stride values, without overflow
        const int extWidth = run.m_lo.width() + 1;
        V3Number lo{fl, extWidth, 0};
        lo.opExtendS(run.m_lo, run.m_lo.width());
        V3Number span{fl, extWidth, 0};
        span.opExtendS(run.m_hi, run.m_hi.width());
        span.opSub(V3Number{span}, lo);
        V3Number covered{fl, extWidth, 0};
        covered.opAssign(run.m_stride);
        covered.opMul(V3Number{covered}, V3Number{fl, extWidth, run.m_count});
        V3Number hasRemainder{fl, 1, 0};
        if (!hasRemainder.opGte(span, covered).isEqZero()) {
            AstConst* const lastp = new AstConst{fl, V3Number{fl, width, run.m_count - 1}};
            indexp = new AstCond{fl, new AstGt{fl, indexp->cloneTree(false), lastp},
                                 lastp->cloneTree(false), indexp};
        }
        if (width < VL_IDATASIZE) {
            indexp = new AstExtend{fl, indexp, VL_IDATASIZE};
        } else if (width > VL_IDATASIZE) {
            indexp = new AstSel{fl, indexp, 0, VL_IDATASIZE};
        }
        return new AstAdd{fl, cnum(fl, run.m_declared), indexp};
    }

    // Emit the sample() hit of a run of bins, whose code does not grow with its number of bins:
    //   if (iff && lo <= value && value <= hi) m_cp.incrementBin(<runBinIndex>);
    void emitRunHit(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                    AstNodeExpr* exprp, const BinRun& run) {
        FileLine* const fl = binp->fileline();
        AstConst* const lop = newValueConst(fl, run.m_lo, exprp);
        AstNodeExpr* condp = nullptr;
        if (run.m_lo.isCaseEq(run.m_hi)) {
            condp = new AstEq{fl, exprp->cloneTree(false), lop};
        } else {
            AstConst* const hip = newValueConst(fl, run.m_hi, exprp);
            condp = makeRangeCondition(fl, exprp, lop, hip);
            VL_DO_DANGLING(pushDeletep(lop), lop);
            VL_DO_DANGLING(pushDeletep(hip), hip);
        }
        emitConvHitIf(coverpointp, binp, cpVarp, runBinIndex(fl, exprp, run), condp);
    }

    // Emit a transition bin's hit action into sample():
    //   if (cond) { m_cp.incrementBin/recordHit(idx); [illegal: $error; $stop] }
    // Used by the transition generators so a completed sequence records into the runtime bin.
    void addConvTransHitIf(AstCoverpoint* coverpointp, AstCoverBin* binp, const ConvBinTarget& tgt,
                           AstNodeExpr* condp) {
        FileLine* const fl = binp->fileline();
        AstNode* actionp = makeRuntimeBinHit(fl, tgt);
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            actionp->addNext(makeIllegalBinAction(
                fl, "Illegal transition bin " + binp->prettyNameQ() + " hit in coverpoint "
                        + coverpointp->prettyNameQ()));
        }
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for transition bin");
        addSampleStmt(new AstIf{fl, condp, actionp, nullptr});
    }

    // Route a coverpoint through a VlCoverpoint member: emit the member, its sample()
    // increments, the constructor configuration (init + namers), and registration.
    void generateCoverpoint(AstCoverpoint* coverpointp, AstNodeExpr* exprp, int atLeastValue) {
        FileLine* const fl = coverpointp->fileline();
        const bool dynamic = m_runtimePoints.count(coverpointp);
        UINFO(4, "  Generating VlCoverpoint member: " << coverpointp->name());

        // Size the hit list to the gen-time max bin overlap (1 unless cross-fed with
        // overlapping ranges), so no cross hit is ever dropped and storage is minimal.
        const bool crossFed = m_crossedCpNames.count(coverpointp->name()) != 0;
        const int hitBound = computeHitListBound(coverpointp, exprp, crossFed);
        UINFO(6, "    Hit-list bound (max bin overlap) = " << hitBound);
        AstVar* const cpVarp = new AstVar{fl, VVarType::MEMBER, "__Vcp_" + coverpointp->name(),
                                          coverpointDType(fl, static_cast<uint32_t>(hitBound))};
        m_covergroupp->addMembersp(cpVarp);
        m_cpVarMap[coverpointp->name()] = cpVarp;
        m_cpBins.emplace(cpVarp, CoverpointBins{});
        m_cpBins.at(cpVarp).exprp = exprp;
        m_cpBins.at(cpVarp).crossed = crossFed;
        // Create the runtime in the instance node first; everything below configures it.
        m_constructorp->addStmtsp(makeItemCreate(fl, cpVarp, VCMethod::COVERGROUP_ADD_COVERPOINT));
        generateItemWeight(fl, cpVarp, coverpointp->optionsp());

        // A cross reads this coverpoint's hit list, so clear it at the start of the
        // coverpoint's sample() contribution (before any incrementBin appends to it), even
        // when the iff guard disables sampling.
        if (crossFed) {
            UASSERT_OBJ(m_sampleFuncp, coverpointp, "sample() CFunc not set for clearHitList");
            m_sampleFuncp->addStmtsp(
                itemCall(fl, cpVarp, VCMethod::COVERGROUP_CLEAR_HIT_LIST)->makeStmt());
        }
        if (dynamic && coverpointHasStateExclusions(coverpointp)) {
            AstVar* const excludedp
                = new AstVar{fl, VVarType::BLOCKTEMP,
                             "__VcpExcluded_" + sanitizeGeneratedName(coverpointp->name()),
                             coverpointp->findBitDType()};
            excludedp->funcLocal(true);
            m_sampleFuncp->addStmtsp(excludedp);
            AstCMethodHard* const callp
                = itemCall(fl, cpVarp,
                           exprp->isWide() ? VCMethod::COVERGROUP_VALUE_EXCLUDED_W
                                           : VCMethod::COVERGROUP_VALUE_EXCLUDED,
                           {exprp->cloneTree(false)});
            callp->dtypeSetBit();
            addSampleStmt(new AstAssign{fl, new AstVarRef{fl, excludedp, VAccess::WRITE}, callp});
            m_excludedVars.emplace(cpVarp, excludedp);
        }

        // Walk bins (non-default, then default), assigning sequential indices that match the
        // namer append order; emit sample increments and collect namer statements.  Constructed
        // bins follow them all, placed when the coverpoint is constructed.
        std::vector<AstNodeStmt*> namerStmts;
        std::vector<AstCoverBin*> defaultBins;
        std::vector<AstCoverBin*> sizedBins;
        std::vector<std::tuple<AstCoverBin*, uint32_t, AstNodeExpr*>> metadata;
        std::vector<const BinRun*> runMetadata;
        uint64_t idx = 0;  // Runtime index of the next bin; 32-bit once checked below
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            const int errorsBefore = dynamic ? V3Error::errorCount() : 0;
            if (cbinp->binsType() == VCoverBinsType::BINS_DEFAULT) {
                defaultBins.push_back(cbinp);
                continue;
            }
            if (isConstructedBins(cbinp)) {
                UASSERT_OBJ(dynamic, cbinp, "Constructed bins without value metadata");
                BinSpan span;
                span.sized = static_cast<int32_t>(sizedBins.size());
                m_cpBins.at(cpVarp).spans.emplace(cbinp->name(), span);
                sizedBins.push_back(cbinp);
                continue;
            }
            if (cbinp->transp()) {
                // Transition bin (incl. array transition 'bins t[] = (a=>b),(c=>d)' and
                // illegal_bins/ignore_bins transitions).  All sequences of one transition bin
                // share a bin name and merge in the coverage DB to a single point, so model
                // them as one runtime bin incremented by any matching sequence.  The sequence
                // matching is generated as a state machine, with the hit routed to this bin's
                // runtime slot.
                namerStmts.push_back(makeNamer(cpVarp, cbinp, -1, static_cast<uint32_t>(idx)));
                const ConvBinTarget tgt{cpVarp, static_cast<uint32_t>(idx),
                                        cbinp->binsType().binIsNormal()};
                for (AstNode* sp = cbinp->transp(); sp; sp = sp->nextp())
                    generateSingleTransitionCode(coverpointp, cbinp, exprp, tgt,
                                                 VN_AS(sp, CoverTransSet));
                if (dynamic && V3Error::errorCount() == errorsBefore) {
                    metadata.emplace_back(cbinp, static_cast<uint32_t>(idx), nullptr);
                }
                ++idx;
                continue;
            }
            BinRuns plan;
            if (binRunsFor(cbinp, exprp, plan)) {
                // Array elements and automatic bins generate as runs, so neither sample() nor
                // the constructor grows with their number of bins.
                if (plan.unsupported) {  // bin ignored or invalid; reserve no slot
                    m_droppedBins[coverpointp].push_back(cbinp->name());
                    continue;
                }
                CoverpointBins& bins = m_cpBins.at(cpVarp);
                const uint32_t firstValue = bins.total;
                const uint32_t firstDeclared = static_cast<uint32_t>(idx);
                namerStmts.push_back(
                    makeNamer(cpVarp, cbinp, plan.count, firstDeclared, {}, plan.values));
                for (BinRun& run : plan.runs) {
                    run.m_declared = static_cast<uint32_t>(idx);
                    bins.runs.push_back(std::move(run));
                    const BinRun& stored = bins.runs.back();
                    if (bins.crossed && cbinp->binsType().binIsNormal()) {
                        const uint32_t first = firstValue + stored.m_declared - firstDeclared;
                        for (uint32_t element = 0; element < stored.m_count; ++element) {
                            bins.values[first + element].runp = &stored;
                            bins.values[first + element].element = element;
                        }
                    }
                    if (!stored.m_empty) {
                        emitRunHit(coverpointp, cbinp, cpVarp, exprp, stored);
                        if (dynamic && V3Error::errorCount() == errorsBefore) {
                            runMetadata.push_back(&stored);
                        }
                    }
                    idx += stored.m_count;
                }
                continue;
            }
            if (cbinp->isArray()) {  // value array of a real coverpoint: b[0]..b[N-1]
                // Only integral coverpoints have runtime value metadata (m_runtimePoints)
                UASSERT_OBJ(!dynamic, cbinp, "Runtime value metadata for a real coverpoint");
                bool unsupported = false;
                std::vector<AstNodeExpr*> values = extractArrayValues(cbinp, exprp, unsupported);
                if (unsupported) {  // bin ignored (COVERIGN emitted); reserve no slot
                    m_droppedBins[coverpointp].push_back(cbinp->name());
                    continue;
                }
                namerStmts.push_back(makeNamer(cpVarp, cbinp, static_cast<int64_t>(values.size()),
                                               static_cast<uint32_t>(idx), values));
                for (AstNodeExpr* valuep : values) {
                    // The cross selections of this covergroup still read the value.
                    m_detachedValues.push_back(valuep);
                    emitConvHitIf(coverpointp, cbinp, cpVarp,
                                  cnum(cbinp->fileline(), static_cast<uint32_t>(idx)),
                                  buildValueCondition(cbinp, exprp, valuep));
                    ++idx;
                }
            } else {
                namerStmts.push_back(makeNamer(cpVarp, cbinp, -1, static_cast<uint32_t>(idx)));
                // buildBinCondition is null for 'ignore_bins = default' (no ranges); the bin
                // still gets a reserved slot (recorded, never incremented).
                if (AstNodeExpr* const condp = buildBinCondition(cbinp, exprp))
                    emitConvHitIf(coverpointp, cbinp, cpVarp,
                                  cnum(cbinp->fileline(), static_cast<uint32_t>(idx)), condp);
                if (dynamic && V3Error::errorCount() == errorsBefore) {
                    metadata.emplace_back(cbinp, static_cast<uint32_t>(idx), nullptr);
                }
                ++idx;
            }
        }
        // A cross selecting an ignored bins declaration selects no bins
        for (const std::string& name : m_droppedBins[coverpointp]) {
            m_cpBins.at(cpVarp).spans.emplace(name, BinSpan{});
        }
        // A value a constructed bin holds is no default bin's; only sampling tells which do
        AstVar* sizedMatchedp = nullptr;
        if (!defaultBins.empty()
            && std::any_of(sizedBins.begin(), sizedBins.end(), [](const AstCoverBin* binp) {
                   return binp->binsType().binIsNormal();
               })) {
            sizedMatchedp = new AstVar{fl, VVarType::BLOCKTEMP,
                                       "__VcpSized_" + sanitizeGeneratedName(coverpointp->name()),
                                       coverpointp->findBitDType()};
            sizedMatchedp->funcLocal(true);
            m_sampleFuncp->addStmtsp(sizedMatchedp);
            addSampleStmt(new AstAssign{fl, new AstVarRef{fl, sizedMatchedp, VAccess::WRITE},
                                        new AstConst{fl, AstConst::BitFalse{}}});
        }
        for (uint32_t sized = 0; sized < sizedBins.size(); ++sized) {
            emitSizedSample(coverpointp, sizedBins[sized], cpVarp, exprp, sized, sizedMatchedp);
        }
        for (AstCoverBin* const defBinp : defaultBins) {
            FileLine* const dfl = defBinp->fileline();
            namerStmts.push_back(makeNamer(cpVarp, defBinp, -1, static_cast<uint32_t>(idx)));
            AstNodeExpr* condp = buildDefaultCondition(coverpointp, exprp, dfl);
            if (sizedMatchedp) {
                condp = new AstLogAnd{
                    dfl, new AstNot{dfl, new AstVarRef{dfl, sizedMatchedp, VAccess::READ}}, condp};
            }
            emitConvHitIf(coverpointp, defBinp, cpVarp, cnum(dfl, static_cast<uint32_t>(idx)),
                          condp);
            ++idx;
        }
        if (idx > std::numeric_limits<uint32_t>::max()) {
            // The runtime indexes bins with 32 bits; stop before generating a model
            coverpointp->v3warn(E_UNSUPPORTED, "Unsupported: coverpoint with more than "
                                                   << std::numeric_limits<uint32_t>::max()
                                                   << " bins");
        }

        // Transition coverpoints track the previous sampled value; update it once at the end of
        // this coverpoint's sample() contribution (the prev var was created on demand by the
        // transition matching above).
        if (coverpointHasTransition(coverpointp)) {
            AstVar* const prevVarp = VN_AS(coverpointp->user1p(), Var);
            addSampleStmt(
                new AstAssign{coverpointp->fileline(),
                              new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::WRITE},
                              exprp->cloneTree(false)});
        }

        // Constructor: init (allocates), namers, then registration (under --coverage).
        // Under --protect-ids the hierarchy and page string reach the coverage database
        // verbatim, so obfuscate them like line/toggle points (per-word hierarchy, whole-
        // unit page).  No-ops when --protect-ids is off.
        const bool prot = v3Global.opt.protectIds();
        const std::string hier
            = VIdProtect::protectWordsIf(m_covergroupName + "." + coverpointp->name(), prot);
        m_constructorp->addStmtsp(
            itemCall(fl, cpVarp, VCMethod::COVERGROUP_INIT,
                     {ctext(fl, quoted(hier)), cnum(fl, static_cast<uint32_t>(atLeastValue)),
                      cnum(fl, static_cast<uint32_t>(idx))})
                ->makeStmt());
        for (AstNodeStmt* const ns : namerStmts) m_constructorp->addStmtsp(ns);
        if (dynamic) {
            m_constructorp->addStmtsp(
                itemCall(fl, cpVarp, VCMethod::COVERGROUP_VALUE_TYPE,
                         {cnum(fl, exprp->width()), cnum(fl, exprp->isSigned())})
                    ->makeStmt());
            ValueLists lists;
            for (const auto& entry : metadata) {
                collectValueMetadata(lists, exprp, std::get<0>(entry), std::get<1>(entry),
                                     std::get<2>(entry));
            }
            for (const BinRun* const runp : runMetadata) collectRunMetadata(lists, exprp, *runp);
            emitValueList(fl, cpVarp, VCMethod::COVERGROUP_VALUE_RANGES, lists.m_ranges);
            emitValueList(fl, cpVarp, VCMethod::COVERGROUP_VALUE_RUNS, lists.m_runs);
            emitValueList(fl, cpVarp, VCMethod::COVERGROUP_VALUE_PATTERNS, lists.m_patterns);
            emitValueList(fl, cpVarp, VCMethod::COVERGROUP_VALUE_TRANSITIONS, lists.m_transitions);
            for (AstCoverBin* const binp : sizedBins) {
                generateConstructedBins(coverpointp, binp, cpVarp, exprp);
            }
            m_constructorp->addStmtsp(
                itemCall(fl, cpVarp, VCMethod::COVERGROUP_VALUE_FINALIZE)->makeStmt());
        }
        if (v3Global.opt.coverage()) {
            const std::string page
                = VIdProtect::protectIf("v_covergroup/" + m_covergroupName, prot);
            m_constructorp->addStmtsp(
                itemCall(fl, cpVarp, VCMethod::COVERGROUP_REGISTER_BINS,
                         {ctext(fl, "vlSymsp->_vm_contextp__->coveragep()"),
                          ctext(fl, quoted(page)),
                          cnum(fl, itemDatabaseWeight(coverpointp->optionsp())),
                          cnum(fl, m_cgTypeWeight)})
                    ->makeStmt());
        }
    }

    // Generate state machine code for multi-value transition sequences
    // Handles transitions like (1 => 2 => 3 => 4)
    void generateMultiValueTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                          AstNodeExpr* exprp, const ConvBinTarget& tgt,
                                          const std::vector<AstCoverTransItem*>& items) {
        UINFO(4, "    Generating multi-value transition state machine for: " << binp->name());
        UINFO(4, "      Sequence length: " << items.size() << " items");

        // Create state position variable
        AstVar* const stateVarp = createSequenceStateVar(coverpointp, binp);

        // Build case statement with N cases (one for each state 0 to N-1)
        // State 0: Not started, looking for first item
        // State 1 to N-1: In progress, looking for next item

        AstCase* const casep
            = new AstCase{binp->fileline(), VCaseType::CT_CASE,
                          new AstVarRef{stateVarp->fileline(), stateVarp, VAccess::READ}, nullptr};

        // Generate each case item in the switch statement
        for (size_t state = 0; state < items.size(); ++state) {
            AstCaseItem* caseItemp = generateTransitionStateCase(coverpointp, binp, exprp, tgt,
                                                                 stateVarp, items, state);
            casep->addItemsp(caseItemp);
        }

        // Add default case (reset to state 0) to prevent CASEINCOMPLETE warnings,
        // since the state variable is wider than the number of valid states.
        AstCaseItem* const defaultItemp = new AstCaseItem{
            binp->fileline(), nullptr,
            new AstAssign{binp->fileline(),
                          new AstVarRef{binp->fileline(), stateVarp, VAccess::WRITE},
                          new AstConst{binp->fileline(), AstConst::WidthedValue{}, 8, 0}}};
        casep->addItemsp(defaultItemp);

        addSampleStmt(casep);
        UINFO(4, "      Successfully added multi-value transition state machine");
    }

    // Generate code for a single state in the transition state machine
    // Returns the case item for this state
    AstCaseItem* generateTransitionStateCase(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                             AstNodeExpr* exprp, const ConvBinTarget& tgt,
                                             AstVar* stateVarp,
                                             const std::vector<AstCoverTransItem*>& items,
                                             size_t state) {
        FileLine* const fl = binp->fileline();

        // Build condition for current value matching expected item at this state
        AstNodeExpr* const matchCondp = buildTransitionItemCondition(items[state], exprp);

        AstNodeStmt* matchActionp = nullptr;

        if (state == items.size() - 1) {
            // Last state: sequence complete!  Record the hit in the runtime VlCoverpoint.
            matchActionp = makeRuntimeBinHit(fl, tgt);

            // For illegal_bins, add error message
            if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                const string errMsg = "Illegal transition bin " + binp->prettyNameQ()
                                      + " hit in coverpoint " + coverpointp->prettyNameQ();
                matchActionp = matchActionp->addNext(makeIllegalBinAction(fl, errMsg));
            }

            // Reset state to 0
            matchActionp = matchActionp->addNext(
                new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                              new AstConst{fl, AstConst::WidthedValue{}, 8, 0}});
        } else {
            // Intermediate state: advance to next state
            matchActionp = new AstAssign{
                fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                new AstConst{fl, AstConst::WidthedValue{}, 8, static_cast<uint32_t>(state + 1)}};
        }

        // Build restart logic: check if current value matches first item
        // If so, restart sequence from state 1 (even if we're in middle of sequence)
        AstNodeStmt* noMatchActionp = nullptr;
        if (state > 0) {
            // Check if current value matches first item (restart condition)
            AstNodeExpr* const restartCondp = buildTransitionItemCondition(items[0], exprp);

            UASSERT_OBJ(restartCondp, items[0],
                        "buildTransitionItemCondition returned nullptr for restart");

            // Restart to state 1
            AstNodeStmt* restartActionp
                = new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                                new AstConst{fl, AstConst::WidthedValue{}, 8, 1}};

            // Reset to state 0 (else branch)
            AstNodeStmt* resetActionp
                = new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                                new AstConst{fl, AstConst::WidthedValue{}, 8, 0}};

            noMatchActionp = new AstIf{fl, restartCondp, restartActionp, resetActionp};
        }
        // For state 0, no action needed if no match (stay in state 0)

        // Combine into if-else
        AstNodeStmt* const stmtp = new AstIf{fl, matchCondp, matchActionp, noMatchActionp};

        // Create case item for this state value
        AstCaseItem* const caseItemp = new AstCaseItem{
            fl, new AstConst{fl, AstConst::WidthedValue{}, 8, static_cast<uint32_t>(state)},
            stmtp};

        return caseItemp;
    }

    // Create: $error(msg); $stop;  Used when an illegal bin is hit.
    AstNodeStmt* makeIllegalBinAction(FileLine* fl, const string& errMsg) {
        AstDisplay* const errorp
            = new AstDisplay{fl, VDisplayType::DT_ERROR, errMsg, nullptr, nullptr};
        errorp->fmtp()->timeunit(m_covergroupp->timeunit());
        static_cast<AstNode*>(errorp)->addNext(new AstStop{fl, true});
        return errorp;
    }

    // Preserve the coverpoint's width and signedness after V3Width.
    static AstConst* newValueConst(FileLine* fl, const V3Number& value, const AstNodeExpr* exprp) {
        V3Number narrowed{fl, exprp->width(), 0};
        narrowed.opAssign(value);
        AstConst* const constp = new AstConst{fl, narrowed};
        constp->dtypeFrom(exprp);
        return constp;
    }

    // A real copy of a real or integral range bound, for comparing with a real coverpoint.
    static AstConst* newRealConst(AstConst* constp) {
        if (constp->num().isDouble()) return constp->cloneTree(false);
        V3Number real{&constp->num(), 64};
        real.opIToRD(constp->num(), constp->isSigned());
        return new AstConst{constp->fileline(), real};
    }

    // Clone a constant node, widening to targetWidth if needed (zero-extend).
    // Used to ensure comparisons use matching widths after V3Width has run.
    static AstConst* widenConst(FileLine* fl, AstConst* constp, int targetWidth) {
        if (constp->width() == targetWidth) return constp->cloneTree(false);
        V3Number num{fl, targetWidth, 0};
        num.opAssign(constp->num());
        return new AstConst{fl, num};
    }

    // Build a range condition: minp <= exprp <= maxp.
    // Uses signed comparisons if exprp is signed; omits trivially-true domain bounds.
    // All arguments are non-owning; clones exprp/minp/maxp as needed.
    AstNodeExpr* makeRangeCondition(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* minp,
                                    AstNodeExpr* maxp) {
        const int exprWidth = exprp->widthMin();
        AstConst* const minConstp = VN_AS(minp, Const);
        AstConst* const maxConstp = VN_AS(maxp, Const);
        if (exprp->isDouble()) {
            // A real coverpoint has no finite domain bounds to omit.
            return new AstAnd{fl,
                              new AstGteD{fl, exprp->cloneTree(false), newRealConst(minConstp)},
                              new AstLteD{fl, exprp->cloneTree(false), newRealConst(maxConstp)}};
        }
        // Widen constants to match expression width so post-V3Width nodes use correct macros
        AstConst* const minWidep = widenConst(fl, minConstp, exprWidth);
        AstConst* const maxWidep = widenConst(fl, maxConstp, exprWidth);
        V3Number minimum{fl, exprWidth, 0};
        V3Number maximum{fl, exprWidth, 0};
        maximum.setAllBits1();
        if (exprp->isSigned()) {
            minimum.setBit(exprWidth - 1, 1);
            maximum.setBit(exprWidth - 1, 0);
        }
        AstNodeExpr* lowerp = nullptr;
        AstNodeExpr* upperp = nullptr;
        if (minWidep->num().isCaseEq(minimum)) {
            VL_DO_DANGLING(pushDeletep(minWidep), minWidep);
        } else {
            lowerp = exprp->isSigned() ? static_cast<AstNodeExpr*>(
                                             new AstGteS{fl, exprp->cloneTree(false), minWidep})
                                       : static_cast<AstNodeExpr*>(
                                             new AstGte{fl, exprp->cloneTree(false), minWidep});
        }
        if (maxWidep->num().isCaseEq(maximum)) {
            VL_DO_DANGLING(pushDeletep(maxWidep), maxWidep);
        } else {
            upperp = exprp->isSigned() ? static_cast<AstNodeExpr*>(
                                             new AstLteS{fl, exprp->cloneTree(false), maxWidep})
                                       : static_cast<AstNodeExpr*>(
                                             new AstLte{fl, exprp->cloneTree(false), maxWidep});
        }
        if (lowerp && upperp) return new AstAnd{fl, lowerp, upperp};
        if (lowerp) return lowerp;
        if (upperp) return upperp;
        return new AstConst{fl, AstConst::BitTrue{}};
    }

    // Build a one-sided comparison for an open-ended bin range whose other bound is '$'.
    // '$' denotes the coverpoint domain extreme, so {[lo:$]} == (expr >= lo) and
    // {[$:hi]} == (expr <= hi).
    AstNodeExpr* makeOpenRangeCondition(FileLine* fl, AstNodeExpr* exprp, AstConst* boundp,
                                        bool isLowerBound) {
        AstConst* const widep = widenConst(fl, boundp, exprp->widthMin());
        if (isLowerBound) {
            if (exprp->isSigned()) return new AstGteS{fl, exprp->cloneTree(false), widep};
            return new AstGte{fl, exprp->cloneTree(false), widep};
        }
        if (exprp->isSigned()) return new AstLteS{fl, exprp->cloneTree(false), widep};
        return new AstLte{fl, exprp->cloneTree(false), widep};
    }

    // Build condition for a single transition item.
    // Returns expression that checks if exprp matches the item's value/range list.
    // Overload for when the expression is a variable read -- creates and manages the VarRef
    // internally, so callers don't need to construct a temporary node.
    AstNodeExpr* buildTransitionItemCondition(AstCoverTransItem* itemp, AstVar* varp) {
        AstNodeExpr* varRefp = new AstVarRef{varp->fileline(), varp, VAccess::READ};
        AstNodeExpr* const condp = buildTransitionItemCondition(itemp, varRefp);
        VL_DO_DANGLING(pushDeletep(varRefp), varRefp);
        return condp;
    }

    // Non-owning: exprp is cloned internally; caller retains ownership of exprp.
    AstNodeExpr* buildTransitionItemCondition(AstCoverTransItem* itemp, AstNodeExpr* exprp) {
        AstNodeExpr* condp = nullptr;

        for (AstNode* valp = itemp->valuesp(); valp; valp = valp->nextp()) {
            AstNodeExpr* singleCondp = nullptr;
            valp = V3Const::constifyEdit(valp);
            AstConst* const constp = VN_CAST(valp, Const);
            if (!constp) {
                valp->v3error("Non-constant expression in transition bin; "
                              "values must be constants (IEEE 1800-2023 19.5)");
                return new AstConst{valp->fileline(), AstConst::BitFalseErroring{}};
            }
            singleCondp
                = new AstEq{constp->fileline(), exprp->cloneTree(false), constp->cloneTree(false)};
            if (condp) {
                condp = new AstOr{itemp->fileline(), condp, singleCondp};
            } else {
                condp = singleCondp;
            }
        }

        return condp;
    }

    // Generate code for a single transition sequence (used by both regular and array bins)
    void generateSingleTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                      AstNodeExpr* exprp, const ConvBinTarget& tgt,
                                      AstCoverTransSet* transSetp) {
        UINFO(4, "      Generating code for transition sequence");

        // Get or create previous value variable
        AstVar* const prevVarp = createPrevValueVar(coverpointp, exprp);

        UASSERT_OBJ(
            transSetp, binp,
            "Transition bin has no transition set (transp() was checked before calling this)");

        // Get transition items (the sequence: item1 => item2 => item3)
        std::vector<AstCoverTransItem*> items;
        for (AstNode* itemp = transSetp->itemsp(); itemp; itemp = itemp->nextp())
            items.push_back(VN_AS(itemp, CoverTransItem));

        if (items.empty()) {
            binp->v3error("Transition set without items");
            return;
        }

        if (items.size() == 1) {
            // Single item transition not valid (need at least 2 values for =>)
            binp->v3error("Transition requires at least two values");
            return;
        } else if (items.size() == 2) {
            // Simple two-value transition: (val1 => val2)
            // Use optimized direct comparison (no state machine needed)
            AstNodeExpr* const cond1p = buildTransitionItemCondition(items[0], prevVarp);
            AstNodeExpr* const cond2p = buildTransitionItemCondition(items[1], exprp);

            // Combine: prev matches val1 AND current matches val2
            AstNodeExpr* fullCondp = new AstAnd{binp->fileline(), cond1p, cond2p};

            addConvTransHitIf(coverpointp, binp, tgt, fullCondp);

            UINFO(4, "        Successfully added 2-value transition if statement");
        } else {
            // Multi-value sequence (a => b => c => ...)
            // Use state machine to track position in sequence
            generateMultiValueTransitionCode(coverpointp, binp, exprp, tgt, items);
        }
    }

    // Append a "{ VlCoverpoint* __Vcx_cps[] = {cp0, cp1, ...}; <call> }" statement.  The brace
    // and the temporary array stay literal text -- a CMethodHard is one call, not a block --
    // but callp itself carries the member, method and '->'.  Construction only: init() copies
    // the array into the cross, so sample() reads it from there and needs no array at all.
    AstCStmt* makeCrossCpsCall(FileLine* fl, const std::vector<AstVar*>& cpVars,
                               AstCMethodHard* callp) {
        AstCStmt* const cs = new AstCStmt{fl};
        cs->add("{ VlCoverpoint* __Vcx_cps[] = {");
        for (size_t d = 0; d < cpVars.size(); ++d) {
            if (d != 0) cs->add(", ");
            cs->add(memberRef(fl, cpVars[d]));
        }
        cs->add("}; ");
        cs->add(callp);
        cs->add("; }");
        return cs;
    }

    // Assign the per-bin flags individually: one-bit SV results have integer C++ storage types,
    // which may narrow in a bool initializer list but convert implicitly in assignments.
    AstCStmt* makeCrossIffsCall(FileLine* fl, const std::vector<AstCoverCrossBin*>& bins,
                                AstCMethodHard* callp) {
        AstCStmt* const cs = new AstCStmt{fl};
        cs->add("{ bool __Vcx_iffs[" + cvtToStr(bins.size()) + "]; ");
        for (size_t i = 0; i < bins.size(); ++i) {
            const AstCoverCrossBin* const binp = bins[i];
            cs->add("__Vcx_iffs[" + cvtToStr(i) + "] = ");
            cs->add(binp->iffp() ? binp->iffp()->cloneTree(false)
                                 : new AstConst{fl, AstConst::BitTrue{}});
            cs->add("; ");
        }
        cs->add(callp);
        cs->add("; }");
        return cs;
    }

    using CrossSelection = std::vector<uint64_t>;
    struct ResolvedCrossBin final {
        AstCoverCrossBin* binp;
        CrossSelection selection;
    };
    struct CrossLayout final {
        uint32_t tuples = 0;
        uint32_t autoBins = 0;
        uint64_t binWords = 0;
        bool valid = true;
        std::vector<ResolvedCrossBin> bins;
    };
    struct CrossSelectionContext final {
        AstCoverCross* crossp;  // Cross whose tuple space is being selected
        const std::vector<AstVar*>& cpVars;  // Feeding coverpoints in dimension order
        const std::map<std::string, uint32_t>& dimensions;  // Coverpoint name -> dimension
        uint32_t tuples;  // Size of the Cartesian product
        std::vector<uint32_t> strides;  // Flat-index stride per dimension
        bool valid = true;  // False if this explicit bin cannot be implemented
    };
    struct CrossBinsofTarget final {
        const CoverpointBins* m_binsp = nullptr;  // Declared bins; null after a reported error
        uint32_t m_dimension = 0;  // Coverpoint index within the cross
        uint32_t m_first = 0;  // First declared normal bin in the selected span
        uint32_t m_count = 0;  // Number of declared normal bins in the selected span
        uint32_t m_declaredFirst = 0;  // First runtime bin index of the selected span
        uint32_t m_declaredEnd = UINT32_MAX;  // One past the last runtime bin index
        int32_t m_sized = -1;  // Index of the sized array holding the selected bins; or -1
    };
    struct CrossValueRange final {
        V3Number lo;  // Inclusive lower bound, sign-extended to the comparison width
        V3Number hi;  // Inclusive upper bound
        V3Number pattern;  // Allowed bit values; all X for an ordinary interval
        bool wildcard = false;  // A wildcard singleton rather than an exact four-state value

        CrossValueRange(AstNode* nodep, int width)
            : lo{nodep, width}
            , hi{nodep, width}
            , pattern{nodep, width} {
            pattern.setAllBitsX();
        }
    };

    static std::vector<AstNode*> crossBinValues(const CrossBinValues& bin) {
        if (bin.valuep) return {bin.valuep};
        std::vector<AstNode*> values;
        if (bin.binp->transp()) {
            // IEEE 1800-2023 19.6.1: binsof uses the last value of each transition.
            for (AstNode* setp = bin.binp->transp(); setp; setp = setp->nextp()) {
                AstCoverTransItem* lastp = VN_AS(setp, CoverTransSet)->itemsp();
                while (lastp->nextp()) lastp = VN_AS(lastp->nextp(), CoverTransItem);
                for (AstNode* valuep = lastp->valuesp(); valuep; valuep = valuep->nextp()) {
                    values.push_back(valuep);
                }
            }
        } else {
            for (AstNode* valuep = bin.binp->rangesp(); valuep; valuep = valuep->nextp()) {
                values.push_back(valuep);
            }
        }
        return values;
    }

    // The values of the element-th bin of a run, sign-extended to 'width'
    static CrossValueRange runBinRange(AstNode* nodep, const BinRun& run, uint32_t element,
                                       int width) {
        const int runw = run.m_lo.width();
        V3Number offset{nodep, runw};
        offset.opMul(run.m_stride, V3Number{nodep, runw, element});
        V3Number lo{nodep, runw};
        lo.opAdd(run.m_lo, offset);
        V3Number hi = run.m_hi;
        if (element + 1 < run.m_count) {
            offset.opSub(run.m_stride, V3Number{nodep, runw, 1});
            hi.opAdd(lo, offset);
        }
        CrossValueRange range{nodep, width};
        range.lo.opExtendS(lo, runw);
        range.hi.opExtendS(hi, runw);
        return range;
    }

    static int crossRangeWidth(AstNode* nodep) {
        if (const AstInsideRange* const rangep = VN_CAST(nodep, InsideRange)) {
            return std::max(rangep->lhsp()->width(), rangep->rhsp()->width());
        }
        return nodep->width();
    }

    static bool crossValueLess(const V3Number& lhs, const V3Number& rhs) {
        V3Number result{&lhs};
        return !result.opLtS(lhs, rhs).isEqZero();
    }

    // Round a real bound inward to the nearest coverpoint value (IEEE 1800-2023 19.5.7).  Sets
    // 'empty' if the domain has no value on the bound's side.
    static void crossRealBound(const AstConst* constp, AstNodeExpr* exprp, bool upper,
                               const CrossValueRange& domain, V3Number& result, bool& empty) {
        const double value = constp->num().toDouble();
        const double bound = upper ? std::floor(value) : std::ceil(value);
        // Powers of two are exact, so the integral bound compares exactly with the domain edges.
        const double limit
            = std::ldexp(1.0, exprp->isSigned() ? exprp->width() - 1 : exprp->width());
        const double minimum = exprp->isSigned() ? -limit : 0.0;
        if (std::isnan(bound) || (upper ? bound < minimum : bound >= limit)) {
            empty = true;
            result = domain.lo;
        } else if (bound < minimum) {
            result = domain.lo;
        } else if (bound >= limit) {
            result = domain.hi;
        } else {
            V3Number real{&result, 64};
            real.setDouble(bound);
            result.opRToIRoundS(real);
        }
    }

    static bool crossRangeBound(AstNode* nodep, AstNodeExpr* exprp, bool upper, bool binValue,
                                const CrossValueRange& domain, V3Number& result, bool& empty) {
        if (VN_IS(nodep, Unbounded)) {
            V3Number limit{nodep, exprp->width()};
            if (upper) limit.setAllBits1();
            if (exprp->isSigned()) {
                limit.setBit(exprp->width() - 1, !upper);
                result.opExtendS(limit, limit.width());
            } else {
                result.opAssign(limit);
            }
            return true;
        }
        const AstConst* const constp = VN_CAST(nodep, Const);
        if (!constp) return false;
        if (constp->num().isDouble()) {
            crossRealBound(constp, exprp, upper, domain, result, empty);
            return true;
        }
        if (constp->num().isString()) return false;
        if (binValue && exprp->isSigned() && constp->width() <= exprp->width()) {
            // Bin bit patterns use the coverpoint's effective type (IEEE 1800-2023 19.5.7).
            // Wider values and intersect filters retain their values for domain clipping.
            V3Number value{nodep, exprp->width()};
            if (constp->isSigned()) {
                value.opExtendS(constp->num(), constp->width());
            } else {
                value.opAssign(constp->num());
            }
            result.opExtendS(value, value.width());
        } else if (constp->isSigned()) {
            result.opExtendS(constp->num(), constp->width());
        } else {
            result.opAssign(constp->num());
        }
        return true;
    }

    static CrossValueRange crossValueDomain(AstNode* nodep, int valueWidth, bool isSigned,
                                            int width) {
        CrossValueRange domain{nodep, width};
        V3Number lo{nodep, valueWidth};
        V3Number hi{nodep, valueWidth};
        hi.setAllBits1();
        if (isSigned) {
            lo.setBit(valueWidth - 1, 1);
            hi.setBit(valueWidth - 1, 0);
            domain.lo.opExtendS(lo, valueWidth);
            domain.hi.opExtendS(hi, valueWidth);
        } else {
            domain.lo.opAssign(lo);
            domain.hi.opAssign(hi);
        }
        return domain;
    }

    static void intersectCrossRange(CrossValueRange& range, const CrossValueRange& other) {
        if (crossValueLess(range.lo, other.lo)) range.lo = other.lo;
        if (crossValueLess(other.hi, range.hi)) range.hi = other.hi;
    }

    static bool crossValueRange(AstNode* nodep, AstNodeExpr* exprp, bool binValue, bool wildcard,
                                const CrossValueRange& domain, CrossValueRange& range) {
        bool empty = false;
        const AstConst* const constp = VN_CAST(nodep, Const);
        if (const AstInsideRange* const rangep = VN_CAST(nodep, InsideRange)) {
            if (!crossRangeBound(rangep->lhsp(), exprp, false, binValue, domain, range.lo, empty)
                || !crossRangeBound(rangep->rhsp(), exprp, true, binValue, domain, range.hi, empty)
                || range.lo.isFourState() || range.hi.isFourState()) {
                return false;
            }
        } else if (constp && constp->num().isDouble()) {
            // A real value participates only if integral; it has no wildcard bits.
            crossRealBound(constp, exprp, false, domain, range.lo, empty);
            crossRealBound(constp, exprp, true, domain, range.hi, empty);
        } else {
            if (!crossRangeBound(nodep, exprp, false, binValue, domain, range.lo, empty)) {
                return false;
            }
            if (binValue && exprp->isSigned() && constp && !constp->isSigned()
                && constp->width() > exprp->width()) {
                bool representable = true;
                for (int bit = exprp->width(); bit < constp->width(); ++bit) {
                    representable &= !constp->num().bitIs1(bit);
                }
                if (representable) {
                    V3Number value{nodep, exprp->width()};
                    value.opAssign(constp->num());
                    range.lo.opExtendS(value, value.width());
                }
            }
            range.hi = range.lo;
            range.wildcard = wildcard;
            if (wildcard) {
                range.pattern = range.lo;
                range.lo = domain.lo;
                range.hi = domain.hi;
                if (constp && constp->isSigned()) {
                    // Replicated X sign bits are correlated, not independent wildcards.
                    // The source domain preserves expansion-before-casting (19.5.7).
                    intersectCrossRange(
                        range, crossValueDomain(nodep, constp->width(), true, domain.lo.width()));
                }
            }
        }
        if (empty) {
            range.lo = domain.hi;
            range.hi = domain.lo;
            return true;
        }
        if (!range.lo.isFourState()) intersectCrossRange(range, domain);
        if (range.wildcard && exprp->isSigned()) {
            const int sign = exprp->width() - 1;
            if (constp && !constp->isSigned() && constp->width() > exprp->width()) {
                // Unsigned equality preserves every target bit pattern if discarded bits are zero.
                for (int bit = exprp->width(); bit < constp->width(); ++bit) {
                    if (constp->num().bitIs1(bit)) {
                        range.lo = domain.hi;
                        range.hi = domain.lo;
                        return true;
                    }
                }
                for (int bit = exprp->width(); bit < range.pattern.width(); ++bit) {
                    if (range.pattern.bitIsXZ(sign))
                        range.pattern.setBit(bit, 'x');
                    else
                        range.pattern.setBit(bit, range.pattern.bitIs1(sign));
                }
                return true;
            }
            // Discarded high bits constrain the target sign, rather than becoming don't-cares.
            for (int bit = exprp->width(); bit < range.pattern.width(); ++bit) {
                if (range.pattern.bitIsXZ(bit)) continue;
                const bool value = range.pattern.bitIs1(bit);
                if (!range.pattern.bitIsXZ(sign) && range.pattern.bitIs1(sign) != value) {
                    range.lo = domain.hi;
                    range.hi = domain.lo;
                    break;
                }
                range.pattern.setBit(sign, value);
            }
        }
        return true;
    }

    enum CrossRangeState : uint8_t {
        CROSS_INSIDE_BOUNDS = 0,  // Prefix is strictly inside the interval
        CROSS_AT_LOWER = 1,
        CROSS_AT_UPPER = 2,
        CROSS_AT_BOUNDS = CROSS_AT_LOWER | CROSS_AT_UPPER,
        CROSS_NO_MATCH = 4  // Prefix cannot match the interval/pattern
    };

    static CrossRangeState crossRangeStep(const CrossValueRange& range, CrossRangeState state,
                                          int bit, int value) {
        if (state == CROSS_NO_MATCH) return CROSS_NO_MATCH;
        // Flipping the sign bit makes signed order lexicographic.
        const bool sign = bit == range.pattern.width() - 1;
        if (!range.pattern.bitIsXZ(bit) && value != (range.pattern.bitIs1(bit) ^ sign)) {
            return CROSS_NO_MATCH;
        }
        const int low = range.lo.bitIs1(bit) ^ sign;
        const int high = range.hi.bitIs1(bit) ^ sign;
        if (((state & CROSS_AT_LOWER) && value < low)
            || ((state & CROSS_AT_UPPER) && value > high)) {
            return CROSS_NO_MATCH;
        }
        return static_cast<CrossRangeState>(
            ((state & CROSS_AT_LOWER) && value == low ? CROSS_AT_LOWER : CROSS_INSIDE_BOUNDS)
            | ((state & CROSS_AT_UPPER) && value == high ? CROSS_AT_UPPER : CROSS_INSIDE_BOUNDS));
    }

    static bool crossWildcardIntersects(const CrossValueRange& range) {
        unsigned states = 1U << CROSS_AT_BOUNDS;
        for (int bit = range.pattern.width() - 1; bit >= 0 && states; --bit) {
            unsigned next = 0;
            for (const CrossRangeState state :
                 {CROSS_INSIDE_BOUNDS, CROSS_AT_LOWER, CROSS_AT_UPPER, CROSS_AT_BOUNDS}) {
                if (!(states & (1U << state))) continue;
                for (int value = 0; value < 2; ++value) {
                    const CrossRangeState equal = crossRangeStep(range, state, bit, value);
                    if (equal != CROSS_NO_MATCH) next |= 1U << equal;
                }
            }
            states = next;
        }
        return states != 0;
    }

    // The least value at least 'from' with the non-x bits of 'pattern', in unsigned order; false
    // if none.  A bit scan, which does not enumerate the pattern's x bits.
    static bool nextPatternValue(const V3Number& pattern, const V3Number& from, V3Number& result) {
        result.opAssign(from);
        int carry = -1;  // Lowest x bit above the bit scanned where 'from' has a 0
        for (int bit = from.width() - 1; bit >= 0; --bit) {
            if (pattern.bitIsXZ(bit)) {
                if (!from.bitIs1(bit)) carry = bit;
                continue;
            }
            if (pattern.bitIs1(bit) == from.bitIs1(bit)) continue;
            if (from.bitIs1(bit)) {  // Only a greater prefix, an x bit above raised, can match
                if (carry < 0) return false;
                bit = carry;
            }
            // Then the least such value: the pattern's bits, with x bits of zero
            result.setBit(bit, 1);
            while (--bit >= 0) result.setBit(bit, pattern.bitIs1(bit));
            return true;
        }
        return true;
    }

    // Append to 'runs' the maximal runs of consecutive values of 'range' that its pattern
    // matches, in value order, until there are more than 'limit'.  A match continues through
    // the pattern's trailing x bits only, which the next value's carry leaves.
    static void crossRangeRuns(const CrossValueRange& range, size_t limit,
                               std::vector<std::pair<V3Number, V3Number>>& runs) {
        // Values order signed, which is the unsigned order of values with the sign bit flipped
        const int sign = range.lo.width() - 1;
        const auto flipped = [sign](V3Number value) {
            if (!value.bitIsXZ(sign)) value.setBit(sign, !value.bitIs1(sign));
            return value;
        };
        const V3Number pattern = flipped(range.pattern);
        const V3Number hi = flipped(range.hi);
        const V3Number one{&hi, hi.width(), 1};
        V3Number trailing{&hi, hi.width()};
        for (int bit = 0; bit <= sign && pattern.bitIsXZ(bit); ++bit) trailing.setBit(bit, 1);
        V3Number from = flipped(range.lo);
        V3Number first{&hi, hi.width()};
        V3Number last{&hi, hi.width()};
        V3Number less{&hi};
        while (runs.size() <= limit && nextPatternValue(pattern, from, first)
               && less.opLt(hi, first).isEqZero()) {
            last.opOr(first, trailing);
            if (!less.opLt(hi, last).isEqZero()) last = hi;
            runs.emplace_back(flipped(first), flipped(last));
            if (last.isCaseEq(hi)) break;
            from.opAdd(last, one);
        }
    }

    // True if no coverpoint value participates in a resolved value or range.  A value with x
    // or z bits participates only as a wildcard pattern (IEEE 1800-2023 19.5.7).
    static bool crossRangeEmpty(const CrossValueRange& range) {
        if (range.lo.isFourState()) return true;
        return crossValueLess(range.hi, range.lo)
               || (range.wildcard && !crossWildcardIntersects(range));
    }

    // Comparison width that holds both the coverpoint's and a bin or intersect value's range.
    static int resolveWidth(AstNode* nodep, const AstNodeExpr* exprp) {
        return std::max(exprp->width(), crossRangeWidth(nodep)) + 1;
    }

    // Resolve a bin or intersect value to coverpoint values (IEEE 1800-2023 19.5.7), in the
    // width 'range' was created with.  False if the value is not a constant integral or real.
    static bool resolveValue(AstNode* nodep, AstNodeExpr* exprp, bool binValue, bool wildcard,
                             CrossValueRange& range) {
        const CrossValueRange domain
            = crossValueDomain(nodep, exprp->width(), exprp->isSigned(), range.lo.width());
        return crossValueRange(nodep, exprp, binValue, wildcard, domain, range);
    }

    static bool crossRangesIntersect(const CrossValueRange& bin, const CrossValueRange& filter) {
        // Values with x or z bits do not participate, even in an identical filter.
        if (bin.lo.isFourState() || filter.lo.isFourState()) return false;
        CrossValueRange match = bin;
        intersectCrossRange(match, filter);
        return !crossValueLess(match.hi, match.lo)
               && (!bin.wildcard || crossWildcardIntersects(match));
    }

    static void unsupportedCrossRange(AstCoverBinsof* selectp, bool& valid) {
        selectp->v3warn(COVERIGN, "Unsupported: non-constant or non-integral 'intersect' value, "
                                  "or four-state range bound.");
        valid = false;
    }

    static bool crossValueMatchesFilters(AstCoverBinsof* selectp, AstNode* valuep,
                                         AstNodeExpr* exprp, const AstCoverBin* binp,
                                         const CrossValueRange& domain,
                                         const std::vector<CrossValueRange>& filters,
                                         bool& valid) {
        CrossValueRange range{valuep, domain.lo.width()};
        if (!crossValueRange(valuep, exprp, true, binp->isWildcard(), domain, range)) {
            unsupportedCrossRange(selectp, valid);
            return false;
        }
        for (const CrossValueRange& filter : filters) {
            if (crossRangesIntersect(range, filter)) return true;
        }
        return false;
    }

    std::vector<bool> selectCoverpointBins(AstCoverBinsof* selectp, const CoverpointBins& bins,
                                           uint32_t first, uint32_t count, bool& valid) {
        if (selectp->rangesp() && !bins.exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
            unsupportedCrossRange(selectp, valid);
            return {};
        }
        std::vector<bool> selected(bins.total, false);
        std::vector<std::vector<AstNode*>> values;
        int width = bins.exprp->width();
        for (AstNode* rangep = selectp->rangesp(); rangep; rangep = rangep->nextp()) {
            width = std::max(width, crossRangeWidth(rangep));
        }
        if (selectp->rangesp()) {
            values.reserve(count);
            for (uint32_t i = first; i < first + count; ++i) {
                // A run's values are in the coverpoint type, whose width 'width' covers
                values.push_back(bins.values[i].runp ? std::vector<AstNode*>{}
                                                     : crossBinValues(bins.values[i]));
                for (AstNode* const valuep : values.back()) {
                    width = std::max(width, crossRangeWidth(valuep));
                }
            }
        }
        // One extra bit preserves both unsigned maxima and negative signed bounds.
        ++width;
        const CrossValueRange domain
            = crossValueDomain(selectp, bins.exprp->width(), bins.exprp->isSigned(), width);
        std::vector<CrossValueRange> filters;
        for (AstNode* rangep = selectp->rangesp(); rangep; rangep = rangep->nextp()) {
            CrossValueRange filter{rangep, width};
            if (!crossValueRange(rangep, bins.exprp, false, false, domain, filter)) {
                unsupportedCrossRange(selectp, valid);
                return {};
            }
            filters.push_back(std::move(filter));
        }
        for (uint32_t i = first; i < first + count; ++i) {
            if (!selectp->rangesp()) {
                selected[i] = true;
                continue;
            }
            if (const BinRun* const runp = bins.values[i].runp) {
                const CrossValueRange range
                    = runBinRange(selectp, *runp, bins.values[i].element, width);
                selected[i] = std::any_of(filters.begin(), filters.end(),
                                          [&](const CrossValueRange& filter) {
                                              return crossRangesIntersect(range, filter);
                                          });
                continue;
            }
            for (AstNode* const valuep : values[i - first]) {
                selected[i] = crossValueMatchesFilters(
                    selectp, valuep, bins.exprp, bins.values[i].binp, domain, filters, valid);
                if (!valid) return {};
                if (selected[i]) break;
            }
        }
        if (selectp->isNegated()) {
            for (uint32_t i = 0; i < bins.total; ++i) selected[i] = !selected[i];
        }
        return selected;
    }

    // Constructor-time value metadata of one coverpoint, as C++ list entries
    struct ValueLists final {
        std::vector<std::string> m_ranges;  // Bin, then low and high words
        std::vector<std::string> m_runs;  // First bin, count, then low, span, and high words
        std::vector<std::string> m_patterns;  // Bin, then value, mask, low, and high words
        std::vector<std::string> m_transitions;  // Transition bin
    };

    // Append a value's words, in the coverpoint's width, to a C++ list entry.
    static void appendWords(std::string& text, const V3Number& value, const AstNodeExpr* exprp) {
        V3Number narrowed{&value, exprp->width()};
        narrowed.opAssign(value);
        for (int word = 0; word < exprp->widthWords(); ++word) {
            text += ", " + cvtToStr(narrowed.edataWord(word)) + "U";
        }
    }

    void collectValueMetadata(ValueLists& lists, AstNodeExpr* exprp, AstCoverBin* binp,
                              uint32_t index, AstNodeExpr* valuep) {
        const std::string bin = cvtToStr(index) + "U";
        if (binp->transp()) lists.m_transitions.push_back(bin);
        for (AstNode* const sourcep : crossBinValues({binp, valuep})) {
            CrossValueRange range{sourcep, resolveWidth(sourcep, exprp)};
            if (!resolveValue(sourcep, exprp, true, binp->isWildcard(), range)) {
                // Sampling already resolved every state bin value, so only transitions remain.
                sourcep->v3warn(E_UNSUPPORTED, "Unsupported: non-integral value in a transition "
                                               "bin of a coverpoint with exclusions.");
                continue;
            }
            if (crossRangeEmpty(range)) continue;
            std::string entry = bin;
            if (range.wildcard) {
                V3Number value{sourcep, exprp->width()};
                V3Number mask{sourcep, exprp->width()};
                mask.opBitsNonXZ(range.pattern);
                value.opBitsOne(range.pattern);
                appendWords(entry, value, exprp);
                appendWords(entry, mask, exprp);
            }
            appendWords(entry, range.lo, exprp);
            appendWords(entry, range.hi, exprp);
            (range.wildcard ? lists.m_patterns : lists.m_ranges).push_back(entry);
        }
    }

    // Describe a run with one entry, from which the runtime computes the values of its bins.
    static void collectRunMetadata(ValueLists& lists, AstNodeExpr* exprp, const BinRun& run) {
        V3Number span{exprp, run.m_stride.width(), 0};
        span.opSub(run.m_stride, V3Number{exprp, run.m_stride.width(), 1});
        std::string entry = cvtToStr(run.m_declared) + "U, " + cvtToStr(run.m_count) + "U";
        appendWords(entry, run.m_lo, exprp);
        appendWords(entry, span, exprp);
        appendWords(entry, run.m_hi, exprp);
        lists.m_runs.push_back(entry);
    }

    // Emit one batched metadata list, bounding the size of each call's temporary list.
    void emitValueList(FileLine* fl, AstVar* cpVarp, VCMethod method,
                       const std::vector<std::string>& entries) {
        for (size_t first = 0; first < entries.size(); first += VALUE_LIST_ENTRIES) {
            const size_t end = std::min(entries.size(), first + VALUE_LIST_ENTRIES);
            std::string text = "{" + entries[first];
            for (size_t i = first + 1; i < end; ++i) text += ", " + entries[i];
            m_constructorp->addStmtsp(
                itemCall(fl, cpVarp, method, {ctext(fl, text + "}")})->makeStmt());
        }
    }

    static bool checkCrossRef(const AstCoverCrossRef* refp, const AstCoverCross* crossp) {
        if (refp->name() == crossp->name()) return true;
        refp->v3error("Cross selection "
                      << refp->prettyNameQ() << " may only name its enclosing cross "
                      << crossp->prettyNameQ() << " (IEEE 1800-2023 19.6.1.2).");
        return false;
    }

    static bool checkCrossBinName(const AstCoverCrossBin* binp, std::set<std::string>& names) {
        if (names.emplace(binp->name()).second) return true;
        binp->v3error("Duplicate cross bin " << binp->prettyNameQ()
                                             << " (IEEE 1800-2023 19.6.1).");
        return false;
    }

    // The span of the implicit automatic bin reported as 'name' ('auto_<i>', see
    // createImplicitAutoBins), found without naming each of its bins
    static bool implicitAutoBinSpan(const CoverpointBins& bins, const std::string& name,
                                    BinSpan& span) {
        const std::string prefix = "auto_";
        if (!VString::startsWith(name, prefix)) return false;
        const std::string digits = name.substr(prefix.size());
        const unsigned long index = std::strtoul(digits.c_str(), nullptr, 10);
        // Only the reported spelling names the bin, not e.g. 'auto_01' or 'auto_x'
        if (index >= bins.implicitAuto.count || digits != cvtToStr(index)) return false;
        const uint32_t offset = static_cast<uint32_t>(index);
        span = BinSpan{bins.implicitAuto.first + offset, 1, bins.implicitAuto.declared + offset};
        return true;
    }

    CrossBinsofTarget
    resolveBinsofTarget(const AstCoverBinsof* selectp, const AstCoverCross* crossp,
                        const std::vector<AstVar*>& cpVars,
                        const std::map<std::string, uint32_t>& dimensions) const {
        const auto dim = dimensions.find(selectp->pointp()->name());
        if (dim == dimensions.end()) {
            selectp->v3error("binsof coverpoint "
                             << selectp->pointp()->prettyNameQ() << " is not an item of cross "
                             << crossp->prettyNameQ() << " (IEEE 1800-2023 19.6.1).");
            return {};
        }
        const CoverpointBins& bins = m_cpBins.at(cpVars[dim->second]);
        CrossBinsofTarget target{&bins, dim->second, 0, bins.total};
        if (!selectp->name().empty()) {
            const auto bin = bins.spans.find(selectp->name());
            BinSpan span{0, 0, 0};
            if (bin != bins.spans.end()) {
                span = bin->second;
            } else if (!implicitAutoBinSpan(bins, selectp->name(), span)) {
                selectp->v3error("Cannot find bin " << selectp->prettyNameQ() << " in coverpoint "
                                                    << selectp->pointp()->prettyNameQ()
                                                    << " (IEEE 1800-2023 19.6.1).");
                return {};
            }
            target.m_first = span.first;
            target.m_count = span.count;
            target.m_declaredFirst = span.declared;
            target.m_declaredEnd = span.declared + span.count;
            target.m_sized = span.sized;
        }
        return target;
    }

    bool generateRuntimeSelection(AstNode* nodep, AstCoverCross* crossp, AstVar* cxp,
                                  const std::vector<AstVar*>& cpVars,
                                  const std::map<string, uint32_t>& dimensions) {
        FileLine* const fl = nodep->fileline();
        if (const AstCoverCrossRef* const refp = VN_CAST(nodep, CoverCrossRef)) {
            if (!checkCrossRef(refp, crossp)) return false;
            m_constructorp->addStmtsp(
                itemCall(fl, cxp, VCMethod::COVERGROUP_SELECT_ALL)->makeStmt());
            return true;
        }
        if (const AstCoverCrossSelect* const opp = VN_CAST(nodep, CoverCrossSelect)) {
            if (!generateRuntimeSelection(opp->lhsp(), crossp, cxp, cpVars, dimensions)
                || !generateRuntimeSelection(opp->rhsp(), crossp, cxp, cpVars, dimensions)) {
                return false;
            }
            m_constructorp->addStmtsp(itemCall(fl, cxp,
                                               opp->isOr() ? VCMethod::COVERGROUP_SELECT_OR
                                                           : VCMethod::COVERGROUP_SELECT_AND)
                                          ->makeStmt());
            return true;
        }
        AstCoverBinsof* const selectp = VN_AS(nodep, CoverBinsof);
        const CrossBinsofTarget target = resolveBinsofTarget(selectp, crossp, cpVars, dimensions);
        if (!target.m_binsp) return false;
        const CoverpointBins& bins = *target.m_binsp;
        if (selectp->rangesp() && !bins.exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
            bool valid = true;
            unsupportedCrossRange(selectp, valid);
            return false;
        }
        AstNodeExpr* firstp;
        AstNodeExpr* endp;
        if (target.m_sized < 0) {
            firstp = cnum(fl, target.m_declaredFirst);
            endp = cnum(fl, target.m_declaredEnd);
        } else {  // A sized array, whose bins the coverpoint's construction placed
            AstVar* const cpVarp = cpVars[target.m_dimension];
            const uint32_t sized = static_cast<uint32_t>(target.m_sized);
            firstp = itemCall(fl, cpVarp, VCMethod::COVERGROUP_SIZED_FIRST, {cnum(fl, sized)});
            endp = itemCall(fl, cpVarp, VCMethod::COVERGROUP_SIZED_END, {cnum(fl, sized)});
            firstp->dtypeSetUInt32();
            endp->dtypeSetUInt32();
        }
        m_constructorp->addStmtsp(
            itemCall(fl, cxp, VCMethod::COVERGROUP_SELECT_DIM,
                     {cnum(fl, target.m_dimension), firstp, endp, cnum(fl, selectp->isNegated()),
                      cnum(fl, selectp->rangesp() != nullptr)})
                ->makeStmt());
        for (AstNode* rangep = selectp->rangesp(); rangep; rangep = rangep->nextp()) {
            CrossValueRange range{rangep, resolveWidth(rangep, bins.exprp)};
            if (!resolveValue(rangep, bins.exprp, false, false, range)) {
                bool valid = true;
                unsupportedCrossRange(selectp, valid);
                return false;
            }
            if (crossRangeEmpty(range)) continue;
            m_constructorp->addStmtsp(itemCall(fl, cxp,
                                               bins.exprp->isWide()
                                                   ? VCMethod::COVERGROUP_SELECT_RANGE_W
                                                   : VCMethod::COVERGROUP_SELECT_RANGE,
                                               {newValueConst(fl, range.lo, bins.exprp),
                                                newValueConst(fl, range.hi, bins.exprp)})
                                          ->makeStmt());
        }
        m_constructorp->addStmtsp(
            itemCall(fl, cxp, VCMethod::COVERGROUP_SELECT_DIM_END)->makeStmt());
        return true;
    }

    std::vector<AstCoverCrossBin*>
    generateRuntimeCrossBins(AstCoverCross* crossp, AstVar* cxp,
                             const std::vector<AstVar*>& cpVars,
                             const std::map<string, uint32_t>& dimensions) {
        std::vector<AstCoverCrossBin*> bins;
        std::set<string> names;
        for (AstNode* itemp = crossp->binsp(); itemp; itemp = itemp->nextp()) {
            AstCoverCrossBin* const binp = VN_AS(itemp, CoverCrossBin);
            if (!checkCrossBinName(binp, names)) continue;
            if (!generateRuntimeSelection(binp->selectp(), crossp, cxp, cpVars, dimensions)) {
                continue;
            }
            FileLine* const fl = binp->fileline();
            const bool protect = v3Global.opt.protectIds();
            m_constructorp->addStmtsp(
                itemCall(fl, cxp, VCMethod::COVERGROUP_SELECT_BIN,
                         {ctext(fl, binp->binsType().binSetEnum()),
                          ctext(fl, quoted(VIdProtect::protectWordsIf(binp->name(), protect))),
                          ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), protect))),
                          cnum(fl, fl->lineno()), cnum(fl, fl->firstColumn()),
                          cnum(fl, static_cast<uint32_t>(bins.size()))})
                    ->makeStmt());
            bins.push_back(binp);
        }
        m_constructorp->addStmtsp(
            itemCall(crossp->fileline(), cxp, VCMethod::COVERGROUP_FINALIZE_BINS)->makeStmt());
        return bins;
    }

    static void setCrossSelectionRange(CrossSelection& selection, uint64_t first, uint64_t end) {
        while (first < end) {
            const unsigned bit = first % 64;
            const unsigned bits = std::min<uint64_t>(64 - bit, end - first);
            selection[VL_BITWORD_Q(first)]
                |= (bits == 64 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1) << bit;
            first += bits;
        }
    }

    CrossSelection crossSelection(AstNode* nodep, CrossSelectionContext& ctx) {
        if (const AstCoverCrossRef* const refp = VN_CAST(nodep, CoverCrossRef)) {
            if (!checkCrossRef(refp, ctx.crossp)) {
                ctx.valid = false;
                return {};
            }
            CrossSelection result(
                VL_BITWORD_Q(static_cast<uint64_t>(ctx.tuples) + VL_QUADSIZE - 1), 0);
            setCrossSelectionRange(result, 0, ctx.tuples);
            return result;
        }
        if (AstCoverCrossSelect* const opp = VN_CAST(nodep, CoverCrossSelect)) {
            CrossSelection lhs = crossSelection(opp->lhsp(), ctx);
            const CrossSelection rhs = crossSelection(opp->rhsp(), ctx);
            if (!ctx.valid) return {};
            for (size_t i = 0; i < lhs.size(); ++i) {
                lhs[i] = opp->isOr() ? lhs[i] | rhs[i] : lhs[i] & rhs[i];
            }
            return lhs;
        }
        AstCoverBinsof* const selectp = VN_AS(nodep, CoverBinsof);
        const CrossBinsofTarget target
            = resolveBinsofTarget(selectp, ctx.crossp, ctx.cpVars, ctx.dimensions);
        if (!target.m_binsp) {
            ctx.valid = false;
            return {};
        }
        const CoverpointBins& bins = *target.m_binsp;
        // Coverpoints with sized arrays are runtime points, so feed only runtime crosses
        UASSERT_OBJ(target.m_sized < 0, selectp, "Sized bin array selected by a static cross");
        const std::vector<bool> selected
            = selectCoverpointBins(selectp, bins, target.m_first, target.m_count, ctx.valid);
        if (!ctx.valid) return {};
        CrossSelection result(VL_BITWORD_Q(static_cast<uint64_t>(ctx.tuples) + VL_QUADSIZE - 1),
                              0);
        const uint64_t stride = ctx.strides[target.m_dimension];
        const uint64_t period = stride * bins.total;
        for (uint64_t base = 0; base < ctx.tuples; base += period) {
            for (uint32_t i = 0; i < bins.total;) {
                if (!selected[i]) {
                    ++i;
                    continue;
                }
                const uint32_t begin = i++;
                while (i < bins.total && selected[i]) ++i;
                setCrossSelectionRange(result, base + begin * stride, base + i * stride);
            }
        }
        return result;
    }

    // Size the Cartesian product of the declared Normal bins, with each dimension's flat-index
    // stride.  Live runtime bins only shrink it.  Warns and returns false if it is too large.
    bool crossShape(AstCoverCross* crossp, const std::vector<AstVar*>& cpVars,
                    std::vector<uint32_t>& strides, uint32_t& tuples) const {
        uint64_t product = std::any_of(cpVars.begin(), cpVars.end(),
                                       [this](AstVar* varp) { return !m_cpBins.at(varp).total; })
                               ? 0
                               : 1;
        strides.resize(cpVars.size());
        for (size_t d = cpVars.size(); d > 0; --d) {
            strides[d - 1] = static_cast<uint32_t>(product);
            product *= m_cpBins.at(cpVars[d - 1]).total;
            if (product > UINT32_MAX) {
                crossp->v3warn(COVERIGN,
                               "Unsupported: cross coverage with more than 2^32-1 tuples.");
                return false;
            }
        }
        tuples = static_cast<uint32_t>(product);
        return true;
    }

    CrossLayout resolveCrossLayout(AstCoverCross* crossp, const std::vector<AstVar*>& cpVars,
                                   const std::map<std::string, uint32_t>& dimensions) {
        CrossLayout layout;
        CrossSelectionContext ctx{crossp, cpVars, dimensions, 0, {}};
        if (!crossShape(crossp, cpVars, ctx.strides, ctx.tuples)) {
            layout.valid = false;
            return layout;
        }
        layout.tuples = ctx.tuples;
        CrossSelection occupied;
        CrossSelection excluded;
        std::set<std::string> names;
        for (AstNode* itemp = crossp->binsp(); itemp; itemp = itemp->nextp()) {
            AstCoverCrossBin* const binp = VN_AS(itemp, CoverCrossBin);
            if (!checkCrossBinName(binp, names)) continue;
            ctx.valid = true;
            CrossSelection selection = crossSelection(binp->selectp(), ctx);
            if (!ctx.valid || std::all_of(selection.begin(), selection.end(), [](uint64_t word) {
                    return word == 0;
                })) {
                continue;
            }
            if (occupied.empty()) {
                occupied.resize(selection.size(), 0);
                excluded.resize(selection.size(), 0);
            }
            for (size_t i = 0; i < selection.size(); ++i) {
                occupied[i] |= selection[i];
                if (!binp->binsType().binIsNormal()) excluded[i] |= selection[i];
            }
            layout.bins.push_back({binp, std::move(selection)});
        }
        if (!layout.bins.empty()) {
            // IEEE 1800-2023 19.6.2/19.6.3: exclusions also remove tuples from named
            // bins, independently of declaration order and sampling guards.
            for (ResolvedCrossBin& resolved : layout.bins) {
                for (size_t i = 0; i < resolved.selection.size(); ++i) {
                    if (resolved.binp->binsType().binIsNormal()) {
                        resolved.selection[i] &= ~excluded[i];
                    }
                    if (resolved.selection[i]) ++layout.binWords;
                }
            }
            layout.bins.erase(std::remove_if(layout.bins.begin(), layout.bins.end(),
                                             [](const ResolvedCrossBin& resolved) {
                                                 return std::all_of(
                                                     resolved.selection.begin(),
                                                     resolved.selection.end(),
                                                     [](uint64_t word) { return word == 0; });
                                             }),
                              layout.bins.end());
            layout.autoBins = layout.tuples;
            for (const uint64_t word : occupied) {
                layout.autoBins -= static_cast<uint32_t>(std::bitset<VL_QUADSIZE>{word}.count());
            }
        }
        return layout;
    }

    AstCoverCrossDType* crossDType(FileLine* fl, uint32_t dimensions, const CrossLayout& layout,
                                   bool dynamic = false) {
        const uint32_t bins = static_cast<uint32_t>(layout.bins.size());
        const CrossShape shape{dimensions,      layout.tuples,   bins,
                               layout.autoBins, layout.binWords, dynamic};
        AstCoverCrossDType*& typep = m_cxDTypes[shape];
        if (!typep) {
            typep = new AstCoverCrossDType{
                fl, dimensions, layout.tuples, bins, layout.autoBins, layout.binWords, dynamic};
            v3Global.rootp()->typeTablep()->addTypesp(typep);
        }
        return typep;
    }

    std::vector<AstCoverCrossBin*> generateCrossBins(AstCoverCross* crossp, AstVar* cxVarp,
                                                     const CrossLayout& layout) {
        std::vector<AstCoverCrossBin*> bins;
        for (const ResolvedCrossBin& resolved : layout.bins) {
            AstCoverCrossBin* const binp = resolved.binp;
            const CrossSelection& selection = resolved.selection;
            FileLine* const fl = binp->fileline();
            const bool prot = v3Global.opt.protectIds();
            std::string mask = "{";
            for (size_t i = 0; i < selection.size(); ++i) {
                if (i) mask += ", ";
                mask += std::to_string(selection[i]) + "ULL";
            }
            mask += "}";
            m_constructorp->addStmtsp(
                itemCall(fl, cxVarp, VCMethod::COVERGROUP_ADD_BIN,
                         {ctext(fl, binp->binsType().binSetEnum()), ctext(fl, mask),
                          ctext(fl, quoted(VIdProtect::protectWordsIf(binp->name(), prot))),
                          ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), prot))),
                          cnum(fl, static_cast<uint32_t>(fl->lineno())),
                          cnum(fl, static_cast<uint32_t>(fl->firstColumn()))})
                    ->makeStmt());
            bins.push_back(binp);
        }
        if (!bins.empty()) {
            m_constructorp->addStmtsp(
                itemCall(crossp->fileline(), cxVarp, VCMethod::COVERGROUP_FINALIZE_BINS)
                    ->makeStmt());
        }
        return bins;
    }

    // Route a cross through a VlCoverCross member: emit the member, its constructor init +
    // registration, and the sample() call.  The feeding coverpoints are already generated
    // (their hit lists drive the cross). Each explicit bin adds one configuration call.
    void generateCross(AstCoverCross* crossp) {
        FileLine* const fl = crossp->fileline();
        const bool dynamic = m_runtimeCrosses.count(crossp);
        UINFO(4, "  Generating VlCoverCross member: " << crossp->name());

        if (AstNodeExpr* const iffp = crossp->iffp()) {
            crossp->iffp(
                captureIffToTemp(iffp, "__VcrossIff_" + sanitizeGeneratedName(crossp->name())));
        }

        // Resolve and unlink the coverpoint refs, in dimension order.  Every ref resolves to a
        // known coverpoint (a cross with an unresolvable item was dropped earlier).
        std::vector<AstVar*> cpVars;
        std::map<std::string, uint32_t> dimensions;
        for (AstNode* itemp = crossp->itemsp(); itemp;) {
            AstNode* const nextp = itemp->nextp();
            AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
            const auto it = m_cpVarMap.find(refp->name());
            UASSERT_OBJ(it != m_cpVarMap.end(), crossp, "Cross references an unknown coverpoint");
            dimensions.emplace(refp->name(), static_cast<uint32_t>(cpVars.size()));
            cpVars.push_back(it->second);
            VL_DO_DANGLING(pushDeletep(refp->unlinkFrBack()), refp);
            itemp = nextp;
        }
        const int dims = static_cast<int>(cpVars.size());
        CrossLayout layout;
        if (dynamic) {
            // The runtime sizes the layout from live bins; only check the declared bound here.
            std::vector<uint32_t> strides;
            uint32_t tuples = 0;
            layout.valid = crossShape(crossp, cpVars, strides, tuples);
        } else {
            layout = resolveCrossLayout(crossp, cpVars, dimensions);
        }
        if (!layout.valid) return;

        AstVar* const cxVarp
            = new AstVar{fl, VVarType::MEMBER, "__Vcx_" + crossp->name(),
                         crossDType(fl, static_cast<uint32_t>(dims), layout, dynamic)};
        m_covergroupp->addMembersp(cxVarp);
        m_constructorp->addStmtsp(makeItemCreate(fl, cxVarp,
                                                 dynamic ? VCMethod::COVERGROUP_ADD_CROSS_DYN
                                                         : VCMethod::COVERGROUP_ADD_CROSS));
        generateItemWeight(fl, cxVarp, crossp->optionsp());

        // Constructor: init (after the coverpoints, which generate earlier) then registration.
        // Obfuscate the hierarchy/filename/page under --protect-ids as for coverpoints above.
        const bool prot = v3Global.opt.protectIds();
        const std::string hier
            = VIdProtect::protectWordsIf(m_covergroupName + "." + crossp->name(), prot);
        m_constructorp->addStmtsp(makeCrossCpsCall(
            fl, cpVars,
            itemCall(fl, cxVarp, VCMethod::COVERGROUP_INIT,
                     {ctext(fl, quoted(hier)), cnum(fl, static_cast<uint32_t>(dims)),
                      ctext(fl, "__Vcx_cps"),
                      ctext(fl, quoted(VIdProtect::protectIf(fl->filename(), prot))),
                      cnum(fl, static_cast<uint32_t>(fl->lineno())),
                      cnum(fl, static_cast<uint32_t>(fl->firstColumn()))})));
        const std::vector<AstCoverCrossBin*> bins
            = dynamic ? generateRuntimeCrossBins(crossp, cxVarp, cpVars, dimensions)
                      : generateCrossBins(crossp, cxVarp, layout);
        if (v3Global.opt.coverage()) {
            const std::string page
                = VIdProtect::protectIf("v_covergroup/" + m_covergroupName, prot);
            m_constructorp->addStmtsp(itemCall(fl, cxVarp, VCMethod::COVERGROUP_REGISTER_BINS,
                                               {ctext(fl, "vlSymsp->_vm_contextp__->coveragep()"),
                                                ctext(fl, quoted(page)),
                                                cnum(fl, itemDatabaseWeight(crossp->optionsp())),
                                                cnum(fl, m_cgTypeWeight)})
                                          ->makeStmt());
        }

        // sample(): after all coverpoints have sampled (cross loop runs after coverpoint loop).
        UASSERT_OBJ(m_sampleFuncp, crossp, "sample() CFunc not set for cross");
        // The cross remembers its feeding coverpoints, so sample() needs no cps array;
        // per-bin iff guards still need a temporary array, hence the block form.
        const bool hasIffs
            = std::any_of(bins.begin(), bins.end(),
                          [](const AstCoverCrossBin* binp) { return binp->iffp() != nullptr; });
        AstNodeStmt* const samplep
            = !hasIffs ? static_cast<AstNodeStmt*>(
                             itemCall(fl, cxVarp, VCMethod::COVERGROUP_SAMPLE)->makeStmt())
                       : static_cast<AstNodeStmt*>(makeCrossIffsCall(
                             fl, bins,
                             itemCall(fl, cxVarp, VCMethod::COVERGROUP_SAMPLE_IFFS,
                                      {ctext(fl, "__Vcx_iffs")})));
        if (AstNodeExpr* const iffp = crossp->iffp()) {
            m_sampleFuncp->addStmtsp(new AstIf{fl, iffp->cloneTree(false), samplep});
        } else {
            m_sampleFuncp->addStmtsp(samplep);
        }
    }

    void generateCrossCode(AstCoverCross* crossp) {
        UINFO(4, "  Generating code for cross: " << crossp->name());

        // Non-standard hierarchical/dotted cross item (e.g. 'cross a.b'): an implicit coverpoint
        // over the referenced expression (carried in refp->exprp()).  The grammar already warned
        // NONSTD; implicit coverpoints are not yet implemented, so generate no sampling code for
        // this cross.  When support is added the implicit coverpoint should be synthesized
        // upstream (V3LinkParse) as a real AstCoverpoint so it flows through the normal coverpoint
        // path - by here coverpoint lowering has already run.
        for (AstNode* itemp = crossp->itemsp(); itemp; itemp = itemp->nextp()) {
            const AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
            if (refp->exprp()) {
                refp->v3warn(COVERIGN,
                             "Unsupported: cross of hierarchical reference (implicit coverpoint)");
                return;
            }
        }

        // A cross naming a bare variable (implicit coverpoint, which Verilator does not
        // synthesize) is dropped entirely with a COVERIGN warning -- it produces no coverage
        // either way -- but only this cross is dropped; its sibling crosses are still generated
        // and the real coverpoints it referenced remain as independent coverpoints.
        if (m_droppedCrosses.count(crossp)) {
            for (AstNode* itemp = crossp->itemsp(); itemp; itemp = itemp->nextp()) {
                const AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
                if (m_coverpointMap.find(refp->name()) == m_coverpointMap.end()) {
                    refp->v3warn(COVERIGN, "Unsupported: cross of "
                                               << refp->prettyNameQ()
                                               << " which is not a coverpoint (implicit "
                                                  "coverpoint)");
                    break;
                }
            }
            return;
        }

        // Every cross that isn't dropped routes through a VlCoverCross member.
        generateCross(crossp);
    }

    AstNodeExpr* buildBinCondition(AstCoverBin* binp, AstNodeExpr* exprp) {
        // Get the range list from the bin
        AstNode* const rangep = binp->rangesp();
        if (!rangep) return nullptr;

        // Integral values resolve to the coverpoint's type, as its runtime metadata does
        const bool integral = exprp->dtypep()->skipRefp()->isIntegralOrPacked();
        // No value form of a wildcard bin is allowed on a real coverpoint (IEEE 1800-2023 19.5.4)
        if (binp->isWildcard() && !integral) return wildcardTypeError(binp, exprp);

        // Build condition by OR-ing all ranges together
        AstNodeExpr* fullCondp = nullptr;

        for (AstNode* currRangep = rangep; currRangep; currRangep = currRangep->nextp()) {
            AstNodeExpr* rangeCondp = nullptr;
            currRangep = V3Const::constifyEdit(currRangep);

            if (AstInsideRange* irp = VN_CAST(currRangep, InsideRange)) {
                AstNodeExpr* const minExprp = irp->lhsp();
                AstNodeExpr* const maxExprp = irp->rhsp();
                AstConst* const minConstp = VN_CAST(minExprp, Const);
                AstConst* const maxConstp = VN_CAST(maxExprp, Const);
                const bool loUnbounded = VN_IS(minExprp, Unbounded);
                const bool hiUnbounded = VN_IS(maxExprp, Unbounded);
                if (loUnbounded || hiUnbounded) {
                    // Open-ended range: '$' is the coverpoint domain min/max, so the
                    // range reduces to a single inequality (e.g. {[10:$]} -> expr >= 10).
                    AstConst* const boundp = hiUnbounded ? minConstp : maxConstp;
                    if (loUnbounded && hiUnbounded) {
                        rangeCondp = new AstConst{irp->fileline(), AstConst::BitTrue{}};
                    } else if (!boundp) {
                        irp->v3error("Non-constant expression in bin range; "
                                     "range bounds must be constants (IEEE 1800-2023 19.5)");
                        if (fullCondp) VL_DO_DANGLING(pushDeletep(fullCondp), fullCondp);
                        return nullptr;
                    } else if (boundp->num().isFourState()) {
                        irp->v3error("Four-state (x/z) value in bin range bound; "
                                     "range bounds must be two-state constants");
                        if (fullCondp) VL_DO_DANGLING(pushDeletep(fullCondp), fullCondp);
                        return nullptr;
                    } else if (integral) {
                        rangeCondp = buildValueCondition(binp, exprp, irp);
                    } else {
                        rangeCondp = makeOpenRangeCondition(irp->fileline(), exprp, boundp,
                                                            /*isLowerBound=*/hiUnbounded);
                    }
                } else if (!minConstp || !maxConstp) {
                    irp->v3error("Non-constant expression in bin range; "
                                 "range bounds must be constants (IEEE 1800-2023 19.5)");
                    if (fullCondp) VL_DO_DANGLING(pushDeletep(fullCondp), fullCondp);
                    return nullptr;
                } else if (minConstp->num().isFourState() || maxConstp->num().isFourState()) {
                    irp->v3error("Four-state (x/z) value in bin range bound; "
                                 "range bounds must be two-state constants");
                    if (fullCondp) VL_DO_DANGLING(pushDeletep(fullCondp), fullCondp);
                    return nullptr;
                } else if (integral) {
                    rangeCondp = buildValueCondition(binp, exprp, irp);
                } else {
                    rangeCondp = makeRangeCondition(irp->fileline(), exprp, minExprp, maxExprp);
                }
            } else if (AstConst* constp = VN_CAST(currRangep, Const)) {
                rangeCondp = buildValueCondition(binp, exprp, constp);
            } else {
                currRangep->v3error("Non-constant expression in bin range; values must be "
                                    "constants (IEEE 1800-2023 19.5)");
                if (fullCondp) VL_DO_DANGLING(pushDeletep(fullCondp), fullCondp);
                return nullptr;
            }

            UASSERT_OBJ(rangeCondp, binp, "rangeCondp is null after building range condition");
            fullCondp
                = fullCondp ? new AstOr{binp->fileline(), fullCondp, rangeCondp} : rangeCondp;
        }

        return fullCondp;
    }

    // Wildcard bits have no meaning for a non-integral coverpoint.
    static AstNodeExpr* wildcardTypeError(AstCoverBin* binp, AstNodeExpr* exprp) {
        const AstNodeDType* const dtypep = exprp->dtypep()->skipRefp();
        exprp->v3error("Cannot use a wildcard bin on a coverpoint of type "
                       << dtypep->prettyDTypeNameQ() << " (IEEE 1800-2023 19.5.4).\n"
                       << exprp->warnContextPrimary() << '\n'
                       << binp->warnOther() << "... Location of wildcard bin\n"
                       << binp->warnContextSecondary());
        return new AstConst{binp->fileline(), AstConst::BitFalse{}};
    }

    // Match one bin value, range, or wildcard pattern.  Integral coverpoints first resolve the
    // value to their type (IEEE 1800-2023 19.5.7).  Non-owning: clones what it uses.
    AstNodeExpr* buildValueCondition(AstCoverBin* binp, AstNodeExpr* exprp, AstNode* valuep) {
        FileLine* const fl = valuep->fileline();
        if (!exprp->dtypep()->skipRefp()->isIntegralOrPacked()) {
            return new AstEq{fl, exprp->cloneTree(false),
                             VN_AS(valuep, NodeExpr)->cloneTree(false)};
        }
        CrossValueRange range{valuep, resolveWidth(valuep, exprp)};
        if (!resolveValue(valuep, exprp, true, binp->isWildcard(), range)) {
            valuep->v3warn(E_UNSUPPORTED,
                           "Unsupported: non-integral value in a coverage bin of an "
                           "integral coverpoint.");
            return new AstConst{fl, AstConst::BitFalse{}};
        }
        if (crossRangeEmpty(range)) return new AstConst{fl, AstConst::BitFalse{}};
        AstConst* const lop = newValueConst(fl, range.lo, exprp);
        AstConst* const hip = newValueConst(fl, range.hi, exprp);
        AstNodeExpr* condp = nullptr;
        if (lop->num().isCaseEq(hip->num())) {
            condp = new AstEq{fl, exprp->cloneTree(false), lop};
        } else {
            condp = makeRangeCondition(fl, exprp, lop, hip);
            VL_DO_DANGLING(pushDeletep(lop), lop);
        }
        VL_DO_DANGLING(pushDeletep(hip), hip);
        if (!range.wildcard) return condp;
        // Match the pattern's value bits within the source-value bounds.
        V3Number mask{valuep, exprp->width()};
        V3Number value{valuep, exprp->width()};
        mask.opBitsNonXZ(range.pattern);
        value.opBitsOne(range.pattern);
        AstConst* const maskConstp = newValueConst(fl, mask, exprp);
        AstConst* const valueConstp = newValueConst(fl, value, exprp);
        AstNodeExpr* const exprMasked = new AstAnd{fl, exprp->cloneTree(false), maskConstp};
        AstNodeExpr* const valueMasked = new AstAnd{fl, valueConstp, maskConstp->cloneTree(false)};
        return new AstLogAnd{fl, condp, new AstEq{fl, exprMasked, valueMasked}};
    }

    void generateCoverageComputationCode() {
        UINFO(4, "  Generating coverage computation code");

        // Invalidate cache: addMembersp() calls in generateCoverpointCode/generateCrossCode
        // have added new members since the last scan, so clear before re-querying.
        m_memberMap.clear();

        // get_inst_coverage(): the average of the coverpoints and crosses, weighted by their
        // option.weight (IEEE 1800-2023 19.11).  The instance node holds their runtimes.  With
        // the instances merged, get_coverage() instead, unless option.get_inst_coverage
        // (Table 19-1).
        AstFunc* const getInstCoveragep
            = VN_AS(m_memberMap.findMember(m_covergroupp, "get_inst_coverage"), Func);
        FileLine* const instFl = getInstCoveragep->fileline();
        AstCMethodHard* const instCallp = instanceCall(instFl, VCMethod::COVERGROUP_COVERAGE);
        instCallp->dtypeSetDouble();
        AstNodeExpr* instValuep = instCallp;
        if (m_cgMayMerge) {
            AstNodeExpr* const mergedp = new AstLogAnd{
                instFl, newOptionSel(instFl, optionVar(true), "merge_instances", VAccess::READ),
                new AstLogNot{instFl, newOptionSel(instFl, optionVar(false), "get_inst_coverage",
                                                   VAccess::READ)}};
            instValuep = new AstCond{instFl, mergedp, typeCoverageCall(instFl), instCallp};
        }
        getInstCoveragep->addStmtsp(new AstAssign{
            instFl, new AstVarRef{instFl, VN_AS(getInstCoveragep->fvarp(), Var), VAccess::WRITE},
            instValuep});

        // get_coverage(): the average of the covergroup's instances, weighted by their
        // option.weight, or with type_option.merge_instances, the coverage of the union of their
        // bins (IEEE 1800-2023 19.11.3).  Static, so the registry finds the instances.
        AstFunc* const getCoveragep
            = VN_AS(m_memberMap.findMember(m_covergroupp, "get_coverage"), Func);
        FileLine* const typeFl = getCoveragep->fileline();
        getCoveragep->addStmtsp(new AstAssign{
            typeFl, new AstVarRef{typeFl, VN_AS(getCoveragep->fvarp(), Var), VAccess::WRITE},
            typeCoverageCall(typeFl)});
    }

    // The registry call computing the covergroup's type coverage, per its type options
    AstCMethodHard* typeCoverageCall(FileLine* fl) {
        AstCExpr* const registryp = ctext(fl, "vlSymsp->_vm_contextp__->covergroupRegistryp()");
        registryp->dtypeSetVoid();  // Opaque receiver; only ever the 'fromp' of the call below
        AstCMethodHard* const callp
            = new AstCMethodHard{fl, registryp, VCMethod::COVERGROUP_TYPE_COVERAGE};
        callp->addPinsp(ctext(fl, quoted(covergroupProtectedName())));
        callp->addPinsp(newOptionSel(fl, optionVar(true), "weight", VAccess::READ));
        callp->addPinsp(newOptionSel(fl, optionVar(true), "merge_instances", VAccess::READ));
        callp->addPinsp(fileLineDebug(m_covergroupp->fileline()));
        callp->usePtr(true);
        callp->dtypeSetDouble();
        return callp;
    }

    // VISITORS
    static bool isEnclosingInstanceVar(const AstVar* varp) {
        return varp->isClassMember() && !varp->lifetime().isStatic() && !varp->isParam();
    }

    void rewriteThisRef(AstThisRef* refp, AstVar* handleVarp) {
        const AstClassRefDType* const refDTypep
            = VN_CAST(refp->dtypep()->skipRefp(), ClassRefDType);
        UASSERT_OBJ(refDTypep && refDTypep->classp() == m_covergroupp, refp,
                    "Unexpected this reference in embedded covergroup");
        AstNodeExpr* const newp = new AstVarRef{refp->fileline(), handleVarp, VAccess::READ};
        refp->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(refp), refp);
    }

    void rewriteVarRef(AstVarRef* refp, AstVar* handleVarp) {
        FileLine* const fl = refp->fileline();
        AstMemberSel* const selp
            = new AstMemberSel{fl, new AstVarRef{fl, handleVarp, VAccess::READ}, refp->varp()};
        selp->access(refp->access());
        refp->replaceWith(selp);
        VL_DO_DANGLING(pushDeletep(refp), refp);
    }

    void rewriteFuncRef(AstFuncRef* refp, AstVar* handleVarp) {
        FileLine* const fl = refp->fileline();
        AstArg* const argsp = refp->argsp() ? refp->argsp()->unlinkFrBackWithNext() : nullptr;
        AstMethodCall* const callp = new AstMethodCall{
            fl, new AstVarRef{fl, handleVarp, VAccess::READ}, refp->name(), argsp};
        callp->taskp(refp->taskp());
        callp->dtypeFrom(refp);
        refp->replaceWith(callp);
        VL_DO_DANGLING(pushDeletep(refp), refp);
    }

    // True if funcp is an instance method of the enclosing class or one of its bases
    bool isEnclosingInstanceFunc(const AstNodeFTask* funcp) const {
        if (!funcp->classMethod() || funcp->isStatic()) return false;
        return AstClass::isClassExtendedFrom(m_enclosingClassp, VN_AS(funcp->aboveLoopp(), Class));
    }

    bool isEmbeddedCovergroupVar(const AstVar* varp) const {
        if (!varp || !varp->isClassMember() || varp->isDeclTyped()) return false;
        const AstClassRefDType* const refp = VN_CAST(varp->dtypep()->skipRefp(), ClassRefDType);
        return refp && refp->classp() == m_covergroupp;
    }

    AstVar* findEmbeddedCovergroupVar() const {
        if (!m_enclosingClassp) return nullptr;
        for (AstNode* itemp = m_enclosingClassp->membersp(); itemp; itemp = itemp->nextp()) {
            if (AstVar* const varp = VN_CAST(itemp, Var)) {
                if (isEmbeddedCovergroupVar(varp)) return varp;
            }
        }
        // V3LinkParse always creates an implicit variable for an embedded covergroup.
        return nullptr;  // LCOV_EXCL_LINE
    }

    std::vector<AstNodeAssign*> findCovergroupConstructions() {
        std::vector<AstNodeAssign*> foundps;
        if (!m_embeddedVarp) return foundps;
        AstFunc* const enclosingNewp
            = VN_CAST(m_memberMap.findMember(m_enclosingClassp, "new"), Func);
        if (!enclosingNewp) return foundps;
        enclosingNewp->foreach([&](AstNodeAssign* asgnp) {
            const AstNew* const newp = VN_CAST(asgnp->rhsp(), New);
            const AstVarRef* const lhsRefp = VN_CAST(asgnp->lhsp(), VarRef);
            if (!newp || !lhsRefp || lhsRefp->varp() != m_embeddedVarp) return;
            const AstClassRefDType* const refp = VN_CAST(newp->dtypep(), ClassRefDType);
            if (refp && refp->classp() == m_covergroupp) foundps.push_back(asgnp);
        });
        return foundps;
    }

    std::set<const AstVar*> enclosingInstanceVars() const {
        std::set<const AstVar*> vars;
        if (m_enclosingClassp) {
            m_enclosingClassp->foreachMember([&](AstClass* const, AstVar* const varp) {
                if (isEnclosingInstanceVar(varp)) vars.insert(varp);
            });
        }
        return vars;
    }

    bool hasEnclosingEventRef(AstCovergroup* cgp) const {
        if (!m_embeddedVarp || !cgp->eventp()) return false;
        const std::set<const AstVar*> enclosingVars = enclosingInstanceVars();
        bool found = false;
        cgp->eventp()->foreach([&](AstVarRef* refp) {
            if (enclosingVars.count(refp->varp())) found = true;
        });
        return found;
    }

    static bool parseEmbeddedEventExpr(AstNodeExpr* exprp, AstVar*& baseVarp,
                                       AstVar*& memberVarp) {
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            baseVarp = refp->varp();
            memberVarp = nullptr;
            return true;
        }
        AstMemberSel* const selp = VN_CAST(exprp, MemberSel);
        if (!selp) return false;
        AstVarRef* const baseRefp = VN_CAST(selp->fromp(), VarRef);
        if (!baseRefp) return false;
        baseVarp = baseRefp->varp();
        memberVarp = selp->varp();
        return true;
    }

    bool isEventLvalue(AstNodeExpr* exprp, const EmbeddedEventTrigger& trigger) const {
        if (AstSel* const selp = VN_CAST(exprp, Sel)) exprp = selp->fromp();
        AstVar* baseVarp = nullptr;
        AstVar* memberVarp = nullptr;
        if (!parseEmbeddedEventExpr(exprp, baseVarp, memberVarp)) return false;
        return baseVarp == trigger.baseVarp && memberVarp == trigger.memberVarp;
    }

    AstNodeExpr* newEventRead(FileLine* fl, const EmbeddedEventTrigger& trigger) const {
        AstNodeExpr* const basep = new AstVarRef{fl, trigger.baseVarp, VAccess::READ};
        if (!trigger.memberVarp) return basep;
        AstMemberSel* const selp = new AstMemberSel{fl, basep, trigger.memberVarp};
        selp->access(VAccess::READ);
        return selp;
    }

    string eventPrevName(const EmbeddedEventTrigger& trigger, size_t triggerIndex) const {
        string name = "__Vcg_prev_" + m_embeddedVarp->name() + "_" + std::to_string(triggerIndex)
                      + "_" + trigger.baseVarp->name();
        if (trigger.memberVarp) name += "_" + trigger.memberVarp->name();
        return name;
    }

    AstNodeExpr* newEmbeddedVarNonNull(FileLine* fl) const {
        return new AstNeq{fl, new AstVarRef{fl, m_embeddedVarp, VAccess::READ},
                          new AstConst{fl, AstConst::Null{}}};
    }

    AstNodeStmt* newSampleStmt(FileLine* fl) const {
        AstMethodCall* const callp = new AstMethodCall{
            fl, new AstVarRef{fl, m_embeddedVarp, VAccess::READ}, "sample", nullptr};
        callp->taskp(m_sampleFuncp);
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }

    void installEmbeddedEventFork(AstSenTree* eventp,
                                  const std::vector<AstNodeAssign*>& constructps) {
        // IEEE 1800-2023 19.3 samples coverpoints whenever their clocking event occurs. A
        // per-instance event cannot use V3Active's static sensitivity path, so spawn
        // 'fork forever begin @(event); cg.sample(); end join_none' after each construction.
        for (AstNodeAssign* const constructp : constructps) {
            FileLine* const fl = constructp->fileline();
            AstLoop* const loopp = new AstLoop{fl};
            loopp->addStmtsp(new AstEventControl{fl, eventp->cloneTree(false), nullptr});
            loopp->addStmtsp(new AstIf{fl, newEmbeddedVarNonNull(fl), newSampleStmt(fl)});
            AstFork* const forkp = new AstFork{fl, VJoinType::JOIN_NONE};
            forkp->immediateStart(true);
            forkp->addForksp(new AstBegin{fl, "", loopp, true});
            constructp->addNextHere(forkp);
        }
        VL_DO_DANGLING(pushDeletep(eventp), eventp);
    }

    AstNodeExpr* newEventReadyCondition(FileLine* fl, const EmbeddedEventTrigger& trigger) const {
        AstNodeExpr* const curp = newEventRead(fl, trigger);
        AstNodeExpr* const prevp = new AstVarRef{fl, trigger.prevVarp, VAccess::READ};
        AstNodeExpr* edgep = nullptr;
        // IEEE 1800-2023 9.4.2 detects edge-qualified events only on the expression's LSB,
        // while an implicit change event observes the complete expression.
        if (trigger.edgeType == VEdgeType::ET_POSEDGE) {
            edgep = new AstSel{fl, new AstAnd{fl, curp, new AstNot{fl, prevp}}, 0, 1};
        } else if (trigger.edgeType == VEdgeType::ET_NEGEDGE) {
            edgep = new AstSel{fl, new AstAnd{fl, new AstNot{fl, curp}, prevp}, 0, 1};
        } else if (trigger.edgeType == VEdgeType::ET_BOTHEDGE) {
            edgep = new AstSel{fl, new AstXor{fl, curp, prevp}, 0, 1};
        } else {
            edgep = new AstNeq{fl, curp, prevp};
        }
        return new AstLogAnd{fl, newEmbeddedVarNonNull(fl), edgep};
    }

    std::vector<EmbeddedEventTrigger> collectEmbeddedEventTriggers(AstCovergroup* cgp) {
        std::vector<EmbeddedEventTrigger> triggers;
        const std::set<const AstVar*> enclosingVars = enclosingInstanceVars();
        for (AstNode* senp = cgp->eventp()->sensesp(); senp; senp = senp->nextp()) {
            AstSenItem* const itemp = VN_AS(senp, SenItem);
            AstVar* baseVarp = nullptr;
            AstVar* memberVarp = nullptr;
            if (!parseEmbeddedEventExpr(itemp->sensp(), baseVarp, memberVarp)
                || !enclosingVars.count(baseVarp)) {
                return {};
            }
            triggers.emplace_back(itemp->fileline(), baseVarp, memberVarp, itemp->edgeType());
        }
        return triggers;
    }

    void installEmbeddedEventTriggers(std::vector<EmbeddedEventTrigger>& triggers,
                                      const std::vector<AstNodeAssign*>& constructps) {
        // Without --timing, approximate a per-instance event by sampling after assignments
        // within the enclosing class. External writes and exact scheduling cannot be observed.
        if (constructps.empty()) return;
        for (size_t triggerIndex = 0; triggerIndex < triggers.size(); ++triggerIndex) {
            EmbeddedEventTrigger& trigger = triggers[triggerIndex];
            std::vector<AstNodeAssign*> assignps;
            m_enclosingClassp->foreach([&](AstNodeAssign* asgnp) {
                if (isEventLvalue(asgnp->lhsp(), trigger)) assignps.push_back(asgnp);
            });
            if (assignps.empty()) {
                trigger.eventFl->v3warn(
                    COVERIGN, "Unsupported: 'covergroup' clocking event signal has no assignment "
                              "within the enclosing class; no coverage sampled. Use --timing for "
                              "full support.");
                continue;
            }
            AstNodeDType* const dtypep
                = trigger.memberVarp ? trigger.memberVarp->dtypep() : trigger.baseVarp->dtypep();
            AstVar* const prevVarp = new AstVar{trigger.eventFl, VVarType::MEMBER,
                                                eventPrevName(trigger, triggerIndex), dtypep};
            m_enclosingClassp->addMembersp(prevVarp);
            trigger.prevVarp = prevVarp;
            for (AstNodeAssign* const asgnp : assignps) {
                FileLine* const fl = asgnp->fileline();
                AstIf* const ifp
                    = new AstIf{fl, newEventReadyCondition(fl, trigger), newSampleStmt(fl)};
                ifp->addNextHere(new AstAssign{fl,
                                               new AstVarRef{fl, trigger.prevVarp, VAccess::WRITE},
                                               newEventRead(fl, trigger)});
                asgnp->addNextHere(ifp);
            }
        }
    }

    void deleteCoverageItems() {
        for (AstCoverpoint* const cpp : m_coverpoints) {
            VL_DO_DANGLING(pushDeletep(cpp->unlinkFrBack()), cpp);
        }
        for (AstCoverCross* const crossp : m_coverCrosses) {
            VL_DO_DANGLING(pushDeletep(crossp->unlinkFrBack()), crossp);
        }
        // Options not lowered: the covergroup was not processed
        for (AstCgOptionAssign* const optp : m_cgOptions) {
            VL_DO_DANGLING(pushDeletep(optp->unlinkFrBack()), optp);
        }
        m_cgOptions.clear();
    }

    class FormalRefVisitor final : public VNVisitor {
        const std::map<const AstVar*, AstVar*>& m_replacements;

        void visit(AstVarRef* nodep) override {
            const auto it = m_replacements.find(nodep->varp());
            if (it == m_replacements.end()) return;
            nodep->varp(it->second);
        }
        void visit(AstNode* nodep) override { iterateChildren(nodep); }

    public:
        explicit FormalRefVisitor(const std::map<const AstVar*, AstVar*>& replacements)
            : m_replacements{replacements} {}
        void scan(AstNode* nodep) { iterate(nodep); }
    };

    void validateCovergroupExpressions() {
        std::set<const AstVar*> sampleMembers;
        std::set<const AstVar*> constructorRefMembers;
        for (AstNode* stmtp = m_constructorp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp || !varp->isIO() || (!varp->isRef() && !varp->isConstRef())) continue;
            const AstVar* const memberp
                = VN_CAST(m_memberMap.findMember(m_covergroupp, varp->name()), Var);
            UASSERT_OBJ(memberp && memberp->isClassMember(), varp,
                        "Covergroup constructor argument missing persistent member");
            constructorRefMembers.insert(varp);
            constructorRefMembers.insert(memberp);
        }
        for (AstNode* stmtp = m_sampleFuncp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            const AstVar* const varp = VN_CAST(stmtp, Var);
            if (!varp || !varp->isIO()) continue;
            const AstVar* const memberp
                = VN_CAST(m_memberMap.findMember(m_covergroupp, varp->name()), Var);
            UASSERT_OBJ(memberp && memberp->isClassMember(), varp,
                        "Covergroup sample argument missing persistent member");
            sampleMembers.insert(memberp);
        }
        CovergroupExprValidVisitor{sampleMembers, constructorRefMembers}.scan(m_constructorp);
    }

    void rebindFormalRefs() {
        std::map<const AstVar*, AstVar*> replacements;
        for (AstNode* stmtp = m_constructorp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (const AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (!varp->isIO()) continue;
                AstVar* const memberp
                    = VN_CAST(m_memberMap.findMember(m_covergroupp, varp->name()), Var);
                UASSERT_OBJ(memberp && memberp->isClassMember(), varp,
                            "Covergroup constructor argument missing persistent member");
                replacements.emplace(varp, memberp);
            }
        }
        size_t expectedBindings = 0;
        for (const auto& pair : replacements) {
            if (pair.first->isRef() || pair.first->isConstRef()) ++expectedBindings;
        }
        size_t rewrittenBindings = 0;
        for (AstNode* stmtp = m_constructorp->stmtsp(); stmtp;) {
            AstNode* const nextp = stmtp->nextp();
            if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
                AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef);
                AstVarRef* const rhsp = VN_CAST(assignp->rhsp(), VarRef);
                if (lhsp && rhsp
                    && (lhsp->varp()->declDirection() == VDirection::REF
                        || lhsp->varp()->declDirection() == VDirection::CONSTREF)) {
                    const auto it = replacements.find(rhsp->varp());
                    UASSERT_OBJ(it != replacements.end() && it->second == lhsp->varp(), assignp,
                                "Unexpected covergroup reference binding assignment");
                    AstCExpr* const bindp = new AstCExpr{assignp->fileline(), ""};
                    bindp->add(lhsp->unlinkFrBack());
                    bindp->add(" = &");
                    bindp->add(rhsp->unlinkFrBack());
                    assignp->replaceWith(bindp->makeStmt());
                    VL_DO_DANGLING(pushDeletep(assignp), assignp);
                    ++rewrittenBindings;
                }
            }
            stmtp = nextp;
        }
        UASSERT_OBJ(rewrittenBindings == expectedBindings, m_constructorp,
                    "Covergroup reference argument missing binding");
        FormalRefVisitor visitor{replacements};
        for (AstCoverpoint* const cpp : m_coverpoints) visitor.scan(cpp);
        for (AstCoverCross* const crossp : m_coverCrosses) visitor.scan(crossp);
    }

    AstVarRef* installEnclosingBackPointer(const std::vector<AstNodeAssign*>& constructps) {
        // Simple-case support for embedded covergroups (IEEE 1800-2023 19.4) whose
        // coverpoints reference members of the enclosing class ("Class members can be used
        // in coverpoint expressions").  The covergroup is lowered into a sibling class with
        // no implicit handle to the enclosing object, so such references would emit
        // uncompilable C++.  Add an explicit back-pointer member to the enclosing instance,
        // route member references through it, and pass it into the constructor so
        // coverage initialization can read enclosing members. Returns an invalid
        // reference if an outer class member cannot be reached; otherwise returns an empty result.
        if (!m_enclosingClassp) return nullptr;  // Offending refs require an enclosing class

        AstVarRef* invalidp = nullptr;
        AstNode* offenderp = nullptr;
        std::set<const AstVar*> ownVars;
        for (AstNode* itemp = m_covergroupp->membersp(); itemp; itemp = itemp->nextp()) {
            if (const AstVar* const varp = VN_CAST(itemp, Var)) ownVars.insert(varp);
        }
        const std::set<const AstVar*> enclosingVars = enclosingInstanceVars();
        std::vector<AstVarRef*> refsToRewrite;
        std::vector<AstThisRef*> thisRefsToRewrite;
        std::vector<AstFuncRef*> funcRefsToRewrite;
        const auto scan = [&](AstNode* rootp) {
            rootp->foreach([&](AstVarRef* refp) {
                if (invalidp) return;
                const AstVar* const varp = refp->varp();
                if (!isEnclosingInstanceVar(varp) || ownVars.count(varp)) return;
                if (!enclosingVars.count(varp)) {
                    invalidp = refp;
                    return;
                }
                refsToRewrite.push_back(refp);
                if (!offenderp) offenderp = refp;
            });
            if (invalidp) return;
            rootp->foreach([&](AstThisRef* refp) {
                const AstClassRefDType* const refDTypep
                    = VN_CAST(refp->dtypep()->skipRefp(), ClassRefDType);
                if (refDTypep && refDTypep->classp() == m_covergroupp) {
                    thisRefsToRewrite.push_back(refp);
                    if (!offenderp) offenderp = refp;
                }
            });
            rootp->foreach([&](AstFuncRef* refp) {
                if (!isEnclosingInstanceFunc(refp->taskp())) return;
                funcRefsToRewrite.push_back(refp);
                if (!offenderp) offenderp = refp;
            });
        };
        for (AstCoverpoint* const cpp : m_coverpoints) scan(cpp);
        for (AstCoverCross* const crossp : m_coverCrosses) scan(crossp);
        for (AstCgOptionAssign* const optp : m_cgOptions) scan(optp);
        if (invalidp || !offenderp) return invalidp;

        UASSERT_OBJ(m_embeddedVarp, m_covergroupp, "Embedded covergroup variable not found");
        // Commit: add the back-pointer member, rewrite the references, initialize the handle.
        FileLine* const fl = m_covergroupp->fileline();
        AstClassRefDType* const enclDTypep = new AstClassRefDType{fl, m_enclosingClassp, nullptr};
        enclDTypep->rawPointer(true);
        v3Global.rootp()->typeTablep()->addTypesp(enclDTypep);
        AstVar* const handleVarp
            = new AstVar{fl, VVarType::MEMBER, "__Vcg_enclosingp", enclDTypep};
        m_covergroupp->addMembersp(handleVarp);
        AstVar* const argumentp = new AstVar{fl, VVarType::BLOCKTEMP, "__Vcg_parentp", enclDTypep};
        argumentp->direction(VDirection::INPUT);
        argumentp->declDirection(VDirection::INPUT);
        argumentp->funcLocal(true);
        argumentp->noReset(true);
        argumentp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_constructorp->addStmtsp(argumentp);
        m_constructorp->stmtsp()->addHereThisAsNext(
            new AstAssign{fl, memberRef(fl, handleVarp, VAccess::WRITE),
                          new AstVarRef{fl, argumentp, VAccess::READ}});

        // Route each enclosing-member reference through the back-pointer: 'm' -> 'h.m'.
        for (AstVarRef* const refp : refsToRewrite) { rewriteVarRef(refp, handleVarp); }
        for (AstThisRef* const refp : thisRefsToRewrite) { rewriteThisRef(refp, handleVarp); }
        for (AstFuncRef* const refp : funcRefsToRewrite) { rewriteFuncRef(refp, handleVarp); }

        // Append a named hidden argument to preserve positional and defaulted user arguments.
        for (AstNodeAssign* const constructp : constructps) {
            FileLine* const cfl = constructp->fileline();
            AstCExpr* const thisp = new AstCExpr{cfl, "this"};
            thisp->dtypep(enclDTypep);
            VN_AS(constructp->rhsp(), New)->addArgsp(new AstArg{cfl, argumentp->name(), thisp});
        }
        return nullptr;
    }

    void visit(AstClass* nodep) override {
        UINFO(9, "Visiting class: " << nodep->name() << " isCovergroup=" << nodep->isCovergroup());
        if (nodep->isCovergroup()) {
            VL_RESTORER(m_covergroupp);
            VL_RESTORER(m_embeddedVarp);
            VL_RESTORER(m_sampleFuncp);
            VL_RESTORER(m_constructorp);
            VL_RESTORER_CLEAR(m_coverpoints);
            VL_RESTORER_CLEAR(m_coverpointMap);
            VL_RESTORER_CLEAR(m_coverCrosses);
            VL_RESTORER_CLEAR(m_cgOptions);
            VL_RESTORER_CLEAR(m_covergroupName);
            m_covergroupp = nodep;
            m_embeddedVarp = findEmbeddedCovergroupVar();
            m_covergroupName = covergroupTypeName();
            m_sampleFuncp = nullptr;
            m_constructorp = nullptr;
            std::vector<EmbeddedEventTrigger> embeddedEventTriggers;
            AstSenTree* embeddedEventForkp = nullptr;

            // Extract and store the clocking event from AstCovergroup node
            // The parser creates this node to preserve the event information
            bool hasUnsupportedEvent = false;
            for (AstNode* itemp = nodep->membersp(); itemp;) {
                AstNode* const nextp = itemp->nextp();
                if (AstCovergroup* const cgp = VN_CAST(itemp, Covergroup)) {
                    // Store the event in the global map for V3Active to retrieve later
                    // V3LinkParse only creates this sentinel AstCovergroup node when a clocking
                    // event exists, so cgp->eventp() is always non-null here.
                    UASSERT_OBJ(cgp->eventp(), cgp,
                                "Sentinel AstCovergroup in class must have non-null eventp");
                    if (hasEnclosingEventRef(cgp)) {
                        UASSERT_OBJ(m_embeddedVarp, cgp,
                                    "Embedded covergroup event has no instance variable");
                        if (v3Global.opt.timing().isSetTrue()) {
                            embeddedEventForkp = cgp->eventp()->unlinkFrBack();
                        } else {
                            embeddedEventTriggers = collectEmbeddedEventTriggers(cgp);
                            if (embeddedEventTriggers.empty()) {
                                cgp->v3warn(COVERIGN,
                                            "Unsupported: 'covergroup' clocking event on complex "
                                            "member expression; use --timing for full support.");
                                hasUnsupportedEvent = true;
                            }
                        }
                        VL_DO_DANGLING(pushDeletep(cgp->unlinkFrBack()), cgp);
                        itemp = nextp;
                        continue;
                    }
                    // V3Active handles events that do not depend on an enclosing instance.
                    UINFO(4, "Keeping covergroup event node for V3Active: " << nodep->name());
                    itemp = nextp;
                    continue;
                }
                itemp = nextp;
            }

            // Find the sample() method and constructor
            m_sampleFuncp = VN_CAST(m_memberMap.findMember(nodep, "sample"), Func);
            // V3LinkParse always synthesizes a sample() method for every covergroup, and the
            // sampling-code generation below dereferences m_sampleFuncp unconditionally.
            UASSERT_OBJ(m_sampleFuncp, nodep, "Covergroup missing synthesized sample() method");
            m_sampleFuncp->isCovergroupSample(true);
            m_constructorp = VN_CAST(m_memberMap.findMember(nodep, "new"), Func);
            UINFO(9, "Found sample() method: " << (m_sampleFuncp ? "yes" : "no"));
            UINFO(9, "Found constructor: " << (m_constructorp ? "yes" : "no"));

            // If covergroup has unsupported clocking event, skip processing it
            // but still clean up coverpoints so they don't reach downstream passes
            if (hasUnsupportedEvent) {
                iterateChildren(nodep);
                validateCovergroupExpressions();
                rebindFormalRefs();
                deleteCoverageItems();
                if (embeddedEventForkp) {
                    VL_DO_DANGLING(pushDeletep(embeddedEventForkp), embeddedEventForkp);
                }
                return;
            }

            iterateChildren(nodep);
            validateCovergroupExpressions();
            rebindFormalRefs();
            const std::vector<AstNodeAssign*> constructps = findCovergroupConstructions();

            // Embedded covergroups (IEEE 1800-2023 19.4): coverpoints, iff expressions, and
            // crosses may reference members of the enclosing class. The covergroup is lowered
            // into a sibling class with no implicit handle to the enclosing instance. Install
            // an explicit back-pointer and route the references through it.
            if (AstVarRef* const invalidp = installEnclosingBackPointer(constructps)) {
                invalidp->v3error("Non-static member "
                                  << invalidp->varp()->prettyNameQ()
                                  << " of an outer class requires an explicit "
                                     "object handle (IEEE 1800-2023 8.23).");
                deleteCoverageItems();
                if (embeddedEventForkp) {
                    VL_DO_DANGLING(pushDeletep(embeddedEventForkp), embeddedEventForkp);
                }
                return;
            }
            installEmbeddedEventTriggers(embeddedEventTriggers, constructps);
            if (embeddedEventForkp) installEmbeddedEventFork(embeddedEventForkp, constructps);
            processCovergroup();
            // Remove lowered coverpoints/crosses from the class - they have been
            // fully translated into C++ code and must not reach downstream passes
            deleteCoverageItems();
        } else {
            // Track the lexically enclosing class so a nested covergroup can resolve
            // references to the enclosing object's members (installEnclosingBackPointer).
            VL_RESTORER(m_enclosingClassp);
            m_enclosingClassp = nodep;
            iterateChildren(nodep);
        }
    }

    void visit(AstCoverpoint* nodep) override {
        UINFO(9, "Found coverpoint: " << nodep->name());
        m_coverpoints.push_back(nodep);
        m_coverpointMap.emplace(nodep->name(), nodep);
        iterateChildren(nodep);
    }

    void visit(AstCoverCross* nodep) override {
        UINFO(9, "Found cross: " << nodep->name());
        m_coverCrosses.push_back(nodep);
        iterateChildren(nodep);
    }

    // V3Width leaves only the covergroup-level options lowerCovergroupOptions() stores
    void visit(AstCgOptionAssign* nodep) override { m_cgOptions.push_back(nodep); }

    // A package, interface, or module, so the design unit declaring the classes within
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_unitp);
        m_unitp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    FunctionalCoverageVisitor(AstNetlist* nodep,
                              const std::set<const AstVar*>& mergeableTypeOptions)
        : m_mergeableTypeOptions{mergeableTypeOptions} {
        iterate(nodep);
    }
    ~FunctionalCoverageVisitor() override = default;
};

//######################################################################
// Functional coverage class functions

void V3Covergroup::covergroup(AstNetlist* nodep) {
    UINFO(4, __FUNCTION__ << ": ");
    const CovergroupAssignValidVisitor validVisitor{nodep};
    if (!validVisitor.valid()) V3Error::abortIfErrors();
    {  // Destruct before checking
        FunctionalCoverageVisitor{nodep, validVisitor.mergeableTypeOptions()};
    }
    V3Global::dumpCheckGlobalTree("coveragefunc", 0, dumpTreeEitherLevel() >= 3);
}
