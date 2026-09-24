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

#include <bitset>
#include <cmath>
#include <deque>
#include <set>
#include <tuple>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Embedded covergroup assignment validation

class CovergroupAssignValidVisitor final : public VNVisitorConst {
    VMemberMap m_memberMap;
    std::map<const AstVar*, const AstNodeFTask*>
        m_constructors;  // Implicit instance -> constructor
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
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    explicit CovergroupAssignValidVisitor(AstNetlist* nodep) {
        // Uses can precede their enclosing class in the tree.
        iterateConst(nodep);
        m_collecting = false;
        if (!m_constructors.empty()) iterateConst(nodep);
    }
    bool valid() const { return m_valid; }
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
// Functional coverage visitor

class FunctionalCoverageVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //  AstCoverpoint::user1p()  -> AstVar*.  Previous-value variable for transition bins
    const VNUser1InUse m_inuser1;

    // STATE
    std::set<AstCoverpoint*>
        m_runtimePoints;  // Points needing value metadata and live-bin mapping
    std::set<AstCoverCross*> m_runtimeCrosses;  // Crosses over finalized live-bin dimensions
    std::map<AstVar*, AstVar*> m_excludedVars;  // Sample-time state-exclusion flags
    AstClass* m_covergroupp = nullptr;  // Current covergroup being processed
    AstClass* m_enclosingClassp = nullptr;  // Class lexically enclosing the covergroup, if any
    AstVar* m_embeddedVarp = nullptr;  // Embedded covergroup member of m_enclosingClassp, if any
    AstFunc* m_sampleFuncp = nullptr;  // Current sample() function
    AstFunc* m_constructorp = nullptr;  // Current constructor
    std::vector<AstCoverpoint*> m_coverpoints;  // Coverpoints in current covergroup
    std::map<std::string, AstCoverpoint*> m_coverpointMap;  // Name -> coverpoint for fast lookup
    std::vector<AstCoverCross*> m_coverCrosses;  // Cross coverage items in current covergroup
    std::vector<AstCgOptionAssign*> m_cgOptions;  // Covergroup-level weights, before lowering

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
    // Bins of one declaration whose values are computed rather than listed: bin k covers
    // [lo + k * stride, lo + (k + 1) * stride - 1], and the last bin extends to hi.  An array bin
    // element is a run of single-value bins; automatic bins partition the coverpoint domain.
    // Bounds are coverpoint values at runWidth(), sign-extended like a CrossValueRange's.
    struct BinRun final {
        uint32_t count;  // Number of bins
        V3Number lo;  // Lowest value of the first bin
        V3Number stride;  // Number of values of each bin but the last
        V3Number hi;  // Highest value of the last bin
        bool empty = false;  // A single bin without a value of the coverpoint type
        uint32_t declared = 0;  // Runtime index of the first bin, once generated
        BinRun(AstNode* nodep, int width, uint32_t count)
            : count{count}
            , lo{nodep, width}
            , stride{nodep, width, 1}
            , hi{nodep, width} {}
    };
    struct BinRuns final {
        std::vector<BinRun> runs;  // Runs of an array or automatic bins declaration, in order
        uint32_t count = 0;  // Bins across all runs
        bool unsupported = false;  // Too many bins, or invalid: the declaration is ignored
    };
    struct CrossBinValues final {
        AstCoverBin* binp;  // Declaration owning this Normal bin
        AstNodeExpr* valuep;  // Individual array-bin value, or nullptr for a scalar bin
        const BinRun* runp = nullptr;  // Run computing the bin's values, if any
        uint32_t element = 0;  // Index of the bin within runp
    };
    struct BinSpan final {
        uint32_t first;  // First Normal index of the bin declaration
        uint32_t count;  // Number of Normal bins of the declaration
        uint32_t declared;  // First runtime bin index, across all bin kinds
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

    // 'option.weight' or 'type_option.weight', per optionVarp
    AstStructSel* newWeightSel(FileLine* fl, AstVar* optionVarp, VAccess access) {
        const AstMemberDType* const memberp = VN_AS(
            m_memberMap.findMember(optionVarp->dtypep()->skipRefp(), "weight"), MemberDType);
        UASSERT_OBJ(memberp, optionVarp, "Coverage option structure missing 'weight'");
        AstNodeExpr* const fromp = optionVarp->lifetime().isStatic()
                                       ? new AstVarRef{fl, optionVarp, access}
                                       : memberRef(fl, optionVarp, access);
        AstStructSel* const selp = new AstStructSel{fl, fromp, "weight"};
        selp->dtypep(memberp->subDTypep()->skipRefToEnump());
        selp->didWidth(true);
        return selp;
    }

    // Store the covergroup-level weights (IEEE 1800-2023 19.7) where SystemVerilog and the
    // runtime read them.  option.weight is evaluated by the constructor, as are the other
    // instance options; type_option.weight is constant, and initializes the static member.
    void lowerCovergroupOptions() {
        for (AstCgOptionAssign* const optp : m_cgOptions) {
            UASSERT_OBJ(optp->optType() == VCoverOptionType::WEIGHT, optp,
                        "Unexpected covergroup option reaching V3Covergroup");
            FileLine* const fl = optp->fileline();
            AstAssign* const assignp = new AstAssign{
                fl, newWeightSel(fl, optionVar(optp->typeOption()), VAccess::WRITE),
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
    }

    // Configure an item's option.weight, its weight in instance coverage (IEEE 1800-2023
    // 19.11).  type_option.weight only weighs type coverage merged over the instances, which
    // type_option.merge_instances would select; without that, it has no effect.
    void generateItemWeight(FileLine* fl, AstVar* itemVarp, AstNode* optionsp) {
        for (AstNode* nodep = optionsp; nodep; nodep = nodep->nextp()) {
            const AstCoverOption* const optp = VN_AS(nodep, CoverOption);
            if (!(optp->optType() == VCoverOptionType::WEIGHT) || optp->typeOption()) continue;
            m_constructorp->addStmtsp(
                itemCall(fl, itemVarp, VCMethod::COVERGROUP_WEIGHT,
                         {optp->valuep()->cloneTree(false), fileLineDebug(optp->fileline())})
                    ->makeStmt());
        }
    }

    void processCovergroup() {
        UINFO(4, "Processing covergroup: " << m_covergroupp->name() << " with "
                                           << m_coverpoints.size() << " coverpoints and "
                                           << m_coverCrosses.size() << " crosses");

        m_crossedCpNames.clear();
        m_cpVarMap.clear();
        m_cpBins.clear();
        m_runtimePoints.clear();
        m_runtimeCrosses.clear();
        m_excludedVars.clear();
        m_droppedCrosses.clear();
        m_cgInstVarp = nullptr;

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
            if (!cpp->exprp()->dtypep()->skipRefp()->isIntegralOrPacked()) continue;
            // Bins without values leave the report (IEEE 1800-2023 19.11.1), exclusions or not.
            if (!coverpointHasStateExclusions(cpp) && !coverpointHasEmptyBins(cpp)) continue;
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

    // Limit on the bins of one array or automatic bins declaration, and on the automatic bins
    // of option.auto_bin_max, like other simulators'; it guards against hangs from e.g. signed
    // underflow.  Such bins generate as runs, whose code size does not depend on their number.
    static constexpr int COVER_BINS_LIMIT = 0x100000;
    // Limit on the values of one array bins declaration of a real coverpoint, which generates
    // a comparison per value (see extractArrayValues)
    static constexpr int COVER_REAL_BINS_LIMIT = 1024;
    static constexpr size_t VALUE_LIST_ENTRIES = 256;  // Metadata entries per constructor call

    // The number of bins requested by a valid 'bins auto[N]', or 0
    static uint32_t autoBinsRequested(const AstCoverBin* binp) {
        const AstConst* const constp = VN_CAST(binp->arraySizep(), Const);
        if (!constp || constp->toSInt() <= 0 || constp->toSInt() > COVER_BINS_LIMIT) return 0;
        return constp->toUInt();
    }

    // True for a 'bins auto[N]' declaration, or the implicit automatic bins of a coverpoint
    static bool isAutoBins(const AstCoverBin* binp) {
        return binp->binsType() == VCoverBinsType::BINS_AUTO
               || binp->binsType() == VCoverBinsType::BINS_AUTO_IMPLICIT;
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
            } else if (constp->toSInt() <= 0) {
                cbinp->v3error("Automatic bins array size must be >= 1, got " << constp->toSInt());
            } else if (constp->toSInt() > COVER_BINS_LIMIT) {
                cbinp->v3error("Automatic bins array size of "
                               << constp->toSInt() << " exceeds limit of " << COVER_BINS_LIMIT);
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
        if (count > static_cast<uint32_t>(COVER_BINS_LIMIT)) {
            coverpointp->v3warn(COVERIGN, "Unsupported: more than "
                                              << COVER_BINS_LIMIT
                                              << " automatic bins from 'option.auto_bin_max'; "
                                                 "using "
                                              << COVER_BINS_LIMIT << ".");
            count = COVER_BINS_LIMIT;
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

    AstNodeExpr* applyCoverpointIffCondition(AstCoverpoint* coverpointp, FileLine* fl,
                                             AstNodeExpr* condp) {
        if (AstNodeExpr* const iffp = coverpointp->iffp()) {
            UINFO(6, "      Adding iff condition");
            condp = new AstAnd{fl, iffp->cloneTree(false), condp};
        }
        return condp;
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

        AstVar* const valueVarp = new AstVar{
            coverpointp->fileline(), VVarType::BLOCKTEMP,
            "__VcpValue_" + sanitizeGeneratedName(coverpointp->name()), exprp->dtypep()};
        valueVarp->funcLocal(true);
        m_sampleFuncp->addStmtsp(valueVarp);
        exprp->unlinkFrBack();
        m_sampleFuncp->addStmtsp(new AstAssign{
            coverpointp->fileline(),
            new AstVarRef{coverpointp->fileline(), valueVarp, VAccess::WRITE}, exprp});
        coverpointp->exprp(new AstVarRef{coverpointp->fileline(), valueVarp, VAccess::READ});
        exprp = coverpointp->exprp();

        // Every coverpoint routes through the VlCoverpoint runtime.  Transition coverpoints are
        // included: their per-value matching is still generated as a state machine in sample()
        // (see generateCoverpoint), but the bin hit is recorded in the runtime bin
        // rather than a bare counter.
        generateCoverpoint(coverpointp, exprp, atLeastValue);
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

    // True if a Normal state bin, or an array-bin element, has no value of the coverpoint's
    // type (IEEE 1800-2023 19.5.7).  Array ranges enumerate in-type values, so cannot vanish.
    static bool coverpointHasEmptyBins(const AstCoverpoint* coverpointp) {
        AstNodeExpr* const exprp = coverpointp->exprp();
        for (AstNode* nodep = coverpointp->binsp(); nodep; nodep = nodep->nextp()) {
            const AstCoverBin* const binp = VN_AS(nodep, CoverBin);
            if (!binp->binsType().binIsNormal() || binp->transp() || !binp->rangesp()) continue;
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

    std::string covergroupProtectedName() const {
        return VIdProtect::protectWordsIf(m_covergroupp->name(), v3Global.opt.protectIds());
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
                                    + quoted(covergroupProtectedName()) + ")")},
                     /*usePtr=*/false)
                ->makeStmt());
        // The node reads option.weight in place, so procedural assignments take effect
        AstCExpr* const weightAddrp = new AstCExpr{fl, "&"};
        weightAddrp->add(newWeightSel(fl, optionVar(false), VAccess::READ));
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
        // Signed values resolve sign-extended, not as unsigned intervals
        bool exact = !exprp->isSigned();
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
    // constant value or range; false if not, after reporting it.
    static bool checkArrayBinElement(AstCoverBin* arrayBinp, AstNode* rangep) {
        if (const AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
            const AstConst* const minp = VN_CAST(irp->lhsp(), Const);
            const AstConst* const maxp = VN_CAST(irp->rhsp(), Const);
            if ((!minp && !VN_IS(irp->lhsp(), Unbounded))
                || (!maxp && !VN_IS(irp->rhsp(), Unbounded))) {
                arrayBinp->v3error("Non-constant expression in array bins range; "
                                   "range bounds must be constants (IEEE 1800-2023 19.5)");
                return false;
            }
            if ((minp && minp->num().isFourState()) || (maxp && maxp->num().isFourState())) {
                arrayBinp->v3error("Four-state (x/z) value in array bins range bound; "
                                   "range bounds must be two-state constants");
                return false;
            }
        } else if (!VN_IS(rangep, Const)) {
            arrayBinp->v3error("Non-constant expression in array bins value list; "
                               "values must be constants (IEEE 1800-2023 19.5)");
            return false;
        }
        return true;
    }

    // Individual equality targets of an array bin (bins b[] = {values/ranges}) of a real
    // coverpoint, in order; integral coverpoints generate array bins as runs (see arrayBinRuns).
    // An open-ended bound ('$', AstUnbounded) resolves to the coverpoint domain: '[lo:$]'
    // covers [lo:maxVal] and '[$:hi]' covers [0:hi].  One target is produced per value; ranges
    // whose resolved size would exceed COVER_REAL_BINS_LIMIT (e.g. an open '[lo:$]') are
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
                if (span >= static_cast<uint64_t>(COVER_REAL_BINS_LIMIT)
                    || values.size() + span + 1 > static_cast<uint64_t>(COVER_REAL_BINS_LIMIT)) {
                    arrayBinp->v3warn(COVERIGN, "Unsupported: array 'bins' of a real coverpoint "
                                                "covering more than "
                                                    << COVER_REAL_BINS_LIMIT
                                                    << " values; bin ignored.");
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
            = width < 31 ? std::min<uint32_t>(uint32_t{1} << width, requested) : requested;
        BinRun run{binp, arithmeticWidth, count};
        V3Number total{binp, arithmeticWidth};
        total.setBit(width, 1);
        run.stride.opDiv(total, V3Number{binp, arithmeticWidth, count});
        const CrossValueRange domain
            = crossValueDomain(binp, width, exprp->isSigned(), arithmeticWidth);
        run.lo = domain.lo;
        run.hi = domain.hi;
        out.runs.push_back(std::move(run));
        out.count = count;
        return true;
    }

    // The elements of an array bin (bins b[] = {values/ranges}), in order, as runs of
    // single-value bins.  A range holds the values of the coverpoint type it contains (IEEE
    // 1800-2023 19.5.7), while a singleton names a bin even without such a value.  Errors on a
    // non-constant element.  More than COVER_BINS_LIMIT bins (e.g. an open '[lo:$]' range over a
    // wide coverpoint) are unsupported -- emits COVERIGN, and sets unsupported.
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
            run.empty = empty;
            uint32_t count = 1;
            if (!empty) {
                run.lo.opAssign(range.lo);
                run.hi.opAssign(range.hi);
                V3Number span{rangep, width};
                span.opSub(run.hi, run.lo);
                count = span.mostSetBitP1() > 31 ? UINT32_MAX : span.toUInt() + 1;
            }
            if (count > static_cast<uint32_t>(COVER_BINS_LIMIT) - out.count) {
                arrayBinp->v3warn(COVERIGN, "Unsupported: array 'bins' covering more than "
                                                << COVER_BINS_LIMIT
                                                << " values (e.g. an open '[lo:$]' range over "
                                                   "a wide coverpoint); bin ignored");
                out.runs.clear();
                out.count = 0;
                out.unsupported = true;
                return out;
            }
            run.count = count;
            out.count += count;
            out.runs.push_back(std::move(run));
        }
        return out;
    }

    // The runs of an automatic bins declaration, or of an array bin of an integral coverpoint.
    // False for other bins, which do not generate as runs.
    bool binRunsFor(AstCoverBin* binp, AstNodeExpr* exprp, BinRuns& out) {
        if (isAutoBins(binp)) {
            if (!autoBinRuns(binp, exprp, out)) out.unsupported = true;
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
    // runtime bin index is 'declared'
    AstNodeStmt* makeNamer(AstVar* cpVarp, AstCoverBin* binp, int count, uint32_t declared,
                           const std::vector<AstNodeExpr*>& values = {}) {
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
        int idx;  // bin index within that coverpoint
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

    void emitConvHitIf(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                       AstNodeExpr* idxp, AstNodeExpr* condp) {
        FileLine* const fl = binp->fileline();
        AstNode* actionp = makeRuntimeBinHit(fl, cpVarp, idxp, binp->binsType().binIsNormal());
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            actionp->addNext(makeIllegalBinAction(fl, "Illegal bin " + binp->prettyNameQ()
                                                          + " hit in coverpoint "
                                                          + coverpointp->prettyNameQ()));
        }
        if (binp->iffp()) condp = new AstLogAnd{fl, binp->iffp()->cloneTree(false), condp};
        const auto excluded = m_excludedVars.find(cpVarp);
        if (excluded != m_excludedVars.end() && !binp->transp()
            && (binp->binsType().binIsNormal()
                || binp->binsType() == VCoverBinsType::BINS_DEFAULT)) {
            condp = new AstLogAnd{
                fl, new AstNot{fl, new AstVarRef{fl, excluded->second, VAccess::READ}}, condp};
        }
        AstNodeExpr* const guardedp = applyCoverpointIffCondition(coverpointp, fl, condp);
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for coverpoint");
        m_sampleFuncp->addStmtsp(new AstIf{fl, guardedp, actionp, nullptr});
    }

    // The runtime index of the bin of a run holding the coverpoint value, which is in the run:
    // declared + (value - lo) / stride, capped at the last bin, which holds any remainder.
    static AstNodeExpr* runBinIndex(FileLine* fl, AstNodeExpr* exprp, const BinRun& run) {
        if (run.count == 1) return cnum(fl, run.declared);
        const int width = exprp->width();
        // A run spans at most 2^width values, so offsets in it are unsigned width-bit numbers
        AstNodeExpr* indexp
            = new AstSub{fl, exprp->cloneTree(false), newValueConst(fl, run.lo, exprp)};
        indexp->dtypeSetLogicSized(width, VSigning::UNSIGNED);
        V3Number stride{fl, width, 0};
        stride.opAssign(run.stride);
        if (stride.countOnes() != 1) {
            indexp = new AstDiv{fl, indexp, new AstConst{fl, stride}};
        } else if (!stride.isEqOne()) {
            indexp = new AstShiftR{fl, indexp, new AstConst{fl, stride.mostSetBitP1() - 1}};
        }
        // Compare the run's values with those of count bins of stride values, without overflow
        const int extWidth = run.lo.width() + 1;
        V3Number lo{fl, extWidth, 0};
        lo.opExtendS(run.lo, run.lo.width());
        V3Number span{fl, extWidth, 0};
        span.opExtendS(run.hi, run.hi.width());
        span.opSub(V3Number{span}, lo);
        V3Number covered{fl, extWidth, 0};
        covered.opAssign(run.stride);
        covered.opMul(V3Number{covered}, V3Number{fl, extWidth, run.count});
        V3Number hasRemainder{fl, 1, 0};
        if (!hasRemainder.opGte(span, covered).isEqZero()) {
            AstConst* const lastp = new AstConst{fl, V3Number{fl, width, run.count - 1}};
            indexp = new AstCond{fl, new AstGt{fl, indexp->cloneTree(false), lastp},
                                 lastp->cloneTree(false), indexp};
        }
        if (width < VL_IDATASIZE) {
            indexp = new AstExtend{fl, indexp, VL_IDATASIZE};
        } else if (width > VL_IDATASIZE) {
            indexp = new AstSel{fl, indexp, 0, VL_IDATASIZE};
        }
        return new AstAdd{fl, cnum(fl, run.declared), indexp};
    }

    // Emit the sample() hit of a run of bins, whose code does not grow with its number of bins:
    //   if (iff && lo <= value && value <= hi) m_cp.incrementBin(<runBinIndex>);
    void emitRunHit(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp,
                    AstNodeExpr* exprp, const BinRun& run) {
        FileLine* const fl = binp->fileline();
        AstConst* const lop = newValueConst(fl, run.lo, exprp);
        AstNodeExpr* condp = nullptr;
        if (run.lo.isCaseEq(run.hi)) {
            condp = new AstEq{fl, exprp->cloneTree(false), lop};
        } else {
            AstConst* const hip = newValueConst(fl, run.hi, exprp);
            condp = makeRangeCondition(fl, exprp, lop, hip);
            VL_DO_DANGLING(pushDeletep(lop), lop);
            VL_DO_DANGLING(pushDeletep(hip), hip);
        }
        emitConvHitIf(coverpointp, binp, cpVarp, runBinIndex(fl, exprp, run), condp);
    }

    // Emit a transition bin's hit action into sample():
    //   if (iff && cond) { m_cp.incrementBin/recordHit(idx); [illegal: $error; $stop] }
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
        AstNodeExpr* const guardedp = applyCoverpointIffCondition(coverpointp, fl, condp);
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for transition bin");
        m_sampleFuncp->addStmtsp(new AstIf{fl, guardedp, actionp, nullptr});
    }

    // Route a coverpoint through a VlCoverpoint member: emit the member, its sample()
    // increments, the constructor configuration (init + namers), and registration.
    void generateCoverpoint(AstCoverpoint* coverpointp, AstNodeExpr* exprp, int atLeastValue) {
        FileLine* const fl = coverpointp->fileline();
        const bool dynamic = m_runtimePoints.count(coverpointp);
        UINFO(4, "  Generating VlCoverpoint member: " << coverpointp->name());

        if (AstNodeExpr* const iffp = coverpointp->iffp()) {
            coverpointp->iffp(
                captureIffToTemp(iffp, "__VcpIff_" + sanitizeGeneratedName(coverpointp->name())));
        }

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
        // coverpoint's sample() contribution (before any incrementBin appends to it).
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
            m_sampleFuncp->addStmtsp(
                new AstAssign{fl, new AstVarRef{fl, excludedp, VAccess::WRITE}, callp});
            m_excludedVars.emplace(cpVarp, excludedp);
        }

        // Walk bins (non-default, then default), assigning sequential indices that match the
        // namer append order; emit sample increments and collect namer statements.
        std::vector<AstNodeStmt*> namerStmts;
        std::vector<AstCoverBin*> defaultBins;
        std::vector<std::tuple<AstCoverBin*, uint32_t, AstNodeExpr*>> metadata;
        std::vector<const BinRun*> runMetadata;
        int idx = 0;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            const int errorsBefore = dynamic ? V3Error::errorCount() : 0;
            if (cbinp->binsType() == VCoverBinsType::BINS_DEFAULT) {
                defaultBins.push_back(cbinp);
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
                const ConvBinTarget tgt{cpVarp, idx, cbinp->binsType().binIsNormal()};
                for (AstNode* sp = cbinp->transp(); sp; sp = sp->nextp())
                    generateSingleTransitionCode(coverpointp, cbinp, exprp, tgt,
                                                 VN_AS(sp, CoverTransSet));
                if (dynamic && V3Error::errorCount() == errorsBefore) {
                    metadata.emplace_back(cbinp, idx, nullptr);
                }
                ++idx;
                continue;
            }
            BinRuns plan;
            if (binRunsFor(cbinp, exprp, plan)) {
                // Array elements and automatic bins generate as runs, so neither sample() nor
                // the constructor grows with their number of bins.
                if (plan.unsupported) continue;  // bin ignored or invalid; reserve no slot
                CoverpointBins& bins = m_cpBins.at(cpVarp);
                const uint32_t firstValue = bins.total;
                const uint32_t firstDeclared = static_cast<uint32_t>(idx);
                namerStmts.push_back(
                    makeNamer(cpVarp, cbinp, static_cast<int>(plan.count), firstDeclared));
                for (BinRun& run : plan.runs) {
                    run.declared = static_cast<uint32_t>(idx);
                    bins.runs.push_back(std::move(run));
                    const BinRun& stored = bins.runs.back();
                    if (bins.crossed && cbinp->binsType().binIsNormal()) {
                        const uint32_t first = firstValue + stored.declared - firstDeclared;
                        for (uint32_t element = 0; element < stored.count; ++element) {
                            bins.values[first + element].runp = &stored;
                            bins.values[first + element].element = element;
                        }
                    }
                    if (!stored.empty) {
                        emitRunHit(coverpointp, cbinp, cpVarp, exprp, stored);
                        if (dynamic && V3Error::errorCount() == errorsBefore) {
                            runMetadata.push_back(&stored);
                        }
                    }
                    idx += static_cast<int>(stored.count);
                }
                continue;
            }
            if (cbinp->isArray()) {  // value array of a real coverpoint: b[0]..b[N-1]
                bool unsupported = false;
                std::vector<AstNodeExpr*> values = extractArrayValues(cbinp, exprp, unsupported);
                if (unsupported) continue;  // bin ignored (COVERIGN emitted); reserve no slot
                namerStmts.push_back(makeNamer(cpVarp, cbinp, static_cast<int>(values.size()),
                                               static_cast<uint32_t>(idx), values));
                for (AstNodeExpr* valuep : values) {
                    // The cross selections of this covergroup still read the value.
                    m_detachedValues.push_back(valuep);
                    emitConvHitIf(coverpointp, cbinp, cpVarp,
                                  cnum(cbinp->fileline(), static_cast<uint32_t>(idx)),
                                  buildValueCondition(cbinp, exprp, valuep));
                    if (dynamic && V3Error::errorCount() == errorsBefore) {
                        metadata.emplace_back(cbinp, idx, valuep);
                    }
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
                    metadata.emplace_back(cbinp, idx, nullptr);
                }
                ++idx;
            }
        }
        for (AstCoverBin* const defBinp : defaultBins) {
            namerStmts.push_back(makeNamer(cpVarp, defBinp, -1, static_cast<uint32_t>(idx)));
            emitConvHitIf(coverpointp, defBinp, cpVarp,
                          cnum(defBinp->fileline(), static_cast<uint32_t>(idx)),
                          buildDefaultCondition(coverpointp, exprp, defBinp->fileline()));
            ++idx;
        }

        // Transition coverpoints track the previous sampled value; update it once at the end of
        // this coverpoint's sample() contribution (the prev var was created on demand by the
        // transition matching above).
        if (coverpointHasTransition(coverpointp)) {
            AstVar* const prevVarp = VN_AS(coverpointp->user1p(), Var);
            m_sampleFuncp->addStmtsp(
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
            = VIdProtect::protectWordsIf(m_covergroupp->name() + "." + coverpointp->name(), prot);
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
            m_constructorp->addStmtsp(
                itemCall(fl, cpVarp, VCMethod::COVERGROUP_VALUE_FINALIZE)->makeStmt());
        }
        if (v3Global.opt.coverage()) {
            const std::string page
                = VIdProtect::protectIf("v_covergroup/" + m_covergroupp->name(), prot);
            m_constructorp->addStmtsp(itemCall(fl, cpVarp, VCMethod::COVERGROUP_REGISTER_BINS,
                                               {ctext(fl, "vlSymsp->_vm_contextp__->coveragep()"),
                                                ctext(fl, quoted(page))})
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

        m_sampleFuncp->addStmtsp(casep);
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
        AstNodeExpr* matchCondp = buildTransitionItemCondition(items[state], exprp);

        // Apply iff condition if present
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            matchCondp = new AstAnd{fl, iffp->cloneTree(false), matchCondp};
        }

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
            AstNodeExpr* restartCondp = buildTransitionItemCondition(items[0], exprp);

            UASSERT_OBJ(restartCondp, items[0],
                        "buildTransitionItemCondition returned nullptr for restart");
            // Apply iff condition
            if (AstNodeExpr* iffp = coverpointp->iffp()) {
                restartCondp = new AstAnd{fl, iffp->cloneTree(false), restartCondp};
            }

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
        const int runw = run.lo.width();
        V3Number offset{nodep, runw};
        offset.opMul(run.stride, V3Number{nodep, runw, element});
        V3Number lo{nodep, runw};
        lo.opAdd(run.lo, offset);
        V3Number hi = run.hi;
        if (element + 1 < run.count) {
            offset.opSub(run.stride, V3Number{nodep, runw, 1});
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
        V3Number span{exprp, run.stride.width(), 0};
        span.opSub(run.stride, V3Number{exprp, run.stride.width(), 1});
        std::string entry = cvtToStr(run.declared) + "U, " + cvtToStr(run.count) + "U";
        appendWords(entry, run.lo, exprp);
        appendWords(entry, span, exprp);
        appendWords(entry, run.hi, exprp);
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
    // createImplicitAutoBins), found without naming each of up to COVER_BINS_LIMIT bins
    static bool implicitAutoBinSpan(const CoverpointBins& bins, const std::string& name,
                                    BinSpan& span) {
        const std::string prefix = "auto_";
        if (name.size() <= prefix.size() || !VString::startsWith(name, prefix)) return false;
        uint32_t index = 0;
        for (size_t i = prefix.size(); i < name.size(); ++i) {
            if (name[i] < '0' || name[i] > '9') return false;
            index = index * 10 + static_cast<uint32_t>(name[i] - '0');
            if (index >= bins.implicitAuto.count) return false;  // Also bounds the digits
        }
        // Only the reported spelling names the bin, not e.g. 'auto_01'
        if (name != prefix + cvtToStr(index)) return false;
        span = BinSpan{bins.implicitAuto.first + index, 1, bins.implicitAuto.declared + index};
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
        m_constructorp->addStmtsp(
            itemCall(fl, cxp, VCMethod::COVERGROUP_SELECT_DIM,
                     {cnum(fl, target.m_dimension), cnum(fl, target.m_declaredFirst),
                      cnum(fl, target.m_declaredEnd), cnum(fl, selectp->isNegated()),
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
            = VIdProtect::protectWordsIf(m_covergroupp->name() + "." + crossp->name(), prot);
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
                = VIdProtect::protectIf("v_covergroup/" + m_covergroupp->name(), prot);
            m_constructorp->addStmtsp(itemCall(fl, cxVarp, VCMethod::COVERGROUP_REGISTER_BINS,
                                               {ctext(fl, "vlSymsp->_vm_contextp__->coveragep()"),
                                                ctext(fl, quoted(page))})
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
        // option.weight (IEEE 1800-2023 19.11).  The instance node holds their runtimes.
        AstFunc* const getInstCoveragep
            = VN_AS(m_memberMap.findMember(m_covergroupp, "get_inst_coverage"), Func);
        FileLine* const instFl = getInstCoveragep->fileline();
        AstCMethodHard* const instCallp = instanceCall(instFl, VCMethod::COVERGROUP_COVERAGE);
        instCallp->dtypeSetDouble();
        getInstCoveragep->addStmtsp(new AstAssign{
            instFl, new AstVarRef{instFl, VN_AS(getInstCoveragep->fvarp(), Var), VAccess::WRITE},
            instCallp});

        // get_coverage(): the average of the covergroup's instances, weighted by their
        // option.weight (IEEE 1800-2023 19.11.3).  Static, so the registry finds the instances.
        AstFunc* const getCoveragep
            = VN_AS(m_memberMap.findMember(m_covergroupp, "get_coverage"), Func);
        FileLine* const typeFl = getCoveragep->fileline();
        AstCExpr* const registryp
            = ctext(typeFl, "vlSymsp->_vm_contextp__->covergroupRegistryp()");
        registryp->dtypeSetVoid();  // Opaque receiver; only ever the 'fromp' of the call below
        AstCMethodHard* const typeCallp
            = new AstCMethodHard{typeFl, registryp, VCMethod::COVERGROUP_TYPE_COVERAGE};
        typeCallp->addPinsp(ctext(typeFl, quoted(covergroupProtectedName())));
        typeCallp->addPinsp(newWeightSel(typeFl, optionVar(true), VAccess::READ));
        typeCallp->addPinsp(fileLineDebug(m_covergroupp->fileline()));
        typeCallp->usePtr(true);
        typeCallp->dtypeSetDouble();
        getCoveragep->addStmtsp(new AstAssign{
            typeFl, new AstVarRef{typeFl, VN_AS(getCoveragep->fvarp(), Var), VAccess::WRITE},
            typeCallp});
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
            m_covergroupp = nodep;
            m_embeddedVarp = findEmbeddedCovergroupVar();
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

    // V3Width leaves only the covergroup-level weights, for lowerCovergroupOptions()
    void visit(AstCgOptionAssign* nodep) override { m_cgOptions.push_back(nodep); }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit FunctionalCoverageVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~FunctionalCoverageVisitor() override = default;
};

//######################################################################
// Functional coverage class functions

void V3Covergroup::covergroup(AstNetlist* nodep) {
    UINFO(4, __FUNCTION__ << ": ");
    if (!CovergroupAssignValidVisitor{nodep}.valid()) V3Error::abortIfErrors();
    { FunctionalCoverageVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragefunc", 0, dumpTreeEitherLevel() >= 3);
}
