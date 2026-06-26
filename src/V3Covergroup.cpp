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
#include "V3MemberMap.h"

#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Functional coverage visitor

class FunctionalCoverageVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //  AstCoverpoint::user1p()  -> AstVar*.  Previous-value variable for transition bins
    const VNUser1InUse m_inuser1;

    // STATE
    AstClass* m_covergroupp = nullptr;  // Current covergroup being processed
    AstFunc* m_sampleFuncp = nullptr;  // Current sample() function
    AstFunc* m_constructorp = nullptr;  // Current constructor
    std::vector<AstCoverpoint*> m_coverpoints;  // Coverpoints in current covergroup
    std::map<std::string, AstCoverpoint*> m_coverpointMap;  // Name -> coverpoint for fast lookup
    std::vector<AstCoverCross*> m_coverCrosses;  // Cross coverage items in current covergroup

    std::set<std::string> m_crossedCpNames;  // Coverpoints referenced by a cross
    std::vector<AstVar*> m_cpVars;  // VlCoverpoint member, one per coverpoint
    std::vector<AstVar*> m_crossVars;  // VlCoverCross member, one per cross
    std::map<std::string, AstVar*> m_cpVarMap;  // Coverpoint name -> its VlCoverpoint member
    std::set<AstCoverCross*>
        m_droppedCrosses;  // Crosses with a bare-variable item: drop (COVERIGN)
    std::map<int, AstCDType*> m_vlCoverpointTypes;  // hit-list bound K -> "VlCoverpointT<K>" type
    AstCDType* m_vlCoverCrossDTypep = nullptr;  // Shared "VlCoverCross" C++ member type

    VMemberMap m_memberMap;  // Member names cached for fast lookup

    // METHODS
    void processCovergroup() {
        UINFO(4, "Processing covergroup: " << m_covergroupp->name() << " with "
                                           << m_coverpoints.size() << " coverpoints and "
                                           << m_coverCrosses.size() << " crosses");

        m_crossedCpNames.clear();
        m_cpVars.clear();
        m_crossVars.clear();
        m_cpVarMap.clear();
        m_droppedCrosses.clear();

        // Scan every cross item to record the coverpoints it references (the cross dimensions)
        // and to flag any cross naming a bare variable -- a would-be implicit coverpoint, which
        // Verilator does not synthesize.  An unresolvable item drops only that one cross (with a
        // COVERIGN in generateCrossCode), leaving the rest of the covergroup intact.
        for (AstCoverCross* crossp : m_coverCrosses) {
            for (AstNode* itemp = crossp->itemsp(); itemp; itemp = itemp->nextp()) {
                const AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
                if (refp->exprp()) continue;  // hierarchical ref: dropped in generateCrossCode
                if (m_coverpointMap.find(refp->name()) == m_coverpointMap.end())
                    m_droppedCrosses.insert(crossp);  // bare variable: drop this cross only
                else
                    m_crossedCpNames.insert(refp->name());
            }
        }

        // For each coverpoint, generate sampling code
        for (AstCoverpoint* cpp : m_coverpoints) generateCoverpointCode(cpp);

        // For each cross, generate sampling code
        for (AstCoverCross* crossp : m_coverCrosses) generateCrossCode(crossp);

        // Generate coverage computation code (even for empty covergroups).  Bin registration
        // with the coverage database is handled per coverpoint/cross by their runtime
        // registerBins() calls (emitted in generateCoverpoint/generateCross).

        // TODO: Generate instance registry infrastructure for static get_coverage()
        // This requires:
        // - Static registry members (t_instances, s_mutex)
        // - registerInstance() / unregisterInstance() methods
        // - Proper C++ emission in EmitC backend
        // For now, get_coverage() returns 0.0 (placeholder)
        generateCoverageComputationCode();
    }

    static constexpr int COVER_BINS_LIMIT
        = 1000;  // Sanity limit to avoid hangs from e.g. signed underflow

    void expandAutomaticBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp) {
        // Find and expand any automatic bins
        AstNode* prevBinp = nullptr;
        for (AstNode* binp = coverpointp->binsp(); binp;) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            AstNode* const nextBinp = binp->nextp();

            if (cbinp->binsType() == VCoverBinsType::BINS_AUTO) {
                UINFO(4, "  Expanding automatic bin: " << cbinp->name());

                // Get array size - must be a constant
                AstNodeExpr* const sizep = cbinp->arraySizep();

                // Evaluate as constant
                const AstConst* constp = VN_CAST(sizep, Const);
                if (!constp) {
                    cbinp->v3error("Automatic bins array size must be a constant");
                    binp = nextBinp;
                    continue;
                }

                const int numBins = constp->toSInt();
                if (numBins <= 0) {
                    cbinp->v3error("Automatic bins array size must be >= 1, got " << numBins);
                    binp = nextBinp;
                    continue;
                }
                if (numBins > COVER_BINS_LIMIT) {
                    cbinp->v3error("Automatic bins array size of "
                                   << numBins << " exceeds limit of " << COVER_BINS_LIMIT);
                    binp = nextBinp;
                    continue;
                }

                // Calculate range division
                const int width = exprp->width();
                const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
                // For width >= 64: (maxVal+1) would overflow; compute binSize without overflow
                const uint64_t binSize
                    = (width < 64) ? ((maxVal + 1) / numBins) : (UINT64_MAX / numBins + 1);

                UINFO(4, "    Width=" << width << " maxVal=" << maxVal << " numBins=" << numBins
                                      << " binSize=" << binSize);

                // Create expanded bins
                for (int i = 0; i < numBins; i++) {
                    const uint64_t lo = static_cast<uint64_t>(i) * binSize;
                    const uint64_t hi = (i == numBins - 1) ? maxVal : ((i + 1) * binSize - 1);

                    // Create constants for range (use setQuad to handle values > 32-bit)
                    V3Number loNum{cbinp->fileline(), width, 0};
                    loNum.setQuad(lo);
                    AstConst* const loConstp = new AstConst{cbinp->fileline(), loNum};
                    V3Number hiNum{cbinp->fileline(), width, 0};
                    hiNum.setQuad(hi);
                    AstConst* const hiConstp = new AstConst{cbinp->fileline(), hiNum};

                    // Create InsideRange [lo:hi]
                    AstInsideRange* const rangep
                        = new AstInsideRange{cbinp->fileline(), loConstp, hiConstp};
                    rangep->dtypeFrom(exprp);  // Set dtype from coverpoint expression

                    // Create new bin
                    const string binName = cbinp->name() + "[" + std::to_string(i) + "]";
                    AstCoverBin* const newBinp
                        = new AstCoverBin{cbinp->fileline(), binName, rangep, false, false};

                    // Insert after previous bin
                    if (prevBinp) {
                        prevBinp->addNext(newBinp);
                    } else {
                        coverpointp->addBinsp(newBinp);
                    }
                    prevBinp = newBinp;
                }

                // Remove the AUTO bin from the list
                VL_DO_DANGLING(pushDeletep(binp->unlinkFrBack()), binp);
            } else {
                prevBinp = binp;
            }

            binp = nextBinp;
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
            AstConst* const constp = VN_CAST(optp->valuep(), Const);
            if (!constp) {
                optp->valuep()->v3warn(COVERIGN, "Ignoring unsupported: non-constant 'option."
                                                     << optp->optionType().ascii()
                                                     << "'; using default value");
                continue;
            }
            if (optp->optionType() == VCoverOptionType::AT_LEAST) {
                atLeastOut = constp->toSInt();
            } else {
                // V3LinkParse only converts at_least/auto_bin_max coverpoint options into
                // AstCoverOption (others are dropped there), so this is the only alternative.
                UASSERT_OBJ(optp->optionType() == VCoverOptionType::AUTO_BIN_MAX, optp,
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

    // Extract individual values from a range expression list, used only to carve values
    // out of implicit auto-bins.  Iterates over all siblings (nextp) in the list, handling
    // AstConst (single value) and AstInsideRange ([lo:hi]); an open-ended bound ('$',
    // AstUnbounded) resolves to the coverpoint domain min (lower) or max (upper, == maxVal).
    void extractValuesFromRange(AstNode* nodep, std::set<uint64_t>& values, uint64_t maxVal) {
        // Cap enumeration so a '$'-bounded or otherwise huge range cannot blow up memory;
        // auto-bins are per-value only for small domains, so a partial set is harmless here.
        constexpr size_t maxEnumerate = 1ULL << 16;
        for (AstNode* np = nodep; np; np = np->nextp()) {
            if (AstConst* constp = VN_CAST(np, Const)) {
                if (constp->num().isFourState())
                    continue;  // wildcard patterns can't be enumerated
                values.insert(constp->toUQuad());
            } else if (AstInsideRange* rangep = VN_CAST(np, InsideRange)) {
                AstNodeExpr* const lhsp = V3Const::constifyEdit(rangep->lhsp());
                AstNodeExpr* const rhsp = V3Const::constifyEdit(rangep->rhsp());
                const bool loUnbounded = VN_IS(lhsp, Unbounded);
                const bool hiUnbounded = VN_IS(rhsp, Unbounded);
                AstConst* const loConstp = VN_CAST(lhsp, Const);
                AstConst* const hiConstp = VN_CAST(rhsp, Const);
                if ((!loConstp && !loUnbounded) || (!hiConstp && !hiUnbounded)) {
                    rangep->v3error("Non-constant expression in bin range; "
                                    "range bounds must be constants");
                    continue;
                }
                if ((loConstp && loConstp->num().isFourState())
                    || (hiConstp && hiConstp->num().isFourState()))
                    continue;
                const uint64_t lo = loUnbounded ? 0 : loConstp->toUQuad();
                const uint64_t hi = hiUnbounded ? maxVal : hiConstp->toUQuad();
                for (uint64_t v = lo; v <= hi; v++) {
                    if (values.size() >= maxEnumerate) break;
                    values.insert(v);
                }
            } else {
                np->v3error("Non-constant expression in bin value list; values must be constants");
            }
        }
    }

    // Single-pass categorization: determine whether any regular (non-ignore/illegal) bins exist
    // and collect the set of excluded values from ignore/illegal bins.
    void categorizeBins(AstCoverpoint* coverpointp, bool& hasRegularOut,
                        std::set<uint64_t>& excludedOut, uint64_t maxVal) {
        hasRegularOut = false;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            const VCoverBinsType btype = cbinp->binsType();
            if (btype == VCoverBinsType::BINS_IGNORE || btype == VCoverBinsType::BINS_ILLEGAL) {
                if (AstNode* rangep = cbinp->rangesp()) {
                    extractValuesFromRange(rangep, excludedOut, maxVal);
                }
            } else {
                hasRegularOut = true;
            }
        }
    }

    // Create implicit automatic bins when coverpoint has no explicit regular bins
    void createImplicitAutoBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp, int autoBinMax) {
        const int width = exprp->width();
        const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);

        // Single pass: check for regular bins and collect excluded values simultaneously.
        // maxVal resolves any '$' (open-ended) bound in ignore_bins/illegal_bins ranges.
        bool hasRegular = false;
        std::set<uint64_t> excluded;
        categorizeBins(coverpointp, hasRegular, excluded, maxVal);

        // If already has regular bins, nothing to do
        if (hasRegular) return;

        UINFO(4, "  Creating implicit automatic bins for coverpoint: " << coverpointp->name());

        const uint64_t numTotalValues = (width >= 64) ? UINT64_MAX : (1ULL << width);
        const uint64_t numValidValues = numTotalValues - excluded.size();

        // Determine number of bins to create (based on non-excluded values)
        int numBins;
        if (numValidValues <= static_cast<uint64_t>(autoBinMax)) {
            // Create one bin per valid value
            numBins = numValidValues;
        } else {
            // Create autoBinMax bins, dividing range
            numBins = autoBinMax;
        }

        UINFO(4, "    Width=" << width << " numTotalValues=" << numTotalValues
                              << " numValidValues=" << numValidValues << " autoBinMax="
                              << autoBinMax << " creating " << numBins << " bins");

        // Strategy: Create bins for each value (if numValidValues <= autoBinMax)
        // or create range bins that avoid excluded values
        if (numValidValues <= static_cast<uint64_t>(autoBinMax)) {
            // Create one bin per valid value
            int binCount = 0;
            for (uint64_t v = 0; v <= maxVal && binCount < numBins; v++) {
                // Skip excluded values
                if (excluded.find(v) != excluded.end()) continue;

                // Create single-value bin
                AstConst* const valConstp = new AstConst{
                    coverpointp->fileline(), V3Number(coverpointp->fileline(), width, v)};
                AstConst* const valConstp2 = new AstConst{
                    coverpointp->fileline(), V3Number(coverpointp->fileline(), width, v)};

                AstInsideRange* const rangep
                    = new AstInsideRange{coverpointp->fileline(), valConstp, valConstp2};
                rangep->dtypeFrom(exprp);

                const string binName = "auto_" + std::to_string(binCount);
                AstCoverBin* const newBinp
                    = new AstCoverBin{coverpointp->fileline(), binName, rangep, false, false};

                coverpointp->addBinsp(newBinp);
                binCount++;
            }
            UINFO(4, "    Created " << binCount << " single-value automatic bins");
        } else {
            // Create range bins (more complex - need to handle excluded values in ranges)
            // For simplicity, create bins and let excluded values not match any bin
            const uint64_t binSize = (maxVal + 1) / numBins;

            for (int i = 0; i < numBins; i++) {
                const uint64_t lo = i * binSize;
                const uint64_t hi = (i == numBins - 1) ? maxVal : ((i + 1) * binSize - 1);

                // Create constants for range
                AstConst* const loConstp = new AstConst{
                    coverpointp->fileline(), V3Number(coverpointp->fileline(), width, lo)};
                AstConst* const hiConstp = new AstConst{
                    coverpointp->fileline(), V3Number(coverpointp->fileline(), width, hi)};

                // Create InsideRange [lo:hi]
                AstInsideRange* const rangep
                    = new AstInsideRange{coverpointp->fileline(), loConstp, hiConstp};
                rangep->dtypeFrom(exprp);

                // Create bin name
                const string binName = "auto_" + std::to_string(i);
                AstCoverBin* const newBinp
                    = new AstCoverBin{coverpointp->fileline(), binName, rangep, false, false};

                // Add to coverpoint
                coverpointp->addBinsp(newBinp);
            }

            UINFO(4, "    Created range-based automatic bins");
        }
    }

    // Sanitize generated names to be valid C++ identifiers
    static string sanitizeGeneratedName(string name) {
        std::replace(name.begin(), name.end(), '[', '_');
        std::replace(name.begin(), name.end(), ']', '_');
        return name;
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
        prevVarp->isStatic(false);
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
        stateVarp->isStatic(false);
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
        AstNodeExpr* const exprp = coverpointp->exprp();

        // Expand automatic bins before processing
        expandAutomaticBins(coverpointp, exprp);

        // Extract all coverpoint options in a single pass
        int atLeastValue;
        int autoBinMax;
        extractCoverpointOptions(coverpointp, atLeastValue, autoBinMax);
        UINFO(6, "    Coverpoint at_least = " << atLeastValue << " auto_bin_max = " << autoBinMax);

        // Create implicit automatic bins if no regular bins exist
        createImplicitAutoBins(coverpointp, exprp, autoBinMax);

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

    // True if a coverpoint has any transition bin.  Used to decide whether sample() emits the
    // end-of-sample previous-value update that transition matching needs.
    static bool coverpointHasTransition(AstCoverpoint* coverpointp) {
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            if (VN_AS(binp, CoverBin)->transp()) return true;
        }
        return false;
    }

    // Get (or create) the "VlCoverpointT<K>" member type for hit-list bound K.
    AstCDType* vlCoverpointType(FileLine* fl, int hitBound) {
        const auto it = m_vlCoverpointTypes.find(hitBound);
        if (it != m_vlCoverpointTypes.end()) return it->second;
        AstCDType* const typep
            = new AstCDType{fl, "VlCoverpointT<" + std::to_string(hitBound) + ">"};
        v3Global.rootp()->typeTablep()->addTypesp(typep);
        m_vlCoverpointTypes.emplace(hitBound, typep);
        return typep;
    }

    // Constant bounds of one rangesp() element (an InsideRange or a single Const).
    struct RangeBounds final {
        AstConst* lc = nullptr;  // low-bound const (null iff loUnb)
        AstConst* hc = nullptr;  // high-bound const (null iff hiUnb)
        bool loUnb = false;  // low bound is '$'
        bool hiUnb = false;  // high bound is '$'
    };

    // Decode one rangesp() element into its constant bounds.  Returns false if rp is neither an
    // InsideRange nor a single Const, or if a present bound is non-constant or 4-state.  '$'
    // bounds are flagged (loUnb/hiUnb), not resolved -- the caller applies its own policy.
    // Centralizes the InsideRange/Const/Unbounded decode shared by the hit-list-bound paths.
    static bool constRangeBounds(AstNode* rp, RangeBounds& rb) {
        if (AstInsideRange* const irp = VN_CAST(rp, InsideRange)) {
            rb.loUnb = VN_IS(irp->lhsp(), Unbounded);
            rb.hiUnb = VN_IS(irp->rhsp(), Unbounded);
            rb.lc = VN_CAST(irp->lhsp(), Const);
            rb.hc = VN_CAST(irp->rhsp(), Const);
            if ((!rb.lc && !rb.loUnb) || (!rb.hc && !rb.hiUnb)) return false;
            if ((rb.lc && rb.lc->num().isFourState()) || (rb.hc && rb.hc->num().isFourState()))
                return false;
            return true;
        }
        if (AstConst* const cp = VN_CAST(rp, Const)) {
            if (cp->num().isFourState()) return false;
            rb.lc = rb.hc = cp;
            return true;
        }
        return false;
    }

    // Collect the covered value intervals of a single (non-array) Normal bin.  Returns false
    // if any range isn't a constant/open InsideRange or single Const (e.g. wildcard, non-const).
    static bool extractRangeIntervals(AstCoverBin* cbinp, uint64_t maxVal,
                                      std::vector<std::pair<uint64_t, uint64_t>>& out) {
        if (!cbinp->rangesp()) return false;
        for (AstNode* rp = cbinp->rangesp(); rp; rp = rp->nextp()) {
            RangeBounds rb;
            if (!constRangeBounds(rp, rb)) return false;
            const uint64_t lo = rb.loUnb ? 0 : rb.lc->toUQuad();
            const uint64_t hi = rb.hiUnb ? maxVal : rb.hc->toUQuad();
            if (lo > hi) return false;
            out.emplace_back(lo, hi);
        }
        return true;
    }

    // Append one Normal bin's cross-slot interval-sets to `bins` and bump `slotCount` by the
    // number of cross slots the bin contributes.  Returns false if any part isn't statically
    // enumerable (the caller then falls back to the always-safe Normal-slot count).  A non-array
    // bin is one slot covering the union of its intervals; an array bin contributes one
    // single-value slot per element value (mirroring how it lowers to b[0]..b[N-1]).
    bool appendBinCrossSlots(AstCoverBin* cbinp, uint64_t maxVal,
                             std::vector<std::vector<std::pair<uint64_t, uint64_t>>>& bins,
                             int& slotCount) {
        if (!cbinp->isArray()) {
            ++slotCount;
            std::vector<std::pair<uint64_t, uint64_t>> ivs;
            if (cbinp->isWildcard() || !extractRangeIntervals(cbinp, maxVal, ivs)) return false;
            bins.push_back(std::move(ivs));
            return true;
        }
        // Array bin: each element value is its own single-value Normal bin.  '$'-bounded or
        // non-constant elements can't be enumerated, so they count one slot but lose exactness.
        bool exact = true;
        for (AstNode* rp = cbinp->rangesp(); rp; rp = rp->nextp()) {
            RangeBounds rb;
            if (!constRangeBounds(rp, rb) || rb.loUnb || rb.hiUnb) {
                ++slotCount;
                exact = false;
            } else if (rb.lc == rb.hc) {  // single Const element (lc/hc alias the same node)
                ++slotCount;
                bins.push_back({{rb.lc->toUQuad(), rb.lc->toUQuad()}});
            } else {  // [lo:hi] range: one single-value slot per enumerated value
                for (int64_t v = rb.lc->toSInt(); v <= rb.hc->toSInt(); ++v) {
                    ++slotCount;
                    bins.push_back({{static_cast<uint64_t>(v), static_cast<uint64_t>(v)}});
                }
            }
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
        bool exact = true;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            if (!cbinp->binsType().binIsNormal())
                continue;  // ignore/illegal/default: not hit-listed
            if (!appendBinCrossSlots(cbinp, maxVal, bins, slotCount)) exact = false;
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
    AstVarRef* memberRef(FileLine* fl, AstVar* varp) {
        AstVarRef* const refp = new AstVarRef{fl, varp, VAccess::READ};
        refp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
        return refp;
    }

    // Individual equality targets of an array bin (bins b[] = {values/ranges}), in order.
    // An open-ended bound ('$', AstUnbounded) resolves to the coverpoint domain: '[lo:$]'
    // covers [lo:maxVal] and '[$:hi]' covers [0:hi].  One target is produced per value; a
    // range whose resolved size would exceed COVER_BINS_LIMIT (e.g. an open '[lo:$]' over a
    // wide coverpoint) is unsupported -- emits COVERIGN, sets unsupportedOut, yields nothing.
    std::vector<AstNodeExpr*> extractArrayValues(AstCoverBin* arrayBinp, AstNodeExpr* exprp,
                                                 bool& unsupportedOut) {
        unsupportedOut = false;
        const int width = exprp->width();
        const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
        std::vector<AstNodeExpr*> values;
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstInsideRange* const irp = VN_CAST(rangep, InsideRange)) {
                AstNodeExpr* const lhsp = V3Const::constifyEdit(irp->lhsp());
                AstNodeExpr* const rhsp = V3Const::constifyEdit(irp->rhsp());
                const bool loUnb = VN_IS(lhsp, Unbounded);
                const bool hiUnb = VN_IS(rhsp, Unbounded);
                AstConst* const minp = VN_CAST(lhsp, Const);
                AstConst* const maxp = VN_CAST(rhsp, Const);
                if ((!minp && !loUnb) || (!maxp && !hiUnb)) {
                    arrayBinp->v3error("Non-constant expression in array bins range; "
                                       "range bounds must be constants");
                    return values;
                }
                if ((minp && minp->num().isFourState()) || (maxp && maxp->num().isFourState())) {
                    arrayBinp->v3error("Four-state (x/z) value in array bins range bound; "
                                       "range bounds must be two-state constants");
                    return values;
                }
                const uint64_t lo = loUnb ? 0 : minp->toUQuad();
                const uint64_t hi = hiUnb ? maxVal : maxp->toUQuad();
                if (hi < lo) continue;  // empty range contributes no bins
                // Guard against a '$'-bounded or otherwise huge range exploding the bin count.
                const uint64_t span = hi - lo;  // == valueCount - 1 (no overflow: hi >= lo)
                if (span >= static_cast<uint64_t>(COVER_BINS_LIMIT)
                    || values.size() + span + 1 > static_cast<uint64_t>(COVER_BINS_LIMIT)) {
                    arrayBinp->v3warn(COVERIGN, "Unsupported: array 'bins' covering more than "
                                                    << COVER_BINS_LIMIT
                                                    << " values (e.g. an open '[lo:$]' range over "
                                                       "a wide coverpoint); bin ignored");
                    unsupportedOut = true;
                    for (AstNodeExpr* const vp : values) VL_DO_DANGLING(pushDeletep(vp), vp);
                    values.clear();
                    return values;
                }
                for (uint64_t v = lo; v <= hi; ++v)
                    values.push_back(new AstConst{irp->fileline(), AstConst::WidthedValue{}, width,
                                                  static_cast<uint32_t>(v)});
            } else if (VN_IS(rangep, Const)) {
                values.push_back(VN_AS(rangep->cloneTree(false), NodeExpr));
            } else {
                arrayBinp->v3error("Non-constant expression in array bins value list; "
                                   "values must be constants");
                return values;
            }
        }
        return values;
    }

    // Emit a 'this->m_cp.addSingleNamer/addArrayNamer(...)' statement for one bin
    AstCStmt* makeNamer(AstVar* cpVarp, AstCoverBin* binp, int count) {
        FileLine* const fl = binp->fileline();
        AstCStmt* const cs = new AstCStmt{fl};
        cs->add(memberRef(fl, cpVarp));
        const std::string loc = "\"" + std::string{fl->filename()} + "\", "
                                + std::to_string(fl->lineno()) + ", "
                                + std::to_string(fl->firstColumn()) + ");";
        if (count < 0) {  // single bin
            cs->add(".addSingleNamer(" + std::string{binp->binsType().binSetEnum()} + ", \""
                    + binp->name() + "\", " + loc);
        } else {  // value array bin
            cs->add(".addArrayNamer(" + std::string{binp->binsType().binSetEnum()} + ", "
                    + std::to_string(count) + ", \"" + binp->name() + "\", " + loc);
        }
        return cs;
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
    AstNodeStmt* makeRuntimeBinHit(FileLine* fl, const ConvBinTarget& tgt) {
        AstCStmt* const cs = new AstCStmt{fl};
        cs->add(memberRef(fl, tgt.cpVarp));
        cs->add((tgt.isNormal ? ".incrementBin(" : ".recordHit(") + std::to_string(tgt.idx)
                + ");");
        return cs;
    }

    void emitConvHitIf(AstCoverpoint* coverpointp, AstCoverBin* binp, AstVar* cpVarp, int idx,
                       AstNodeExpr* condp) {
        FileLine* const fl = binp->fileline();
        AstNode* actionp = makeRuntimeBinHit(fl, {cpVarp, idx, binp->binsType().binIsNormal()});
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            actionp->addNext(makeIllegalBinAction(fl, "Illegal bin " + binp->prettyNameQ()
                                                          + " hit in coverpoint "
                                                          + coverpointp->prettyNameQ()));
        }
        AstNodeExpr* const guardedp = applyCoverpointIffCondition(coverpointp, fl, condp);
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set for coverpoint");
        m_sampleFuncp->addStmtsp(new AstIf{fl, guardedp, actionp, nullptr});
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
        UINFO(4, "  Generating VlCoverpoint member: " << coverpointp->name());

        // Size the hit list to the gen-time max bin overlap (1 unless cross-fed with
        // overlapping ranges), so no cross hit is ever dropped and storage is minimal.
        const bool crossFed = m_crossedCpNames.count(coverpointp->name()) != 0;
        const int hitBound = computeHitListBound(coverpointp, exprp, crossFed);
        UINFO(6, "    Hit-list bound (max bin overlap) = " << hitBound);
        AstVar* const cpVarp = new AstVar{fl, VVarType::MEMBER, "__Vcp_" + coverpointp->name(),
                                          vlCoverpointType(fl, hitBound)};
        cpVarp->isStatic(false);
        m_covergroupp->addMembersp(cpVarp);
        m_cpVars.push_back(cpVarp);
        m_cpVarMap[coverpointp->name()] = cpVarp;

        // A cross reads this coverpoint's hit list, so clear it at the start of the
        // coverpoint's sample() contribution (before any incrementBin appends to it).
        if (crossFed) {
            AstCStmt* const clrp = new AstCStmt{fl};
            clrp->add(memberRef(fl, cpVarp));
            clrp->add(".clearHitList();");
            UASSERT_OBJ(m_sampleFuncp, coverpointp, "sample() CFunc not set for clearHitList");
            m_sampleFuncp->addStmtsp(clrp);
        }

        // Walk bins (non-default, then default), assigning sequential indices that match the
        // namer append order; emit sample increments and collect namer statements.
        std::vector<AstCStmt*> namerStmts;
        std::vector<AstCoverBin*> defaultBins;
        int idx = 0;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
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
                namerStmts.push_back(makeNamer(cpVarp, cbinp, -1));
                const ConvBinTarget tgt{cpVarp, idx, cbinp->binsType().binIsNormal()};
                for (AstNode* sp = cbinp->transp(); sp; sp = sp->nextp())
                    generateSingleTransitionCode(coverpointp, cbinp, exprp, tgt,
                                                 VN_AS(sp, CoverTransSet));
                ++idx;
                continue;
            }
            if (cbinp->isArray()) {  // value array: bins b[N] = {...} -> b[0]..b[N-1]
                bool unsupported = false;
                std::vector<AstNodeExpr*> values = extractArrayValues(cbinp, exprp, unsupported);
                if (unsupported) continue;  // bin ignored (COVERIGN emitted); reserve no slot
                namerStmts.push_back(makeNamer(cpVarp, cbinp, static_cast<int>(values.size())));
                for (AstNodeExpr* valuep : values) {
                    // TODO: A 4-state bin value (e.g. bins b[] = {2'b0x}) must match with ===
                    // (AstEqCase) per IEEE 1800-2023 19.5.4. == is equivalent under 2-state sim
                    // (x/z collapse to 0); switch to AstEqCase when 4-state sim support lands.
                    emitConvHitIf(coverpointp, cbinp, cpVarp, idx++,
                                  new AstEq{cbinp->fileline(), exprp->cloneTree(false), valuep});
                }
            } else {
                namerStmts.push_back(makeNamer(cpVarp, cbinp, -1));
                // buildBinCondition is null for 'ignore_bins = default' (no ranges); the bin
                // still gets a reserved slot (recorded, never incremented).
                if (AstNodeExpr* const condp = buildBinCondition(cbinp, exprp))
                    emitConvHitIf(coverpointp, cbinp, cpVarp, idx, condp);
                ++idx;
            }
        }
        for (AstCoverBin* const defBinp : defaultBins) {
            namerStmts.push_back(makeNamer(cpVarp, defBinp, -1));
            emitConvHitIf(coverpointp, defBinp, cpVarp, idx++,
                          buildDefaultCondition(coverpointp, exprp, defBinp->fileline()));
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

        // Constructor: init (allocates), namers, then registration (under --coverage)
        const std::string hier = m_covergroupp->name() + "." + coverpointp->name();
        AstCStmt* const initp = new AstCStmt{fl};
        initp->add(memberRef(fl, cpVarp));
        initp->add(".init(\"" + hier + "\", " + std::to_string(atLeastValue) + ", "
                   + std::to_string(idx) + ");");
        m_constructorp->addStmtsp(initp);
        for (AstCStmt* const ns : namerStmts) m_constructorp->addStmtsp(ns);
        if (v3Global.opt.coverage()) {
            AstCStmt* const regp = new AstCStmt{fl};
            regp->add(memberRef(fl, cpVarp));
            regp->add(".registerBins(vlSymsp->_vm_contextp__->coveragep(), \"v_covergroup/"
                      + m_covergroupp->name() + "\");");
            m_constructorp->addStmtsp(regp);
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

    // Clone a constant node, widening to targetWidth if needed (zero-extend).
    // Used to ensure comparisons use matching widths after V3Width has run.
    static AstConst* widenConst(FileLine* fl, AstConst* constp, int targetWidth) {
        if (constp->width() == targetWidth) return constp->cloneTree(false);
        V3Number num{fl, targetWidth, 0};
        num.opAssign(constp->num());
        return new AstConst{fl, num};
    }

    // Build a range condition: minp <= exprp <= maxp.
    // Uses signed comparisons if exprp is signed; omits trivially-true bounds for unsigned.
    // All arguments are non-owning; clones exprp/minp/maxp as needed.
    AstNodeExpr* makeRangeCondition(FileLine* fl, AstNodeExpr* exprp, AstNodeExpr* minp,
                                    AstNodeExpr* maxp) {
        const int exprWidth = exprp->widthMin();
        AstConst* const minConstp = VN_AS(minp, Const);
        AstConst* const maxConstp = VN_AS(maxp, Const);
        // Widen constants to match expression width so post-V3Width nodes use correct macros
        AstConst* const minWidep = widenConst(fl, minConstp, exprWidth);
        AstConst* const maxWidep = widenConst(fl, maxConstp, exprWidth);
        if (exprp->isSigned()) {
            return new AstAnd{fl, new AstGteS{fl, exprp->cloneTree(false), minWidep},
                              new AstLteS{fl, exprp->cloneTree(false), maxWidep}};
        }
        // Unsigned: skip bounds that are trivially satisfied for the expression width
        const bool skipLowerCheck = (minConstp->toUQuad() == 0);
        bool skipUpperCheck = false;
        if (exprWidth <= 64) {
            const uint64_t maxVal
                = (exprWidth == 64) ? ~static_cast<uint64_t>(0) : ((1ULL << exprWidth) - 1ULL);
            skipUpperCheck = (maxConstp->toUQuad() == maxVal);
        }
        if (skipLowerCheck && skipUpperCheck) {
            VL_DO_DANGLING(pushDeletep(minWidep), minWidep);
            VL_DO_DANGLING(pushDeletep(maxWidep), maxWidep);
            return new AstConst{fl, AstConst::BitTrue{}};
        } else if (skipLowerCheck) {
            VL_DO_DANGLING(pushDeletep(minWidep), minWidep);
            return new AstLte{fl, exprp->cloneTree(false), maxWidep};
        } else if (skipUpperCheck) {
            VL_DO_DANGLING(pushDeletep(maxWidep), maxWidep);
            return new AstGte{fl, exprp->cloneTree(false), minWidep};
        } else {
            return new AstAnd{fl, new AstGte{fl, exprp->cloneTree(false), minWidep},
                              new AstLte{fl, exprp->cloneTree(false), maxWidep}};
        }
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

            AstConst* const constp = VN_AS(valp, Const);
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

    // Append a "{ VlCoverpoint* __Vcx_cps[] = {&cp0, &cp1, ...}; <member>.<call> }" statement.
    AstCStmt* makeCrossCpsCall(FileLine* fl, const std::vector<AstVar*>& cpVars, AstVar* cxVarp,
                               const std::string& callText) {
        AstCStmt* const cs = new AstCStmt{fl};
        cs->add("{ VlCoverpoint* __Vcx_cps[] = {");
        for (size_t d = 0; d < cpVars.size(); ++d) {
            cs->add(d == 0 ? "&" : ", &");
            cs->add(memberRef(fl, cpVars[d]));
        }
        cs->add("}; ");
        cs->add(memberRef(fl, cxVarp));
        cs->add(callText);
        cs->add(" }");
        return cs;
    }

    // Route a cross through a VlCoverCross member: emit the member, its constructor init +
    // registration, and the sample() call.  The feeding coverpoints are already generated
    // (their hit lists drive the cross), so only O(1) generated code is needed here.
    void generateCross(AstCoverCross* crossp) {
        FileLine* const fl = crossp->fileline();
        UINFO(4, "  Generating VlCoverCross member: " << crossp->name());

        // Resolve and unlink the coverpoint refs, in dimension order.  Every ref resolves to a
        // known coverpoint (a cross with an unresolvable item was dropped earlier).
        std::vector<AstVar*> cpVars;
        for (AstNode* itemp = crossp->itemsp(); itemp;) {
            AstNode* const nextp = itemp->nextp();
            AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
            const auto it = m_cpVarMap.find(refp->name());
            UASSERT_OBJ(it != m_cpVarMap.end(), crossp, "Cross references an unknown coverpoint");
            cpVars.push_back(it->second);
            VL_DO_DANGLING(pushDeletep(refp->unlinkFrBack()), refp);
            itemp = nextp;
        }
        const int dims = static_cast<int>(cpVars.size());

        if (!m_vlCoverCrossDTypep) {
            m_vlCoverCrossDTypep = new AstCDType{fl, "VlCoverCross"};
            v3Global.rootp()->typeTablep()->addTypesp(m_vlCoverCrossDTypep);
        }
        AstVar* const cxVarp
            = new AstVar{fl, VVarType::MEMBER, "__Vcx_" + crossp->name(), m_vlCoverCrossDTypep};
        cxVarp->isStatic(false);
        m_covergroupp->addMembersp(cxVarp);
        m_crossVars.push_back(cxVarp);

        // Constructor: init (after the coverpoints, which generate earlier) then registration.
        const std::string hier = m_covergroupp->name() + "." + crossp->name();
        const std::string initCall = ".init(\"" + hier + "\", " + std::to_string(dims)
                                     + ", __Vcx_cps, \"" + std::string{fl->filename()} + "\", "
                                     + std::to_string(fl->lineno()) + ", "
                                     + std::to_string(fl->firstColumn()) + ");";
        m_constructorp->addStmtsp(makeCrossCpsCall(fl, cpVars, cxVarp, initCall));
        if (v3Global.opt.coverage()) {
            AstCStmt* const regp = new AstCStmt{fl};
            regp->add(memberRef(fl, cxVarp));
            regp->add(".registerBins(vlSymsp->_vm_contextp__->coveragep(), \"v_covergroup/"
                      + m_covergroupp->name() + "\");");
            m_constructorp->addStmtsp(regp);
        }

        // sample(): after all coverpoints have sampled (cross loop runs after coverpoint loop).
        UASSERT_OBJ(m_sampleFuncp, crossp, "sample() CFunc not set for cross");
        m_sampleFuncp->addStmtsp(makeCrossCpsCall(fl, cpVars, cxVarp, ".sample(__Vcx_cps);"));
    }

    void generateCrossCode(AstCoverCross* crossp) {
        UINFO(4, "  Generating code for cross: " << crossp->name());

        // Non-standard hierarchical/dotted cross item (e.g. 'cross a.b'): an implicit coverpoint
        // over the referenced expression (carried in refp->exprp()).  The grammar already warned
        // NONSTD; implicit coverpoints are not yet implemented, so generate no sampling code for
        // this cross.  When support is added the implicit coverpoint should be synthesized upstream
        // (V3LinkParse) as a real AstCoverpoint so it flows through the normal coverpoint path - by
        // here coverpoint lowering has already run.
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
                    refp->v3warn(COVERIGN, "Unsupported: cross of '"
                                               << refp->prettyName()
                                               << "' which is not a coverpoint (implicit "
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

        // Check if this is a wildcard bin
        const bool isWildcard = binp->isWildcard();

        // Build condition by OR-ing all ranges together
        AstNodeExpr* fullCondp = nullptr;

        for (AstNode* currRangep = rangep; currRangep; currRangep = currRangep->nextp()) {
            AstNodeExpr* rangeCondp = nullptr;

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
                                     "range bounds must be constants");
                        return nullptr;
                    } else if (boundp->num().isFourState()) {
                        irp->v3error("Four-state (x/z) value in bin range bound; "
                                     "range bounds must be two-state constants");
                        return nullptr;
                    } else {
                        rangeCondp = makeOpenRangeCondition(irp->fileline(), exprp, boundp,
                                                            /*isLowerBound=*/hiUnbounded);
                    }
                } else if (!minConstp || !maxConstp) {
                    irp->v3error("Non-constant expression in bin range; "
                                 "range bounds must be constants");
                    return nullptr;
                } else if (minConstp->num().isFourState() || maxConstp->num().isFourState()) {
                    irp->v3error("Four-state (x/z) value in bin range bound; "
                                 "range bounds must be two-state constants");
                    return nullptr;
                } else if (minConstp->toUQuad() == maxConstp->toUQuad()) {
                    // Single value
                    if (isWildcard) {
                        rangeCondp = buildWildcardCondition(binp, exprp, minConstp);
                    } else {
                        rangeCondp = new AstEq{binp->fileline(), exprp->cloneTree(false),
                                               minExprp->cloneTree(false)};
                    }
                } else {
                    rangeCondp = makeRangeCondition(irp->fileline(), exprp, minExprp, maxExprp);
                }
            } else if (AstConst* constp = VN_CAST(currRangep, Const)) {
                if (isWildcard) {
                    rangeCondp = buildWildcardCondition(binp, exprp, constp);
                } else {
                    // TODO: A 4-state bin value (e.g. bins b = {2'b0x}) must match with ===
                    // (AstEqCase) per IEEE 1800-2023 19.5.4. == is equivalent under 2-state sim
                    // (x/z collapse to 0); switch to AstEqCase when 4-state sim support lands.
                    rangeCondp = new AstEq{binp->fileline(), exprp->cloneTree(false),
                                           constp->cloneTree(false)};
                }
            } else {
                currRangep->v3error(
                    "Non-constant expression in bin range; values must be constants");
                return nullptr;
            }

            UASSERT_OBJ(rangeCondp, binp, "rangeCondp is null after building range condition");
            fullCondp
                = fullCondp ? new AstOr{binp->fileline(), fullCondp, rangeCondp} : rangeCondp;
        }

        return fullCondp;
    }

    // Build a wildcard condition: (expr & mask) == (value & mask)
    // where mask has 1s for defined bits and 0s for wildcard bits
    // Non-owning: exprp is cloned internally; caller retains ownership.
    AstNodeExpr* buildWildcardCondition(AstCoverBin* binp, AstNodeExpr* exprp, AstConst* constp) {
        FileLine* const fl = binp->fileline();

        // Extract mask from constant (bits that are not X/Z)
        V3Number mask{constp, constp->width()};
        V3Number value{constp, constp->width()};

        for (int bit = 0; bit < constp->width(); ++bit) {
            if (constp->num().bitIs0(bit) || constp->num().bitIs1(bit)) {
                mask.setBit(bit, 1);
                value.setBit(bit, constp->num().bitIs1(bit) ? 1 : 0);
            } else {
                mask.setBit(bit, 0);
                value.setBit(bit, 0);
            }
        }

        // Generate: (expr & mask) == (value & mask)
        AstConst* const maskConstp = new AstConst{fl, mask};
        AstConst* const valueConstp = new AstConst{fl, value};

        AstNodeExpr* const exprMasked = new AstAnd{fl, exprp->cloneTree(false), maskConstp};
        AstNodeExpr* const valueMasked = new AstAnd{fl, valueConstp, maskConstp->cloneTree(false)};

        // TODO: masking the wildcard (don't-care) bits is correct, but the defined-bit
        // comparison should use === (AstEqCase) per IEEE 1800-2023 19.5.4 once 4-state sim
        // support lands; == is equivalent under 2-state sim (x/z collapse to 0).
        return new AstEq{fl, exprMasked, valueMasked};
    }

    void generateCoverageComputationCode() {
        UINFO(4, "  Generating coverage computation code");

        // Invalidate cache: addMembersp() calls in generateCoverpointCode/generateCrossCode
        // have added new members since the last scan, so clear before re-querying.
        m_memberMap.clear();

        // Find get_coverage() and get_inst_coverage() methods
        AstFunc* const getCoveragep
            = VN_CAST(m_memberMap.findMember(m_covergroupp, "get_coverage"), Func);
        AstFunc* const getInstCoveragep
            = VN_CAST(m_memberMap.findMember(m_covergroupp, "get_inst_coverage"), Func);

        // Generate code for get_inst_coverage() (an empty covergroup returns 100%).
        generateCoverageMethodBody(getInstCoveragep);

        // Generate code for get_coverage() (type-level)
        // NOTE: Full type-level coverage requires instance tracking infrastructure
        // For now, return 0.0 as a placeholder
        AstVar* const coverageReturnVarp = VN_AS(getCoveragep->fvarp(), Var);
        // TODO: Implement proper type-level coverage aggregation
        // This requires tracking all instances and averaging their coverage
        // For now, return 0.0
        getCoveragep->addStmtsp(new AstAssign{
            getCoveragep->fileline(),
            new AstVarRef{getCoveragep->fileline(), coverageReturnVarp, VAccess::WRITE},
            new AstConst{getCoveragep->fileline(), AstConst::RealDouble{}, 0.0}});
        UINFO(4, "    Added placeholder get_coverage() (returns 0.0)");
    }

    void generateCoverageMethodBody(AstFunc* funcp) {
        FileLine* const fl = funcp->fileline();
        AstVar* const returnVarp = VN_AS(funcp->fvarp(), Var);

        // Every coverpoint and cross holds its bins in the runtime (VlCoverpoint/VlCoverCross).
        // Sum their covered/total contributions via coverageParts (Normal bins only; ignore,
        // illegal, and default are excluded per LRM 19.5).  A covergroup with no coverpoints
        // (and hence no crosses) has nothing to cover and reports 100%.
        if (m_cpVars.empty()) {
            funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, returnVarp, VAccess::WRITE},
                                           new AstConst{fl, AstConst::RealDouble{}, 100.0}});
            return;
        }
        AstCStmt* const headp = new AstCStmt{fl};
        headp->add("double __Vcov = 0.0; double __Vtot = 0.0;");
        funcp->addStmtsp(headp);
        for (AstVar* const cpVarp : m_cpVars) {
            AstCStmt* const cs = new AstCStmt{fl};
            cs->add("{ double __Vc = 0.0; double __Vt = 0.0; ");
            cs->add(memberRef(fl, cpVarp));
            cs->add(".coverageParts(__Vc, __Vt); __Vcov += __Vc; __Vtot += __Vt; }");
            funcp->addStmtsp(cs);
        }
        // Crosses contribute the same covered/total ratio as their per-tuple bins.
        for (AstVar* const cxVarp : m_crossVars) {
            AstCStmt* const cs = new AstCStmt{fl};
            cs->add("{ double __Vc = 0.0; double __Vt = 0.0; ");
            cs->add(memberRef(fl, cxVarp));
            cs->add(".coverageParts(__Vc, __Vt); __Vcov += __Vc; __Vtot += __Vt; }");
            funcp->addStmtsp(cs);
        }
        AstCStmt* const retp = new AstCStmt{fl};
        retp->add(new AstVarRef{fl, returnVarp, VAccess::WRITE});
        retp->add(" = (__Vtot != 0.0) ? (100.0 * __Vcov / __Vtot) : 100.0;");
        funcp->addStmtsp(retp);
    }

    // VISITORS
    AstNode* findEnclosingMemberRef(AstClass* cgClassp) {
        // An embedded covergroup is lowered into a sibling AstClass that has no handle to
        // the enclosing object.  A coverpoint/iff/cross expression that references a
        // (non-static) member of the enclosing class therefore emits C++ that accesses the
        // member as if it were static ("invalid use of non-static data member").  Detect
        // such references so the caller can skip lowering with a clean warning instead of
        // producing uncompilable code.  Returns the first offending node, or nullptr.
        // Collect the covergroup class's own member variables (sample/constructor args);
        // references to those are legitimate.
        std::set<const AstVar*> ownVars;
        for (AstNode* itemp = cgClassp->membersp(); itemp; itemp = itemp->nextp()) {
            if (const AstVar* const varp = VN_CAST(itemp, Var)) ownVars.insert(varp);
        }
        AstNode* offenderp = nullptr;
        const auto scan = [&](AstNode* rootp) {
            rootp->foreach([&](AstVarRef* refp) {
                if (offenderp) return;
                const AstVar* const varp = refp->varp();  // Always set post-LinkDot
                // A member of another class (the enclosing class) reached with no handle.
                // Members of the covergroup class itself (sample/constructor args) are
                // legitimate and excluded via ownVars.
                if (varp->isClassMember() && !ownVars.count(varp)) offenderp = refp;
            });
        };
        for (AstCoverpoint* cpp : m_coverpoints) scan(cpp);
        for (AstCoverCross* crossp : m_coverCrosses) scan(crossp);
        return offenderp;
    }

    void visit(AstClass* nodep) override {
        UINFO(9, "Visiting class: " << nodep->name() << " isCovergroup=" << nodep->isCovergroup());
        if (nodep->isCovergroup()) {
            VL_RESTORER(m_covergroupp);
            VL_RESTORER(m_sampleFuncp);
            VL_RESTORER(m_constructorp);
            VL_RESTORER(m_coverpoints);
            VL_RESTORER(m_coverpointMap);
            VL_RESTORER(m_coverCrosses);
            m_covergroupp = nodep;
            m_sampleFuncp = nullptr;
            m_constructorp = nullptr;
            m_coverpoints.clear();
            m_coverpointMap.clear();
            m_coverCrosses.clear();

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
                    // Check if the clocking event references a member variable (unsupported)
                    // Clocking events should be on signals/nets, not class members
                    bool eventUnsupported = false;
                    for (AstNode* senp = cgp->eventp()->sensesp(); senp; senp = senp->nextp()) {
                        AstSenItem* const senItemp = VN_AS(senp, SenItem);
                        if (AstVarRef* const varrefp  // LCOV_EXCL_BR_LINE
                            = VN_CAST(senItemp->sensp(), VarRef)) {
                            if (varrefp->varp()->isClassMember()) {
                                cgp->v3warn(COVERIGN, "Unsupported: 'covergroup' clocking event "
                                                      "on member variable");
                                eventUnsupported = true;
                                hasUnsupportedEvent = true;
                                break;
                            }
                        }
                    }

                    if (!eventUnsupported) {
                        // Leave cgp in the class membersp so the SenTree stays
                        // linked in the AST. V3Active will find it via membersp,
                        // use the event, then delete the AstCovergroup itself.
                        UINFO(4, "Keeping covergroup event node for V3Active: " << nodep->name());
                        itemp = nextp;
                        continue;
                    }
                    // Remove the AstCovergroup node - either unsupported event or no event
                    VL_DO_DANGLING(pushDeletep(cgp->unlinkFrBack()), cgp);
                }
                itemp = nextp;
            }

            // If covergroup has unsupported clocking event, skip processing it
            // but still clean up coverpoints so they don't reach downstream passes
            if (hasUnsupportedEvent) {
                iterateChildren(nodep);
                for (AstCoverpoint* cpp : m_coverpoints) {
                    VL_DO_DANGLING(pushDeletep(cpp->unlinkFrBack()), cpp);
                }
                for (AstCoverCross* crossp : m_coverCrosses) {
                    VL_DO_DANGLING(pushDeletep(crossp->unlinkFrBack()), crossp);
                }
                return;
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

            iterateChildren(nodep);

            // Option B safety net for embedded covergroups: if a coverpoint/iff/cross
            // references a member of the enclosing class, lowering would emit uncompilable
            // C++ (no handle to the enclosing instance).  Skip this covergroup with a clean
            // warning rather than crashing the C++ compile.  (Full support - an enclosing
            // back-pointer - is the planned follow-up.)
            if (AstNode* const offenderp = findEnclosingMemberRef(nodep)) {
                offenderp->v3warn(COVERIGN,
                                  "Unsupported: 'covergroup' coverpoint referencing enclosing "
                                  "class member; ignoring covergroup "
                                      << nodep->prettyNameQ());
                for (AstCoverpoint* cpp : m_coverpoints) {
                    VL_DO_DANGLING(pushDeletep(cpp->unlinkFrBack()), cpp);
                }
                for (AstCoverCross* crossp : m_coverCrosses) {
                    VL_DO_DANGLING(pushDeletep(crossp->unlinkFrBack()), crossp);
                }
                return;
            }

            processCovergroup();
            // Remove lowered coverpoints/crosses from the class - they have been
            // fully translated into C++ code and must not reach downstream passes
            for (AstCoverpoint* cpp : m_coverpoints) {
                VL_DO_DANGLING(pushDeletep(cpp->unlinkFrBack()), cpp);
            }
            for (AstCoverCross* crossp : m_coverCrosses) {
                VL_DO_DANGLING(pushDeletep(crossp->unlinkFrBack()), crossp);
            }
        } else {
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
    { FunctionalCoverageVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragefunc", 0, dumpTreeEitherLevel() >= 3);
}
