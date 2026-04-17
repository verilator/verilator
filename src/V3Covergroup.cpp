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

    // Structure to track bins with their variables and options
    struct BinInfo final {
        AstCoverBin* binp;
        AstVar* varp;
        int atLeast;  // Minimum hits required for coverage (from option.at_least)
        AstCoverpoint* coverpointp;  // Associated coverpoint (or nullptr for cross bins)
        AstCoverCross* crossp;  // Associated cross (or nullptr for coverpoint bins)
        BinInfo(AstCoverBin* b, AstVar* v, int al = 1, AstCoverpoint* cp = nullptr,
                AstCoverCross* cr = nullptr)
            : binp{b}
            , varp{v}
            , atLeast{al}
            , coverpointp{cp}
            , crossp{cr} {}
    };
    std::vector<BinInfo> m_binInfos;  // All bins in current covergroup

    VMemberMap m_memberMap;  // Member names cached for fast lookup

    // METHODS
    void clearBinInfos() {
        // Delete pseudo-bins created for cross coverage (they're never inserted into the AST)
        for (const BinInfo& bi : m_binInfos) {
            if (!bi.coverpointp) pushDeletep(bi.binp);
        }
        m_binInfos.clear();
    }

    void processCovergroup() {
        UINFO(4, "Processing covergroup: " << m_covergroupp->name() << " with "
                                           << m_coverpoints.size() << " coverpoints and "
                                           << m_coverCrosses.size() << " crosses");

        // Clear bin info for this covergroup (deleting any orphaned cross pseudo-bins)
        clearBinInfos();

        // For each coverpoint, generate sampling code
        for (AstCoverpoint* cpp : m_coverpoints) generateCoverpointCode(cpp);

        // For each cross, generate sampling code
        for (AstCoverCross* crossp : m_coverCrosses) generateCrossCode(crossp);

        // Generate coverage computation code (even for empty covergroups)
        generateCoverageComputationCode();

        // TODO: Generate instance registry infrastructure for static get_coverage()
        // This requires:
        // - Static registry members (t_instances, s_mutex)
        // - registerInstance() / unregisterInstance() methods
        // - Proper C++ emission in EmitC backend
        // For now, get_coverage() returns 0.0 (placeholder)

        // Generate coverage database registration if coverage is enabled
        if (v3Global.opt.coverage()) generateCoverageRegistration();

        // Clean up orphaned cross pseudo-bins now that we're done with them
        clearBinInfos();
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
                optp->valuep()->v3error("option." << optp->optionType().ascii()
                                                  << " must be a constant expression");
                continue;
            }
            if (optp->optionType() == VCoverOptionType::AT_LEAST) {
                atLeastOut = constp->toSInt();
            } else if (optp->optionType() == VCoverOptionType::AUTO_BIN_MAX) {
                autoBinMaxOut = constp->toSInt();
            }
        }
        // Fall back to covergroup-level auto_bin_max if not set at coverpoint level
        if (autoBinMaxOut < 0) {
            if (m_covergroupp->cgAutoBinMax() >= 0) {
                autoBinMaxOut = m_covergroupp->cgAutoBinMax();
            } else {
                autoBinMaxOut = 64;  // Default per IEEE 1800-2017
            }
        }
    }

    // Extract individual values from a range expression list.
    // Iterates over all siblings (nextp) in the list, handling AstConst (single value)
    // and AstInsideRange ([lo:hi]).
    void extractValuesFromRange(AstNode* nodep, std::set<uint64_t>& values) {
        for (AstNode* np = nodep; np; np = np->nextp()) {
            if (AstConst* constp = VN_CAST(np, Const)) {
                values.insert(constp->toUQuad());
            } else if (AstInsideRange* rangep = VN_CAST(np, InsideRange)) {
                AstNodeExpr* const lhsp = V3Const::constifyEdit(rangep->lhsp());
                AstNodeExpr* const rhsp = V3Const::constifyEdit(rangep->rhsp());
                AstConst* const loConstp = VN_CAST(lhsp, Const);
                AstConst* const hiConstp = VN_CAST(rhsp, Const);
                if (!loConstp || !hiConstp) {
                    rangep->v3error("Non-constant expression in bin range; "
                                    "range bounds must be constants");
                    continue;
                }
                const uint64_t lo = loConstp->toUQuad();
                const uint64_t hi = hiConstp->toUQuad();
                for (uint64_t v = lo; v <= hi; v++) values.insert(v);
            } else {
                np->v3error("Non-constant expression in bin value list; values must be constants");
            }
        }
    }

    // Single-pass categorization: determine whether any regular (non-ignore/illegal) bins exist
    // and collect the set of excluded values from ignore/illegal bins.
    void categorizeBins(AstCoverpoint* coverpointp, bool& hasRegularOut,
                        std::set<uint64_t>& excludedOut) {
        hasRegularOut = false;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
            const VCoverBinsType btype = cbinp->binsType();
            if (btype == VCoverBinsType::BINS_IGNORE || btype == VCoverBinsType::BINS_ILLEGAL) {
                if (AstNode* rangep = cbinp->rangesp()) {
                    extractValuesFromRange(rangep, excludedOut);
                }
            } else {
                hasRegularOut = true;
            }
        }
    }

    // Create implicit automatic bins when coverpoint has no explicit regular bins
    void createImplicitAutoBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp, int autoBinMax) {
        // Single pass: check for regular bins and collect excluded values simultaneously
        bool hasRegular = false;
        std::set<uint64_t> excluded;
        categorizeBins(coverpointp, hasRegular, excluded);

        // If already has regular bins, nothing to do
        if (hasRegular) return;

        UINFO(4, "  Creating implicit automatic bins for coverpoint: " << coverpointp->name());

        const int width = exprp->width();
        const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
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

        // Generate member variables and matching code for each bin
        // Process in two passes: first non-default bins, then default bins
        std::vector<AstCoverBin*> defaultBins;
        bool hasTransition = false;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);

            // Defer default bins to second pass
            if (cbinp->binsType() == VCoverBinsType::BINS_DEFAULT) {
                defaultBins.push_back(cbinp);
                continue;
            }

            // Handle array bins: create separate bin for each value/transition
            if (cbinp->isArray()) {
                if (cbinp->transp()) {  // transition bin (includes illegal_bins with transitions)
                    hasTransition = true;
                    generateTransitionArrayBins(coverpointp, cbinp, exprp, atLeastValue);
                } else {
                    generateArrayBins(coverpointp, cbinp, exprp, atLeastValue);
                }
                continue;
            }

            // Create a member variable to track hits for this bin
            // Sanitize bin name to make it a valid C++ identifier
            string binName = cbinp->name();
            std::replace(binName.begin(), binName.end(), '[', '_');
            std::replace(binName.begin(), binName.end(), ']', '_');
            const string varName = "__Vcov_" + coverpointp->name() + "_" + binName;
            AstVar* const varp = new AstVar{cbinp->fileline(), VVarType::MEMBER, varName,
                                            cbinp->findUInt32DType()};
            varp->isStatic(false);
            varp->valuep(new AstConst{cbinp->fileline(), AstConst::WidthedValue{}, 32, 0});
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created member variable: " << varName
                                                     << " type=" << cbinp->binsType().ascii());

            // Track this bin for coverage computation with at_least value
            m_binInfos.push_back(BinInfo(cbinp, varp, atLeastValue, coverpointp));

            // Note: Coverage database registration happens later via VL_COVER_INSERT
            // (see generateCoverageDeclarations() method around line 1164)
            // Classes use "v_covergroup/" hier prefix vs modules

            // Generate bin matching code in sample()
            // Handle transition bins specially (includes illegal_bins with transition syntax)
            if (cbinp->transp()) {
                hasTransition = true;
                generateTransitionBinMatchCode(coverpointp, cbinp, exprp, varp);
            } else {
                generateBinMatchCode(coverpointp, cbinp, exprp, varp);
            }
        }

        // Second pass: Handle default bins
        // Default bin matches when value doesn't match any other explicit bin
        for (AstCoverBin* defBinp : defaultBins) {
            // Create member variable for default bin
            string binName = defBinp->name();
            std::replace(binName.begin(), binName.end(), '[', '_');
            std::replace(binName.begin(), binName.end(), ']', '_');
            const string varName = "__Vcov_" + coverpointp->name() + "_" + binName;
            AstVar* const varp = new AstVar{defBinp->fileline(), VVarType::MEMBER, varName,
                                            defBinp->findUInt32DType()};
            varp->isStatic(false);
            varp->valuep(new AstConst{defBinp->fileline(), AstConst::WidthedValue{}, 32, 0});
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created default bin variable: " << varName);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(defBinp, varp, atLeastValue, coverpointp));

            // Generate matching code: if (NOT (bin1 OR bin2 OR ... OR binN))
            generateDefaultBinMatchCode(coverpointp, defBinp, exprp, varp);
        }

        // After all bins processed, if coverpoint has transition bins, update previous value
        if (hasTransition) {
            AstVar* const prevVarp = VN_AS(coverpointp->user1p(), Var);
            // Generate: __Vprev_cpname = current_value;
            AstNodeStmt* updateStmtp
                = new AstAssign{coverpointp->fileline(),
                                new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::WRITE},
                                exprp->cloneTree(false)};
            m_sampleFuncp->addStmtsp(updateStmtp);
            UINFO(4, "    Added previous value update at end of sample()");
        }
    }

    void generateBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* binp, AstNodeExpr* exprp,
                              AstVar* hitVarp) {
        UINFO(4, "    Generating bin match for: " << binp->name());

        // Build the bin matching condition using the shared function
        AstNodeExpr* fullCondp = buildBinCondition(binp, exprp);

        if (!fullCondp) {
            // Reachable: e.g. 'ignore_bins ib = default' creates a BINS_IGNORE bin
            // with null rangesp. Skipping match code generation is correct in that case.
            return;
        }

        // Apply iff condition if present - wraps the bin match condition
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            UINFO(6, "      Adding iff condition");
            fullCondp = new AstAnd{binp->fileline(), iffp->cloneTree(false), fullCondp};
        }

        // Create the increment statement
        AstNode* stmtp = makeBinHitIncrement(binp->fileline(), hitVarp);

        // For illegal_bins, add an error message
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            const string errMsg = "Illegal bin '" + binp->name() + "' hit in coverpoint '"
                                  + coverpointp->name() + "'";
            stmtp = stmtp->addNext(makeIllegalBinAction(binp->fileline(), errMsg));
        }

        // Create: if (condition) { hitVar++; [error if illegal] }
        AstIf* const ifp = new AstIf{binp->fileline(), fullCondp, stmtp, nullptr};

        UINFO(4, "      Adding bin match if statement to sample function");
        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set when generating bin match code");
        m_sampleFuncp->addStmtsp(ifp);
        UINFO(4, "      Successfully added if statement for bin: " << binp->name());
    }

    // Generate matching code for default bins
    // Default bins match when value doesn't match any other explicit bin
    void generateDefaultBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* defBinp,
                                     AstNodeExpr* exprp, AstVar* hitVarp) {
        UINFO(4, "    Generating default bin match for: " << defBinp->name());

        // Build OR of all non-default, non-ignore bins
        AstNodeExpr* anyBinMatchp = nullptr;

        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_AS(binp, CoverBin);

            // Skip default, ignore, and illegal bins
            if (cbinp->binsType() == VCoverBinsType::BINS_DEFAULT
                || cbinp->binsType() == VCoverBinsType::BINS_IGNORE
                || cbinp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                continue;
            }

            // Build condition for this bin
            AstNodeExpr* const binCondp = buildBinCondition(cbinp, exprp);
            UASSERT_OBJ(binCondp, cbinp,
                        "buildBinCondition returned nullptr for non-ignore/non-illegal bin");

            // OR with previous conditions
            if (anyBinMatchp) {
                anyBinMatchp = new AstOr{defBinp->fileline(), anyBinMatchp, binCondp};
            } else {
                anyBinMatchp = binCondp;
            }
        }

        // Default matches when NO explicit bin matches
        AstNodeExpr* defaultCondp = nullptr;
        if (anyBinMatchp) {
            // NOT (bin1 OR bin2 OR ... OR binN)
            defaultCondp = new AstNot{defBinp->fileline(), anyBinMatchp};
        } else {
            // No other bins - default always matches (shouldn't happen in practice)
            defaultCondp = new AstConst{defBinp->fileline(), AstConst::BitTrue{}};
        }

        // Apply iff condition if present
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            defaultCondp = new AstAnd{defBinp->fileline(), iffp->cloneTree(false), defaultCondp};
        }

        // Create increment statement
        AstNode* const stmtp = makeBinHitIncrement(defBinp->fileline(), hitVarp);

        // Create if statement
        AstIf* const ifp = new AstIf{defBinp->fileline(), defaultCondp, stmtp, nullptr};

        UASSERT_OBJ(m_sampleFuncp, defBinp,
                    "sample() CFunc not set when generating default bin code");
        m_sampleFuncp->addStmtsp(ifp);
        UINFO(4, "      Successfully added default bin if statement");
    }

    // Generate matching code for transition bins
    // Transition bins match sequences like: (val1 => val2 => val3)
    void generateTransitionBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                        AstNodeExpr* exprp, AstVar* hitVarp) {
        UINFO(4, "    Generating transition bin match for: " << binp->name());

        // Get the (single) transition set
        AstCoverTransSet* const transSetp = binp->transp();

        // Use the helper function to generate code for this transition
        generateSingleTransitionCode(coverpointp, binp, exprp, hitVarp, transSetp);
    }

    // Generate state machine code for multi-value transition sequences
    // Handles transitions like (1 => 2 => 3 => 4)
    void generateMultiValueTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                          AstNodeExpr* exprp, AstVar* hitVarp,
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
            AstCaseItem* caseItemp = generateTransitionStateCase(coverpointp, binp, exprp, hitVarp,
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
                                             AstNodeExpr* exprp, AstVar* hitVarp,
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
            // Last state: sequence complete!
            // Increment bin counter
            matchActionp = makeBinHitIncrement(fl, hitVarp);

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

    // Create: hitVarp = hitVarp + 1
    AstAssign* makeBinHitIncrement(FileLine* fl, AstVar* hitVarp) {
        return new AstAssign{fl, new AstVarRef{fl, hitVarp, VAccess::WRITE},
                             new AstAdd{fl, new AstVarRef{fl, hitVarp, VAccess::READ},
                                        new AstConst{fl, AstConst::WidthedValue{}, 32, 1}}};
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

    // Generate multiple bins for array bins
    // Array bins create one bin per value in the range list
    void generateArrayBins(AstCoverpoint* coverpointp, AstCoverBin* arrayBinp, AstNodeExpr* exprp,
                           int atLeastValue) {
        UINFO(4, "    Generating array bins for: " << arrayBinp->name());

        // Extract all values from the range list
        std::vector<AstNodeExpr*> values;
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstInsideRange* const insideRangep = VN_CAST(rangep, InsideRange)) {
                // For InsideRange [min:max], create bins for each value
                AstNodeExpr* const minp = V3Const::constifyEdit(insideRangep->lhsp());
                AstNodeExpr* const maxp = V3Const::constifyEdit(insideRangep->rhsp());
                AstConst* const minConstp = VN_CAST(minp, Const);
                AstConst* const maxConstp = VN_CAST(maxp, Const);
                if (minConstp && maxConstp) {  // LCOV_EXCL_BR_LINE
                    const int minVal = minConstp->toSInt();
                    const int maxVal = maxConstp->toSInt();
                    UINFO(6, "      Expanding InsideRange [" << minVal << ":" << maxVal << "]");
                    for (int val = minVal; val <= maxVal; ++val) {
                        values.push_back(new AstConst{insideRangep->fileline(),
                                                      AstConst::WidthedValue{},
                                                      (int)exprp->width(), (uint32_t)val});
                    }
                } else {
                    arrayBinp->v3error("Non-constant expression in array bins range; "
                                       "range bounds must be constants");
                    return;
                }
            } else {
                // Single value - should be an expression
                values.push_back(VN_AS(rangep->cloneTree(false), NodeExpr));
            }
        }

        // Create a separate bin for each value
        int index = 0;
        for (AstNodeExpr* valuep : values) {
            // Create bin name: originalName[index]
            const string binName = arrayBinp->name() + "[" + std::to_string(index) + "]";
            const string sanitizedName = arrayBinp->name() + "_" + std::to_string(index);
            const string varName = "__Vcov_" + coverpointp->name() + "_" + sanitizedName;

            // Create member variable for this bin
            AstVar* const varp = new AstVar{arrayBinp->fileline(), VVarType::MEMBER, varName,
                                            arrayBinp->findUInt32DType()};
            varp->isStatic(false);
            varp->valuep(new AstConst{arrayBinp->fileline(), AstConst::WidthedValue{}, 32, 0});
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created array bin [" << index << "]: " << varName);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(arrayBinp, varp, atLeastValue, coverpointp));

            // Generate matching code for this specific value
            generateArrayBinMatchCode(coverpointp, arrayBinp, exprp, varp, valuep);

            ++index;
        }

        UINFO(4, "    Generated " << index << " array bins");
    }

    // Generate matching code for a single array bin element
    void generateArrayBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                   AstNodeExpr* exprp, AstVar* hitVarp, AstNodeExpr* valuep) {
        // Create condition: expr == value
        AstNodeExpr* condp = new AstEq{binp->fileline(), exprp->cloneTree(false), valuep};

        // Apply iff condition if present
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            condp = new AstAnd{binp->fileline(), iffp->cloneTree(false), condp};
        }

        // Create increment statement
        AstNode* stmtp = makeBinHitIncrement(binp->fileline(), hitVarp);

        // For illegal_bins, add error message
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            const string errMsg = "Illegal bin hit in coverpoint '" + coverpointp->name() + "'";
            stmtp = stmtp->addNext(makeIllegalBinAction(binp->fileline(), errMsg));
        }

        // Create if statement
        AstIf* const ifp = new AstIf{binp->fileline(), condp, stmtp, nullptr};

        UASSERT_OBJ(m_sampleFuncp, binp, "sample() CFunc not set when generating array bin code");
        m_sampleFuncp->addStmtsp(ifp);
    }

    // Generate multiple bins for transition array bins
    // Array bins with transitions create one bin per transition sequence
    void generateTransitionArrayBins(AstCoverpoint* coverpointp, AstCoverBin* arrayBinp,
                                     AstNodeExpr* exprp, int atLeastValue) {
        UINFO(4, "    Generating transition array bins for: " << arrayBinp->name());

        // Extract all transition sets
        std::vector<AstCoverTransSet*> transSets;
        for (AstNode* transSetp = arrayBinp->transp(); transSetp; transSetp = transSetp->nextp())
            transSets.push_back(VN_AS(transSetp, CoverTransSet));

        UINFO(4, "      Found " << transSets.size() << " transition sets");
        int index = 0;
        for (AstCoverTransSet* transSetp : transSets) {
            // Create bin name: originalName[index]
            const string binName = arrayBinp->name() + "[" + std::to_string(index) + "]";
            const string sanitizedName = arrayBinp->name() + "_" + std::to_string(index);
            const string varName = "__Vcov_" + coverpointp->name() + "_" + sanitizedName;

            // Create member variable for this bin
            AstVar* const varp = new AstVar{arrayBinp->fileline(), VVarType::MEMBER, varName,
                                            arrayBinp->findUInt32DType()};
            varp->isStatic(false);
            varp->valuep(new AstConst{arrayBinp->fileline(), AstConst::WidthedValue{}, 32, 0});
            m_covergroupp->addMembersp(varp);
            UINFO(4, "      Created transition array bin [" << index << "]: " << varName);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(arrayBinp, varp, atLeastValue, coverpointp));

            // Generate matching code for this specific transition
            generateSingleTransitionCode(coverpointp, arrayBinp, exprp, varp, transSetp);

            ++index;
        }

        UINFO(4, "    Generated " << index << " transition array bins");
    }

    // Generate code for a single transition sequence (used by both regular and array bins)
    void generateSingleTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                      AstNodeExpr* exprp, AstVar* hitVarp,
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

            // Apply iff condition if present
            if (AstNodeExpr* iffp = coverpointp->iffp()) {
                fullCondp = new AstAnd{binp->fileline(), iffp->cloneTree(false), fullCondp};
            }

            // Create increment statement
            AstNode* stmtp = makeBinHitIncrement(binp->fileline(), hitVarp);

            // For illegal_bins, add an error message
            if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                const string errMsg = "Illegal transition bin " + binp->prettyNameQ()
                                      + " hit in coverpoint " + coverpointp->prettyNameQ();
                stmtp = stmtp->addNext(makeIllegalBinAction(binp->fileline(), errMsg));
            }

            // Create if statement
            AstIf* const ifp = new AstIf{binp->fileline(), fullCondp, stmtp, nullptr};
            m_sampleFuncp->addStmtsp(ifp);

            UINFO(4, "        Successfully added 2-value transition if statement");
        } else {
            // Multi-value sequence (a => b => c => ...)
            // Use state machine to track position in sequence
            generateMultiValueTransitionCode(coverpointp, binp, exprp, hitVarp, items);
        }
    }

    // Recursive helper to generate Cartesian product of cross bins
    void generateCrossBinsRecursive(AstCoverCross* crossp,
                                    const std::vector<AstCoverpoint*>& coverpointRefs,
                                    const std::vector<std::vector<AstCoverBin*>>& allCpBins,
                                    std::vector<AstCoverBin*> currentCombination,
                                    size_t dimension) {
        if (dimension == allCpBins.size()) {
            // Base case: we have a complete combination, generate the cross bin
            generateOneCrossBin(crossp, coverpointRefs, currentCombination);
            return;
        }

        // Recursive case: iterate through bins at current dimension
        for (AstCoverBin* binp : allCpBins[dimension]) {
            currentCombination.push_back(binp);
            generateCrossBinsRecursive(crossp, coverpointRefs, allCpBins, currentCombination,
                                       dimension + 1);
            currentCombination.pop_back();
        }
    }

    // Generate a single cross bin for a specific combination of bins
    void generateOneCrossBin(AstCoverCross* crossp,
                             const std::vector<AstCoverpoint*>& coverpointRefs,
                             const std::vector<AstCoverBin*>& bins) {
        // Build sanitized name from all bins
        string binName;
        string varName = "__Vcov_" + crossp->name();

        for (size_t i = 0; i < bins.size(); ++i) {
            string sanitized = bins[i]->name();
            std::replace(sanitized.begin(), sanitized.end(), '[', '_');
            std::replace(sanitized.begin(), sanitized.end(), ']', '_');

            if (i > 0) {
                binName += "_x_";
                varName += "_x_";
            }
            binName += sanitized;
            varName += "_" + sanitized;
        }

        // Create member variable for this cross bin
        AstVar* const varp = new AstVar{crossp->fileline(), VVarType::MEMBER, varName,
                                        bins[0]->findUInt32DType()};
        varp->isStatic(false);
        varp->valuep(new AstConst{crossp->fileline(), AstConst::WidthedValue{}, 32, 0});
        m_covergroupp->addMembersp(varp);

        UINFO(4, "      Created cross bin variable: " << varName);

        // Track this for coverage computation
        AstCoverBin* const pseudoBinp = new AstCoverBin{
            crossp->fileline(), binName, static_cast<AstNode*>(nullptr), false, false};
        m_binInfos.push_back(BinInfo(pseudoBinp, varp, 1, nullptr, crossp));

        // Generate matching code: if (bin1 && bin2 && ... && binN) varName++;
        generateNWayCrossBinMatchCode(crossp, coverpointRefs, bins, varp);
    }

    // Generate matching code for N-way cross bin
    void generateNWayCrossBinMatchCode(AstCoverCross* crossp,
                                       const std::vector<AstCoverpoint*>& coverpointRefs,
                                       const std::vector<AstCoverBin*>& bins, AstVar* hitVarp) {
        UINFO(4, "      Generating " << bins.size() << "-way cross bin match");

        // Build combined condition by ANDing all bin conditions
        AstNodeExpr* fullCondp = nullptr;

        for (size_t i = 0; i < bins.size(); ++i) {
            AstNodeExpr* const exprp = coverpointRefs[i]->exprp();
            AstNodeExpr* const condp = buildBinCondition(bins[i], exprp);

            if (fullCondp) {
                fullCondp = new AstAnd{crossp->fileline(), fullCondp, condp};
            } else {
                fullCondp = condp;
            }
        }

        // Generate: if (cond1 && cond2 && ... && condN) { ++varName; }
        AstNodeStmt* const incrp = makeBinHitIncrement(crossp->fileline(), hitVarp);

        AstIf* const ifp = new AstIf{crossp->fileline(), fullCondp, incrp};
        m_sampleFuncp->addStmtsp(ifp);
    }

    void generateCrossCode(AstCoverCross* crossp) {
        UINFO(4, "  Generating code for cross: " << crossp->name());

        // Resolve coverpoint references and build list
        std::vector<AstCoverpoint*> coverpointRefs;
        AstNode* itemp = crossp->itemsp();
        while (itemp) {
            AstNode* const nextp = itemp->nextp();
            AstCoverpointRef* const refp = VN_AS(itemp, CoverpointRef);
            // Find the referenced coverpoint via name map (O(log n) vs O(n) linear scan)
            const auto it = m_coverpointMap.find(refp->name());
            AstCoverpoint* const foundCpp = (it != m_coverpointMap.end()) ? it->second : nullptr;

            if (!foundCpp) {
                // Name not found as an explicit coverpoint - it's likely a direct variable
                // reference (implicit coverpoint). Silently ignore; cross is dropped.
                UINFO(4, "  Ignoring cross with implicit variable reference: " << refp->name());
                return;
            }

            coverpointRefs.push_back(foundCpp);

            // Delete the reference node - it's no longer needed
            VL_DO_DANGLING(pushDeletep(refp->unlinkFrBack()), refp);
            itemp = nextp;
        }  // LCOV_EXCL_BR_LINE

        UINFO(4, "    Generating " << coverpointRefs.size() << "-way cross");

        // Collect bins from all coverpoints (excluding ignore/illegal bins)
        std::vector<std::vector<AstCoverBin*>> allCpBins;
        for (AstCoverpoint* cpp : coverpointRefs) {
            std::vector<AstCoverBin*> cpBins;
            for (AstNode* binp = cpp->binsp(); binp; binp = binp->nextp()) {
                AstCoverBin* const cbinp = VN_AS(binp, CoverBin);
                if (cbinp->binsType() == VCoverBinsType::BINS_USER) { cpBins.push_back(cbinp); }
            }
            UINFO(4, "      Found " << cpBins.size() << " bins in " << cpp->name());
            allCpBins.push_back(cpBins);
        }

        // Generate cross bins using Cartesian product
        generateCrossBinsRecursive(crossp, coverpointRefs, allCpBins, {}, 0);
    }

    AstNodeExpr* buildBinCondition(AstCoverBin* binp, AstNodeExpr* exprp) {
        // Get the range list from the bin
        AstNode* const rangep = binp->rangesp();
        if (!rangep) return nullptr;

        // Check if this is a wildcard bin
        const bool isWildcard = (binp->binsType() == VCoverBinsType::BINS_WILDCARD);

        // Build condition by OR-ing all ranges together
        AstNodeExpr* fullCondp = nullptr;

        for (AstNode* currRangep = rangep; currRangep; currRangep = currRangep->nextp()) {
            AstNodeExpr* rangeCondp = nullptr;

            if (AstInsideRange* irp = VN_CAST(currRangep, InsideRange)) {
                AstNodeExpr* const minExprp = irp->lhsp();
                AstNodeExpr* const maxExprp = irp->rhsp();
                AstConst* const minConstp = VN_CAST(minExprp, Const);
                AstConst* const maxConstp = VN_CAST(maxExprp, Const);
                if (!minConstp || !maxConstp) {
                    irp->v3error("Non-constant expression in bin range; "
                                 "range bounds must be constants");
                    return nullptr;
                }
                if (minConstp->toUQuad() == maxConstp->toUQuad()) {
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

        // Even if there are no bins, we still need to generate the coverage methods
        // Empty covergroups should return 100% coverage
        if (m_binInfos.empty()) {
            UINFO(4, "    No bins found, will generate method to return 100%");
        } else {
            UINFO(6, "    Found " << m_binInfos.size() << " bins for coverage");
        }

        // Generate code for get_inst_coverage()
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

        // Count total bins (excluding ignore_bins and illegal_bins)
        int totalBins = 0;
        for (const BinInfo& bi : m_binInfos) {
            UINFO(6, "      Bin: " << bi.binp->name() << " type=" << bi.binp->binsType().ascii());
            if (bi.binp->binsType() != VCoverBinsType::BINS_IGNORE
                && bi.binp->binsType() != VCoverBinsType::BINS_ILLEGAL) {
                totalBins++;
            }
        }

        UINFO(4, "    Total regular bins: " << totalBins << " of " << m_binInfos.size());

        if (totalBins == 0) {
            // No coverage to compute - return 100%.
            // Any parser-generated initialization of returnVar is overridden by our assignment.
            UINFO(4, "    Empty covergroup, returning 100.0");
            AstVar* const returnVarp = VN_AS(funcp->fvarp(), Var);
            funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, returnVarp, VAccess::WRITE},
                                           new AstConst{fl, AstConst::RealDouble{}, 100.0}});
            UINFO(4, "    Added assignment to return 100.0");
            return;
        }

        // Create local variable to count covered bins
        AstVar* const coveredCountp
            = new AstVar{fl, VVarType::BLOCKTEMP, "__Vcovered_count", funcp->findUInt32DType()};
        coveredCountp->funcLocal(true);
        funcp->addStmtsp(coveredCountp);

        // Initialize: covered_count = 0
        funcp->addStmtsp(new AstAssign{fl, new AstVarRef{fl, coveredCountp, VAccess::WRITE},
                                       new AstConst{fl, AstConst::WidthedValue{}, 32, 0}});

        // For each regular bin, if count > 0, increment covered_count
        for (const BinInfo& bi : m_binInfos) {
            // Skip ignore_bins and illegal_bins in coverage calculation
            if (bi.binp->binsType() == VCoverBinsType::BINS_IGNORE
                || bi.binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                continue;
            }

            // if (bin_count >= at_least) covered_count++;
            AstIf* ifp = new AstIf{
                fl,
                new AstGte{fl, new AstVarRef{fl, bi.varp, VAccess::READ},
                           new AstConst{fl, AstConst::WidthedValue{}, 32,
                                        static_cast<uint32_t>(bi.atLeast)}},
                new AstAssign{fl, new AstVarRef{fl, coveredCountp, VAccess::WRITE},
                              new AstAdd{fl, new AstVarRef{fl, coveredCountp, VAccess::READ},
                                         new AstConst{fl, AstConst::WidthedValue{}, 32, 1}}},
                nullptr};
            funcp->addStmtsp(ifp);
        }

        // Find the return variable
        AstVar* const returnVarp = VN_AS(funcp->fvarp(), Var);

        // Calculate coverage: (covered_count / total_bins) * 100.0
        // return_var = (double)covered_count / (double)total_bins * 100.0

        // Cast covered_count to real/double
        AstNodeExpr* const coveredReal
            = new AstIToRD{fl, new AstVarRef{fl, coveredCountp, VAccess::READ}};

        // Create total bins as a double constant
        AstNodeExpr* const totalReal
            = new AstConst{fl, AstConst::RealDouble{}, static_cast<double>(totalBins)};

        // Divide using AstDivD (double division that emits native /)
        AstNodeExpr* const divExpr = new AstDivD{fl, coveredReal, totalReal};

        // Multiply by 100 using AstMulD (double multiplication that emits native *)
        AstNodeExpr* const hundredConst = new AstConst{fl, AstConst::RealDouble{}, 100.0};
        AstNodeExpr* const coverageExpr = new AstMulD{fl, hundredConst, divExpr};

        // Assign to return variable
        funcp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, returnVarp, VAccess::WRITE}, coverageExpr});

        UINFO(6, "    Added coverage computation to " << funcp->name() << " with " << totalBins
                                                      << " bins (excluding ignore/illegal)");
    }

    void generateCoverageRegistration() {
        // Generate VL_COVER_INSERT calls for each bin in the covergroup
        // This registers the bins with the coverage database so they can be reported

        UINFO(4,
              "  Generating coverage database registration for " << m_binInfos.size() << " bins");

        if (m_binInfos.empty()) return;

        // For each bin, generate a VL_COVER_INSERT call
        // The calls use CCall nodes to invoke VL_COVER_INSERT macro
        for (const BinInfo& binInfo : m_binInfos) {
            AstVar* const varp = binInfo.varp;
            AstCoverBin* const binp = binInfo.binp;
            AstCoverpoint* const coverpointp = binInfo.coverpointp;
            AstCoverCross* const crossp = binInfo.crossp;

            FileLine* const fl = binp->fileline();

            // Build hierarchical name: covergroup.coverpoint.bin or covergroup.cross.bin
            std::string hierName = m_covergroupp->name();
            const std::string binName = binp->name();

            if (coverpointp) {
                // Coverpoint bin: use coverpoint name or generate from expression
                std::string cpName = coverpointp->name();
                if (cpName.empty()) {
                    // Unlabeled coverpoint: name comes from its expression (always a VarRef)
                    UASSERT_OBJ(coverpointp->exprp(), coverpointp,
                                "Coverpoint without expression and without name");
                    cpName = coverpointp->exprp()->name();
                    UASSERT_OBJ(!cpName.empty(), coverpointp,
                                "Coverpoint expression has empty name");
                }
                hierName += "." + cpName;
            } else {
                // Cross bin: grammar always provides a name (user label or auto "__crossN")
                hierName += "." + crossp->name();
            }
            hierName += "." + binName;

            // Generate: VL_COVER_INSERT(contextp, hier, &binVar, "page", "v_covergroup/...", ...)

            UINFO(6, "    Registering bin: " << hierName << " -> " << varp->name());

            // Build the coverage insert as a C statement mixing literal text with a proper
            // AstVarRef for the bin variable.  Using AstVarRef (with selfPointer=This) lets
            // V3Name apply __PVT__ mangling and the emitter apply nameProtect(), which also
            // handles --protect-ids correctly.  The vlSymsp->_vm_contextp__ path is the
            // established convention used by the existing __vlCoverInsert helper.
            // Use "page" field with v_covergroup prefix so the coverage type is identified
            // correctly (consistent with code coverage).
            const std::string pageName = "v_covergroup/" + m_covergroupp->name();
            AstCStmt* const cstmtp = new AstCStmt{fl};
            cstmtp->add("VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), "
                        "\""
                        + hierName + "\", &(");
            AstVarRef* const binVarRefp = new AstVarRef{fl, varp, VAccess::READ};
            binVarRefp->selfPointer(VSelfPointerText{VSelfPointerText::This{}});
            cstmtp->add(binVarRefp);
            cstmtp->add("), \"page\", \"" + pageName
                        + "\", "
                          "\"filename\", \""
                        + fl->filename()
                        + "\", "
                          "\"lineno\", \""
                        + std::to_string(fl->lineno())
                        + "\", "
                          "\"column\", \""
                        + std::to_string(fl->firstColumn()) + "\", ");
            const std::string crossSuffix = crossp ? ", \"cross\", \"1\"" : "";
            if (binp->binsType() == VCoverBinsType::BINS_IGNORE) {
                cstmtp->add("\"bin\", \"" + binName + "\", \"bin_type\", \"ignore\"" + crossSuffix
                            + ");");
            } else if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                cstmtp->add("\"bin\", \"" + binName + "\", \"bin_type\", \"illegal\"" + crossSuffix
                            + ");");
            } else {
                cstmtp->add("\"bin\", \"" + binName + "\"" + crossSuffix + ");");
            }

            // Add to constructor
            m_constructorp->addStmtsp(cstmtp);

            UINFO(6, "      Added VL_COVER_INSERT call to constructor");
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        UINFO(9, "Visiting class: " << nodep->name() << " isCovergroup=" << nodep->isCovergroup());
        if (nodep->isCovergroup()) {
            VL_RESTORER(m_covergroupp);
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
            if (m_sampleFuncp) m_sampleFuncp->isCovergroupSample(true);
            m_constructorp = VN_CAST(m_memberMap.findMember(nodep, "new"), Func);
            UINFO(9, "Found sample() method: " << (m_sampleFuncp ? "yes" : "no"));
            UINFO(9, "Found constructor: " << (m_constructorp ? "yes" : "no"));

            iterateChildren(nodep);
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
