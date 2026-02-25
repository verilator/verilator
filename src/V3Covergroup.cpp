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
#include "V3MemberMap.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Functional coverage visitor

class FunctionalCoverageVisitor final : public VNVisitor {
    // STATE
    AstClass* m_covergroupp = nullptr;  // Current covergroup being processed
    AstFunc* m_sampleFuncp = nullptr;  // Current sample() function
    AstFunc* m_constructorp = nullptr;  // Current constructor
    std::vector<AstCoverpoint*> m_coverpoints;  // Coverpoints in current covergroup
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

    // Track coverpoints that need previous value tracking (for transition bins)
    std::map<AstCoverpoint*, AstVar*> m_prevValueVars;  // coverpoint -> prev_value variable

    // Track sequence state variables for multi-value transition bins
    // Key is bin pointer, value is state position variable
    std::map<AstCoverBin*, AstVar*> m_seqStateVars;  // transition bin -> sequence state variable

    VMemberMap m_memberMap;  // Member names cached for fast lookup

    // METHODS
    void clearBinInfos() {
        // Delete pseudo-bins created for cross coverage (they're never inserted into the AST)
        for (const BinInfo& bi : m_binInfos) {
            if (!bi.coverpointp && bi.crossp && bi.binp) {
                VL_DO_DANGLING(bi.binp->deleteTree(), bi.binp);
            }
        }
        m_binInfos.clear();
    }

    void processCovergroup() {
        if (!m_covergroupp) return;

        UINFO(4, "Processing covergroup: " << m_covergroupp->name() << " with "
                                           << m_coverpoints.size() << " coverpoints and "
                                           << m_coverCrosses.size() << " crosses" << endl);

        // Clear bin info for this covergroup (deleting any orphaned cross pseudo-bins)
        clearBinInfos();

        // For each coverpoint, generate sampling code
        for (AstCoverpoint* cpp : m_coverpoints) { generateCoverpointCode(cpp); }

        // For each cross, generate sampling code
        for (AstCoverCross* crossp : m_coverCrosses) { generateCrossCode(crossp); }

        // Generate coverage computation code (even for empty covergroups)
        generateCoverageComputationCode();

        // TODO: Generate instance registry infrastructure for static get_coverage()
        // This requires:
        // - Static registry members (t_instances, s_mutex)
        // - registerInstance() / unregisterInstance() methods
        // - Proper C++ emission in EmitC backend
        // For now, get_coverage() returns 0.0 (placeholder)

        // Generate coverage database registration if coverage is enabled
        if (v3Global.opt.coverage()) { generateCoverageRegistration(); }

        // Clean up orphaned cross pseudo-bins now that we're done with them
        clearBinInfos();
    }

    void expandAutomaticBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp) {
        // Find and expand any automatic bins
        AstNode* prevBinp = nullptr;
        for (AstNode* binp = coverpointp->binsp(); binp;) {
            AstCoverBin* const cbinp = VN_CAST(binp, CoverBin);
            AstNode* nextBinp = binp->nextp();

            if (cbinp && cbinp->binsType() == VCoverBinsType::AUTO) {
                UINFO(4, "  Expanding automatic bin: " << cbinp->name() << endl);

                // Get array size - must be a constant
                AstNodeExpr* sizep = cbinp->arraySizep();
                if (!sizep) {
                    cbinp->v3error("Automatic bins requires array size [N]");  // LCOV_EXCL_LINE
                    binp = nextBinp;
                    continue;
                }

                // Evaluate as constant
                const AstConst* constp = VN_CAST(sizep, Const);
                if (!constp) {
                    cbinp->v3error("Automatic bins array size must be a constant");
                    binp = nextBinp;
                    continue;
                }

                const int numBins = constp->toSInt();
                if (numBins <= 0 || numBins > 10000) {
                    cbinp->v3error("Automatic bins array size must be 1-10000, got "
                                   + std::to_string(numBins));
                    binp = nextBinp;
                    continue;
                }

                // Calculate range division
                const int width = exprp->width();
                const uint64_t maxVal = (width >= 64) ? UINT64_MAX : ((1ULL << width) - 1);
                const uint64_t binSize = (maxVal + 1) / numBins;

                UINFO(4, "    Width=" << width << " maxVal=" << maxVal << " numBins=" << numBins
                                      << " binSize=" << binSize << endl);

                // Create expanded bins
                for (int i = 0; i < numBins; i++) {
                    const uint64_t lo = i * binSize;
                    const uint64_t hi = (i == numBins - 1) ? maxVal : ((i + 1) * binSize - 1);

                    // Create constants for range
                    AstConst* loConstp
                        = new AstConst{cbinp->fileline(), V3Number(cbinp->fileline(), width, lo)};
                    AstConst* hiConstp
                        = new AstConst{cbinp->fileline(), V3Number(cbinp->fileline(), width, hi)};

                    // Create InsideRange [lo:hi]
                    AstInsideRange* rangep
                        = new AstInsideRange{cbinp->fileline(), loConstp, hiConstp};
                    rangep->dtypeFrom(exprp);  // Set dtype from coverpoint expression

                    // Create new bin
                    const string binName = cbinp->name() + "[" + std::to_string(i) + "]";
                    AstCoverBin* newBinp
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
                binp->unlinkFrBack();
                VL_DO_DANGLING(binp->deleteTree(), binp);
            } else {
                prevBinp = binp;
            }

            binp = nextBinp;
        }
    }

    // Extract option values from a coverpoint
    int getCoverpointAtLeast(AstCoverpoint* coverpointp) {
        // Look for option.at_least in coverpoint options
        for (AstNode* optionp = coverpointp->optionsp(); optionp; optionp = optionp->nextp()) {
            if (AstCoverOption* optp = VN_CAST(optionp, CoverOption)) {
                if (optp->optionType() == VCoverOptionType::AT_LEAST) {
                    // Extract the value from the option expression
                    if (AstConst* constp = VN_CAST(optp->valuep(), Const)) {
                        return constp->toSInt();
                    }
                }
            }
        }
        return 1;  // Default: at least 1 hit required
    }

    // Get auto_bin_max option value (check coverpoint options, then covergroup)
    int getAutoBinMax(AstCoverpoint* coverpointp) {
        // Check coverpoint options first
        for (AstNode* optionp = coverpointp->optionsp(); optionp; optionp = optionp->nextp()) {
            if (AstCoverOption* optp = VN_CAST(optionp, CoverOption)) {
                if (optp->optionType() == VCoverOptionType::AUTO_BIN_MAX) {
                    if (AstConst* constp = VN_CAST(optp->valuep(), Const)) {
                        return constp->toSInt();
                    }
                }
            }
        }
        // Check covergroup-level option stored in AstClass
        if (m_covergroupp && m_covergroupp->cgAutoBinMax() >= 0) {
            // Value was explicitly set (>= 0)
            return m_covergroupp->cgAutoBinMax();
        }
        return 64;  // Default per IEEE 1800-2017
    }

    // Extract values to exclude from automatic bins (from ignore_bins and illegal_bins)
    std::set<uint64_t> getExcludedValues(AstCoverpoint* coverpointp) {
        std::set<uint64_t> excluded;

        // Scan existing bins for ignore/illegal types
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* cbinp = VN_CAST(binp, CoverBin);
            if (!cbinp) continue;

            VCoverBinsType btype = cbinp->binsType();
            if (btype != VCoverBinsType::BINS_IGNORE && btype != VCoverBinsType::BINS_ILLEGAL) {
                continue;
            }

            // Extract values from the bin's range expression
            if (AstNode* rangep = cbinp->rangesp()) { extractValuesFromRange(rangep, excluded); }
        }

        return excluded;
    }

    // Extract individual values from a range expression
    void extractValuesFromRange(AstNode* nodep, std::set<uint64_t>& values) {
        if (!nodep) return;

        if (AstConst* constp = VN_CAST(nodep, Const)) {
            // Single constant value
            values.insert(constp->toUQuad());
        } else if (AstInsideRange* rangep = VN_CAST(nodep, InsideRange)) {
            // Range [lo:hi]
            AstConst* loConstp = VN_CAST(rangep->lhsp(), Const);
            AstConst* hiConstp = VN_CAST(rangep->rhsp(), Const);
            if (loConstp && hiConstp) {
                uint64_t lo = loConstp->toUQuad();
                uint64_t hi = hiConstp->toUQuad();
                // Add all values in range (but limit to reasonable size)
                if (hi - lo < 1000) {  // Sanity check
                    for (uint64_t v = lo; v <= hi && v <= lo + 1000; v++) { values.insert(v); }
                }
            }
        }

        // Recurse into list of nodes
        extractValuesFromRange(nodep->op1p(), values);
        extractValuesFromRange(nodep->op2p(), values);
        extractValuesFromRange(nodep->op3p(), values);
        extractValuesFromRange(nodep->op4p(), values);
    }

    // Check if coverpoint has any regular bins (not just ignore/illegal)
    bool hasRegularBins(AstCoverpoint* coverpointp) {
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            if (AstCoverBin* cbinp = VN_CAST(binp, CoverBin)) {
                VCoverBinsType btype = cbinp->binsType();
                if (btype != VCoverBinsType::BINS_IGNORE
                    && btype != VCoverBinsType::BINS_ILLEGAL) {
                    return true;
                }
            }
        }
        return false;
    }

    // Create implicit automatic bins when coverpoint has no explicit regular bins
    void createImplicitAutoBins(AstCoverpoint* coverpointp, AstNodeExpr* exprp) {
        // If already has regular bins, nothing to do
        if (hasRegularBins(coverpointp)) return;

        UINFO(4, "  Creating implicit automatic bins for coverpoint: " << coverpointp->name()
                                                                       << endl);

        // Get excluded values from ignore_bins and illegal_bins
        std::set<uint64_t> excluded = getExcludedValues(coverpointp);

        if (!excluded.empty()) {
            UINFO(4, "    Found " << excluded.size() << " excluded values" << endl);
        }

        // Get auto_bin_max option
        const int autoBinMax = getAutoBinMax(coverpointp);
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
                              << autoBinMax << " creating " << numBins << " bins" << endl);

        // Strategy: Create bins for each value (if numValidValues <= autoBinMax)
        // or create range bins that avoid excluded values
        if (numValidValues <= static_cast<uint64_t>(autoBinMax)) {
            // Create one bin per valid value
            int binCount = 0;
            for (uint64_t v = 0; v <= maxVal && binCount < numBins; v++) {
                // Skip excluded values
                if (excluded.find(v) != excluded.end()) continue;

                // Create single-value bin
                AstConst* valConstp = new AstConst{coverpointp->fileline(),
                                                   V3Number(coverpointp->fileline(), width, v)};
                AstConst* valConstp2 = new AstConst{coverpointp->fileline(),
                                                    V3Number(coverpointp->fileline(), width, v)};

                AstInsideRange* rangep
                    = new AstInsideRange{coverpointp->fileline(), valConstp, valConstp2};
                rangep->dtypeFrom(exprp);

                const string binName = "auto_" + std::to_string(binCount);
                AstCoverBin* newBinp
                    = new AstCoverBin{coverpointp->fileline(), binName, rangep, false, false};

                coverpointp->addBinsp(newBinp);
                binCount++;
            }
            UINFO(4, "    Created " << binCount << " single-value automatic bins" << endl);
        } else {
            // Create range bins (more complex - need to handle excluded values in ranges)
            // For simplicity, create bins and let excluded values not match any bin
            const uint64_t binSize = (maxVal + 1) / numBins;

            for (int i = 0; i < numBins; i++) {
                const uint64_t lo = i * binSize;
                const uint64_t hi = (i == numBins - 1) ? maxVal : ((i + 1) * binSize - 1);

                // Check if entire range is excluded
                bool anyValid = false;
                for (uint64_t v = lo; v <= hi && v <= lo + 1000; v++) {
                    if (excluded.find(v) == excluded.end()) {
                        anyValid = true;
                        break;
                    }
                }

                if (!anyValid && (hi - lo < 1000)) {
                    // Skip this bin entirely if all values are excluded
                    UINFO(4, "    Skipping bin [" << lo << ":" << hi << "] - all values excluded"
                                                  << endl);
                    continue;
                }

                // Create constants for range
                AstConst* loConstp = new AstConst{coverpointp->fileline(),
                                                  V3Number(coverpointp->fileline(), width, lo)};
                AstConst* hiConstp = new AstConst{coverpointp->fileline(),
                                                  V3Number(coverpointp->fileline(), width, hi)};

                // Create InsideRange [lo:hi]
                AstInsideRange* rangep
                    = new AstInsideRange{coverpointp->fileline(), loConstp, hiConstp};
                rangep->dtypeFrom(exprp);

                // Create bin name
                const string binName = "auto_" + std::to_string(i);
                AstCoverBin* newBinp
                    = new AstCoverBin{coverpointp->fileline(), binName, rangep, false, false};

                // Add to coverpoint
                coverpointp->addBinsp(newBinp);
            }

            UINFO(4, "    Created range-based automatic bins" << endl);
        }
    }

    // Check if coverpoint has any transition bins and create previous value variable if needed
    bool hasTransitionBins(AstCoverpoint* coverpointp) {
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* cbinp = VN_CAST(binp, CoverBin);
            if (cbinp && cbinp->binsType() == VCoverBinsType::TRANSITION) { return true; }
        }
        return false;
    }

    // Create previous value variable for transition tracking
    AstVar* createPrevValueVar(AstCoverpoint* coverpointp, AstNodeExpr* exprp) {
        // Check if already created
        auto it = m_prevValueVars.find(coverpointp);
        if (it != m_prevValueVars.end()) { return it->second; }

        // Create variable to store previous sampled value
        const string varName = "__Vprev_" + coverpointp->name();
        AstVar* prevVarp
            = new AstVar{coverpointp->fileline(), VVarType::MEMBER, varName, exprp->dtypep()};
        prevVarp->isStatic(false);
        m_covergroupp->addMembersp(prevVarp);

        UINFO(4, "    Created previous value variable: " << varName << endl);

        // Initialize to zero in constructor
        AstNodeExpr* initExprp
            = new AstConst{prevVarp->fileline(), AstConst::WidthedValue{}, prevVarp->width(), 0};
        AstNodeStmt* initStmtp = new AstAssign{
            prevVarp->fileline(), new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::WRITE},
            initExprp};
        m_constructorp->addStmtsp(initStmtp);

        m_prevValueVars[coverpointp] = prevVarp;
        return prevVarp;
    }

    // Create state position variable for multi-value transition bins
    // Tracks position in sequence: 0=not started, 1=seen first item, etc.
    AstVar* createSequenceStateVar(AstCoverpoint* coverpointp, AstCoverBin* binp) {
        // Check if already created
        auto it = m_seqStateVars.find(binp);
        if (it != m_seqStateVars.end()) { return it->second; }

        // Create variable to track sequence position
        const string varName = "__Vseqpos_" + coverpointp->name() + "_" + binp->name();
        // Use 8-bit integer for state position (sequences rarely > 255 items)
        AstVar* stateVarp
            = new AstVar{binp->fileline(), VVarType::MEMBER, varName, VFlagLogicPacked{}, 8};
        stateVarp->isStatic(false);
        m_covergroupp->addMembersp(stateVarp);

        UINFO(4, "    Created sequence state variable: " << varName << endl);

        // Initialize to 0 (not started) in constructor
        AstNodeStmt* initStmtp = new AstAssign{
            stateVarp->fileline(), new AstVarRef{stateVarp->fileline(), stateVarp, VAccess::WRITE},
            new AstConst{stateVarp->fileline(), AstConst::WidthedValue{}, 8, 0}};
        m_constructorp->addStmtsp(initStmtp);

        m_seqStateVars[binp] = stateVarp;
        return stateVarp;
    }

    void generateCoverpointCode(AstCoverpoint* coverpointp) {
        if (!m_sampleFuncp || !m_constructorp) {
            coverpointp->v3warn(E_UNSUPPORTED,
                                "Coverpoint without sample() or constructor");  // LCOV_EXCL_LINE
            return;
        }

        UINFO(4, "  Generating code for coverpoint: " << coverpointp->name() << endl);

        // Get the coverpoint expression
        AstNodeExpr* exprp = coverpointp->exprp();
        if (!exprp) {
            coverpointp->v3warn(E_UNSUPPORTED, "Coverpoint without expression");  // LCOV_EXCL_LINE
            return;
        }

        // Expand automatic bins before processing
        expandAutomaticBins(coverpointp, exprp);

        // Create implicit automatic bins if no regular bins exist
        createImplicitAutoBins(coverpointp, exprp);

        // Extract option values for this coverpoint
        int atLeastValue = getCoverpointAtLeast(coverpointp);
        UINFO(6, "    Coverpoint at_least = " << atLeastValue << endl);

        // Generate member variables and matching code for each bin
        // Process in two passes: first non-default bins, then default bins
        std::vector<AstCoverBin*> defaultBins;
        int binCount = 0;
        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            if (++binCount > 1000) {
                coverpointp->v3error("Too many bins or infinite loop detected in bin iteration");
                break;
            }
            AstCoverBin* const cbinp = VN_CAST(binp, CoverBin);
            if (!cbinp) continue;

            // Defer default bins to second pass
            if (cbinp->binsType() == VCoverBinsType::DEFAULT) {
                defaultBins.push_back(cbinp);
                continue;
            }

            // Handle array bins: create separate bin for each value/transition
            if (cbinp->isArray()) {
                if (cbinp->binsType() == VCoverBinsType::TRANSITION) {
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
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created member variable: "
                         << varName << " type=" << static_cast<int>(cbinp->binsType())
                         << (cbinp->binsType() == VCoverBinsType::BINS_IGNORE    ? " (IGNORE)"
                             : cbinp->binsType() == VCoverBinsType::BINS_ILLEGAL ? " (ILLEGAL)"
                                                                                 : " (USER)")
                         << endl);

            // Track this bin for coverage computation with at_least value
            m_binInfos.push_back(BinInfo(cbinp, varp, atLeastValue, coverpointp));

            // Note: Coverage database registration happens later via VL_COVER_INSERT
            // (see generateCoverageDeclarations() method around line 1164)
            // Classes use "v_funccov/" hier prefix vs modules

            // Generate bin matching code in sample()
            // Handle transition bins specially
            if (cbinp->binsType() == VCoverBinsType::TRANSITION) {
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
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created default bin variable: " << varName << endl);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(defBinp, varp, atLeastValue, coverpointp));

            // Generate matching code: if (NOT (bin1 OR bin2 OR ... OR binN))
            generateDefaultBinMatchCode(coverpointp, defBinp, exprp, varp);
        }

        // After all bins processed, if coverpoint has transition bins, update previous value
        if (hasTransitionBins(coverpointp)) {
            AstVar* prevVarp = m_prevValueVars[coverpointp];
            // Generate: __Vprev_cpname = current_value;
            AstNodeStmt* updateStmtp
                = new AstAssign{coverpointp->fileline(),
                                new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::WRITE},
                                exprp->cloneTree(false)};
            m_sampleFuncp->addStmtsp(updateStmtp);
            UINFO(4, "    Added previous value update at end of sample()" << endl);
        }
    }

    void generateBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* binp, AstNodeExpr* exprp,
                              AstVar* hitVarp) {
        UINFO(4, "    Generating bin match for: " << binp->name() << endl);

        // Build the bin matching condition using the shared function
        AstNodeExpr* fullCondp = buildBinCondition(binp, exprp);

        if (!fullCondp) {
            UINFO(4, "      No valid conditions generated" << endl);
            return;
        }

        // Apply iff condition if present - wraps the bin match condition
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            UINFO(6, "      Adding iff condition" << endl);
            fullCondp = new AstAnd{binp->fileline(), iffp->cloneTree(false), fullCondp};
        }

        // Create the increment statement
        AstNode* stmtp = new AstAssign{
            binp->fileline(), new AstVarRef{binp->fileline(), hitVarp, VAccess::WRITE},
            new AstAdd{binp->fileline(), new AstVarRef{binp->fileline(), hitVarp, VAccess::READ},
                       new AstConst{binp->fileline(), AstConst::WidthedValue{}, 32, 1}}};

        // For illegal_bins, add an error message
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            const string errMsg = "Illegal bin '" + binp->name() + "' hit in coverpoint '"
                                  + coverpointp->name() + "'";
            AstDisplay* errorp = new AstDisplay{binp->fileline(), VDisplayType::DT_ERROR, errMsg,
                                                nullptr, nullptr};
            errorp->fmtp()->timeunit(m_covergroupp->timeunit());
            stmtp = stmtp->addNext(errorp);
            stmtp = stmtp->addNext(new AstStop{binp->fileline(), true});
        }

        // Create: if (condition) { hitVar++; [error if illegal] }
        AstIf* const ifp = new AstIf{binp->fileline(), fullCondp, stmtp, nullptr};

        UINFO(4, "      Adding bin match if statement to sample function" << endl);
        if (!m_sampleFuncp)
            binp->v3fatalSrc("m_sampleFuncp is null when trying to add bin match code");
        m_sampleFuncp->addStmtsp(ifp);
        UINFO(4, "      Successfully added if statement for bin: " << binp->name() << endl);
    }

    // Generate matching code for default bins
    // Default bins match when value doesn't match any other explicit bin
    void generateDefaultBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* defBinp,
                                     AstNodeExpr* exprp, AstVar* hitVarp) {
        UINFO(4, "    Generating default bin match for: " << defBinp->name() << endl);

        // Build OR of all non-default, non-ignore bins
        AstNodeExpr* anyBinMatchp = nullptr;

        for (AstNode* binp = coverpointp->binsp(); binp; binp = binp->nextp()) {
            AstCoverBin* const cbinp = VN_CAST(binp, CoverBin);
            if (!cbinp) continue;

            // Skip default, ignore, and illegal bins
            if (cbinp->binsType() == VCoverBinsType::DEFAULT
                || cbinp->binsType() == VCoverBinsType::BINS_IGNORE
                || cbinp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                continue;
            }

            // Build condition for this bin
            AstNodeExpr* binCondp = buildBinCondition(cbinp, exprp);
            if (!binCondp) continue;

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
        AstNode* stmtp = new AstAssign{
            defBinp->fileline(), new AstVarRef{defBinp->fileline(), hitVarp, VAccess::WRITE},
            new AstAdd{defBinp->fileline(),
                       new AstVarRef{defBinp->fileline(), hitVarp, VAccess::READ},
                       new AstConst{defBinp->fileline(), AstConst::WidthedValue{}, 32, 1}}};

        // Create if statement
        AstIf* const ifp = new AstIf{defBinp->fileline(), defaultCondp, stmtp, nullptr};

        if (!m_sampleFuncp) defBinp->v3fatalSrc("m_sampleFuncp is null for default bin");
        m_sampleFuncp->addStmtsp(ifp);
        UINFO(4, "      Successfully added default bin if statement" << endl);
    }

    // Generate matching code for transition bins
    // Transition bins match sequences like: (val1 => val2 => val3)
    void generateTransitionBinMatchCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                        AstNodeExpr* exprp, AstVar* hitVarp) {
        UINFO(4, "    Generating transition bin match for: " << binp->name() << endl);

        // Get the (single) transition set
        AstCoverTransSet* transSetp = binp->transp();
        if (!transSetp) {
            binp->v3error("Transition bin without transition set");  // LCOV_EXCL_LINE
            return;
        }

        // Use the helper function to generate code for this transition
        generateSingleTransitionCode(coverpointp, binp, exprp, hitVarp, transSetp);
    }

    // Generate state machine code for multi-value transition sequences
    // Handles transitions like (1 => 2 => 3 => 4)
    void generateMultiValueTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                          AstNodeExpr* exprp, AstVar* hitVarp,
                                          const std::vector<AstCoverTransItem*>& items) {
        UINFO(4,
              "    Generating multi-value transition state machine for: " << binp->name() << endl);
        UINFO(4, "      Sequence length: " << items.size() << " items" << endl);

        // Create state position variable
        AstVar* stateVarp = createSequenceStateVar(coverpointp, binp);

        // Build case statement with N cases (one for each state 0 to N-1)
        // State 0: Not started, looking for first item
        // State 1 to N-1: In progress, looking for next item

        AstCase* casep
            = new AstCase{binp->fileline(), VCaseType::CT_CASE,
                          new AstVarRef{stateVarp->fileline(), stateVarp, VAccess::READ}, nullptr};

        // Generate each case item in the switch statement
        for (size_t state = 0; state < items.size(); ++state) {
            AstCaseItem* caseItemp = generateTransitionStateCase(coverpointp, binp, exprp, hitVarp,
                                                                 stateVarp, items, state);

            if (caseItemp) { casep->addItemsp(caseItemp); }
        }

        m_sampleFuncp->addStmtsp(casep);
        UINFO(4, "      Successfully added multi-value transition state machine" << endl);
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
        AstNodeExpr* matchCondp
            = buildTransitionItemCondition(items[state], exprp->cloneTree(false));
        if (!matchCondp) {
            binp->v3error("Could not build transition condition for state "  // LCOV_EXCL_LINE
                          + std::to_string(state));  // LCOV_EXCL_LINE
            return nullptr;
        }

        // Apply iff condition if present
        if (AstNodeExpr* iffp = coverpointp->iffp()) {
            matchCondp = new AstAnd{fl, iffp->cloneTree(false), matchCondp};
        }

        AstNodeStmt* matchActionp = nullptr;

        if (state == items.size() - 1) {
            // Last state: sequence complete!
            // Increment bin counter
            matchActionp
                = new AstAssign{fl, new AstVarRef{fl, hitVarp, VAccess::WRITE},
                                new AstAdd{fl, new AstVarRef{fl, hitVarp, VAccess::READ},
                                           new AstConst{fl, AstConst::WidthedValue{}, 32, 1}}};

            // For illegal_bins, add error message
            if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                const string errMsg = "Illegal transition bin '" + binp->name()
                                      + "' hit in coverpoint '" + coverpointp->name() + "'";
                AstDisplay* errorp
                    = new AstDisplay{fl, VDisplayType::DT_ERROR, errMsg, nullptr, nullptr};
                errorp->fmtp()->timeunit(m_covergroupp->timeunit());
                matchActionp = matchActionp->addNext(errorp);
                matchActionp = matchActionp->addNext(new AstStop{fl, true});
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
            AstNodeExpr* restartCondp
                = buildTransitionItemCondition(items[0], exprp->cloneTree(false));

            if (restartCondp) {
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
            } else {
                // Can't build restart condition, just reset
                noMatchActionp = new AstAssign{fl, new AstVarRef{fl, stateVarp, VAccess::WRITE},
                                               new AstConst{fl, AstConst::WidthedValue{}, 8, 0}};
            }
        }
        // For state 0, no action needed if no match (stay in state 0)

        // Combine into if-else
        AstNodeStmt* stmtp = new AstIf{fl, matchCondp, matchActionp, noMatchActionp};

        // Create case item for this state value
        AstCaseItem* caseItemp = new AstCaseItem{
            fl, new AstConst{fl, AstConst::WidthedValue{}, 8, static_cast<uint32_t>(state)},
            stmtp};

        return caseItemp;
    }

    // Build condition for a single transition item
    // Returns expression that checks if value matches the item's value/range list
    AstNodeExpr* buildTransitionItemCondition(AstCoverTransItem* itemp, AstNodeExpr* exprp) {
        AstNodeExpr* condp = nullptr;

        // Get values from the transition item
        for (AstNode* valp = itemp->valuesp(); valp; valp = valp->nextp()) {
            AstNodeExpr* singleCondp = nullptr;

            if (AstConst* constp = VN_CAST(valp, Const)) {
                // Simple value: check equality
                singleCondp = new AstEq{constp->fileline(), exprp->cloneTree(false),
                                        constp->cloneTree(false)};
            } else if (AstRange* rangep = VN_CAST(valp, Range)) {
                // Range [min:max]: check if value is in range (use signed if expr is signed)
                if (exprp->isSigned()) {
                    singleCondp
                        = new AstAnd{rangep->fileline(),
                                     new AstGteS{rangep->fileline(), exprp->cloneTree(false),
                                                 rangep->leftp()->cloneTree(false)},
                                     new AstLteS{rangep->fileline(), exprp->cloneTree(false),
                                                 rangep->rightp()->cloneTree(false)}};
                } else {
                    // For unsigned, skip >= 0 check as it's always true
                    AstNodeExpr* minExprp = rangep->leftp();
                    AstNodeExpr* maxExprp = rangep->rightp();
                    AstConst* minConstp = VN_CAST(minExprp, Const);
                    AstConst* maxConstp = VN_CAST(maxExprp, Const);
                    const int exprWidth = exprp->widthMin();
                    bool skipLowerCheck = (minConstp && minConstp->toUQuad() == 0);
                    bool skipUpperCheck = false;
                    if (maxConstp && exprWidth > 0 && exprWidth <= 64) {
                        const uint64_t maxVal = (exprWidth == 64) ? ~static_cast<uint64_t>(0)
                                                                  : ((1ULL << exprWidth) - 1ULL);
                        skipUpperCheck = (maxConstp->toUQuad() == maxVal);
                    }

                    if (skipLowerCheck && skipUpperCheck) {
                        singleCondp = new AstConst{rangep->fileline(), AstConst::BitTrue{}};
                    } else if (skipLowerCheck) {
                        // Only check upper bound for [0:max]
                        singleCondp = new AstLte{rangep->fileline(), exprp->cloneTree(false),
                                                 maxExprp->cloneTree(false)};
                    } else if (skipUpperCheck) {
                        // Only check lower bound when upper is maximal for the expression width
                        singleCondp = new AstGte{rangep->fileline(), exprp->cloneTree(false),
                                                 minExprp->cloneTree(false)};
                    } else {
                        singleCondp
                            = new AstAnd{rangep->fileline(),
                                         new AstGte{rangep->fileline(), exprp->cloneTree(false),
                                                    rangep->leftp()->cloneTree(false)},
                                         new AstLte{rangep->fileline(), exprp->cloneTree(false),
                                                    rangep->rightp()->cloneTree(false)}};
                    }
                }
            } else if (AstInsideRange* inrangep = VN_CAST(valp, InsideRange)) {
                // InsideRange [min:max]: similar to Range (use signed if expr is signed)
                if (exprp->isSigned()) {
                    singleCondp
                        = new AstAnd{inrangep->fileline(),
                                     new AstGteS{inrangep->fileline(), exprp->cloneTree(false),
                                                 inrangep->lhsp()->cloneTree(false)},
                                     new AstLteS{inrangep->fileline(), exprp->cloneTree(false),
                                                 inrangep->rhsp()->cloneTree(false)}};
                } else {
                    // For unsigned, skip >= 0 check as it's always true
                    AstNodeExpr* minExprp = inrangep->lhsp();
                    AstNodeExpr* maxExprp = inrangep->rhsp();
                    AstConst* minConstp = VN_CAST(minExprp, Const);
                    AstConst* maxConstp = VN_CAST(maxExprp, Const);
                    const int exprWidth = exprp->widthMin();
                    bool skipLowerCheck = (minConstp && minConstp->toUQuad() == 0);
                    bool skipUpperCheck = false;
                    if (maxConstp && exprWidth > 0 && exprWidth <= 64) {
                        const uint64_t maxVal = (exprWidth == 64) ? ~static_cast<uint64_t>(0)
                                                                  : ((1ULL << exprWidth) - 1ULL);
                        skipUpperCheck = (maxConstp->toUQuad() == maxVal);
                    }

                    if (skipLowerCheck && skipUpperCheck) {
                        singleCondp = new AstConst{inrangep->fileline(), AstConst::BitTrue{}};
                    } else if (skipLowerCheck) {
                        // Only check upper bound for [0:max]
                        singleCondp = new AstLte{inrangep->fileline(), exprp->cloneTree(false),
                                                 maxExprp->cloneTree(false)};
                    } else if (skipUpperCheck) {
                        // Only check lower bound when upper is maximal for the expression width
                        singleCondp = new AstGte{inrangep->fileline(), exprp->cloneTree(false),
                                                 minExprp->cloneTree(false)};
                    } else {
                        singleCondp
                            = new AstAnd{inrangep->fileline(),
                                         new AstGte{inrangep->fileline(), exprp->cloneTree(false),
                                                    inrangep->lhsp()->cloneTree(false)},
                                         new AstLte{inrangep->fileline(), exprp->cloneTree(false),
                                                    inrangep->rhsp()->cloneTree(false)}};
                    }
                }
            } else {
                // Unknown node type - try to handle as expression
                UINFO(4, "      Transition item has unknown value node type: " << valp->typeName()
                                                                               << endl);
                // For now, just skip unknown types - this prevents crashes
                continue;
            }

            // OR together multiple values
            if (singleCondp) {
                if (condp) {
                    condp = new AstOr{itemp->fileline(), condp, singleCondp};
                } else {
                    condp = singleCondp;
                }
            }
        }

        if (!condp) {
            // If no values were successfully processed, return nullptr
            // The caller will handle this error
            UINFO(4, "      No valid transition conditions could be built" << endl);
        }

        // Take ownership of exprp (used only for cloning above)
        VL_DO_DANGLING(exprp->deleteTree(), exprp);
        return condp;
    }

    // Generate multiple bins for array bins
    // Array bins create one bin per value in the range list
    void generateArrayBins(AstCoverpoint* coverpointp, AstCoverBin* arrayBinp, AstNodeExpr* exprp,
                           int atLeastValue) {
        UINFO(4, "    Generating array bins for: " << arrayBinp->name() << endl);

        // Extract all values from the range list
        std::vector<AstNodeExpr*> values;
        for (AstNode* rangep = arrayBinp->rangesp(); rangep; rangep = rangep->nextp()) {
            if (AstRange* const rangenodep = VN_CAST(rangep, Range)) {
                // For ranges [min:max], create bins for each value
                AstConst* const minConstp = VN_CAST(rangenodep->leftp(), Const);
                AstConst* const maxConstp = VN_CAST(rangenodep->rightp(), Const);
                if (minConstp && maxConstp) {
                    int minVal = minConstp->toSInt();
                    int maxVal = maxConstp->toSInt();
                    for (int val = minVal; val <= maxVal; ++val) {
                        values.push_back(
                            new AstConst{rangenodep->fileline(), AstConst::Signed32{}, val});
                    }
                } else {
                    arrayBinp->v3error("covergroup value range");
                    return;
                }
            } else if (AstInsideRange* const insideRangep = VN_CAST(rangep, InsideRange)) {
                // For InsideRange [min:max], create bins for each value
                AstConst* const minConstp = VN_CAST(insideRangep->lhsp(), Const);
                AstConst* const maxConstp = VN_CAST(insideRangep->rhsp(), Const);
                if (minConstp && maxConstp) {
                    int minVal = minConstp->toSInt();
                    int maxVal = maxConstp->toSInt();
                    UINFO(6, "      Expanding InsideRange [" << minVal << ":" << maxVal << "]"
                                                             << endl);
                    for (int val = minVal; val <= maxVal; ++val) {
                        values.push_back(
                            new AstConst{insideRangep->fileline(), AstConst::Signed32{}, val});
                    }
                } else {
                    arrayBinp->v3error("covergroup value range");
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
            m_covergroupp->addMembersp(varp);
            UINFO(4, "    Created array bin [" << index << "]: " << varName << endl);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(arrayBinp, varp, atLeastValue, coverpointp));

            // Generate matching code for this specific value
            generateArrayBinMatchCode(coverpointp, arrayBinp, exprp, varp, valuep);

            ++index;
        }

        UINFO(4, "    Generated " << index << " array bins" << endl);
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
        AstNode* stmtp = new AstAssign{
            binp->fileline(), new AstVarRef{binp->fileline(), hitVarp, VAccess::WRITE},
            new AstAdd{binp->fileline(), new AstVarRef{binp->fileline(), hitVarp, VAccess::READ},
                       new AstConst{binp->fileline(), AstConst::WidthedValue{}, 32, 1}}};

        // For illegal_bins, add error message
        if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
            const string errMsg = "Illegal bin hit in coverpoint '" + coverpointp->name() + "'";
            AstDisplay* errorp = new AstDisplay{binp->fileline(), VDisplayType::DT_ERROR, errMsg,
                                                nullptr, nullptr};
            errorp->fmtp()->timeunit(m_covergroupp->timeunit());
            stmtp = stmtp->addNext(errorp);
            stmtp = stmtp->addNext(new AstStop{binp->fileline(), true});
        }

        // Create if statement
        AstIf* const ifp = new AstIf{binp->fileline(), condp, stmtp, nullptr};

        if (!m_sampleFuncp) binp->v3fatalSrc("m_sampleFuncp is null for array bin");
        m_sampleFuncp->addStmtsp(ifp);
    }

    // Generate multiple bins for transition array bins
    // Array bins with transitions create one bin per transition sequence
    void generateTransitionArrayBins(AstCoverpoint* coverpointp, AstCoverBin* arrayBinp,
                                     AstNodeExpr* exprp, int atLeastValue) {
        UINFO(4, "    Generating transition array bins for: " << arrayBinp->name() << endl);

        // Extract all transition sets
        std::vector<AstCoverTransSet*> transSets;
        for (AstNode* transSetp = arrayBinp->transp(); transSetp; transSetp = transSetp->nextp()) {
            if (AstCoverTransSet* ts = VN_CAST(transSetp, CoverTransSet)) {
                transSets.push_back(ts);
            }
        }

        if (transSets.empty()) {
            arrayBinp->v3error("Transition array bin without transition sets");  // LCOV_EXCL_LINE
            return;
        }

        UINFO(4, "      Found " << transSets.size() << " transition sets" << endl);

        // Create a separate bin for each transition sequence
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
            m_covergroupp->addMembersp(varp);
            UINFO(4, "      Created transition array bin [" << index << "]: " << varName << endl);

            // Track for coverage computation
            m_binInfos.push_back(BinInfo(arrayBinp, varp, atLeastValue, coverpointp));

            // Generate matching code for this specific transition
            generateSingleTransitionCode(coverpointp, arrayBinp, exprp, varp, transSetp);

            ++index;
        }

        UINFO(4, "    Generated " << index << " transition array bins" << endl);
    }

    // Generate code for a single transition sequence (used by both regular and array bins)
    void generateSingleTransitionCode(AstCoverpoint* coverpointp, AstCoverBin* binp,
                                      AstNodeExpr* exprp, AstVar* hitVarp,
                                      AstCoverTransSet* transSetp) {
        UINFO(4, "      Generating code for transition sequence" << endl);

        // Get or create previous value variable
        AstVar* prevVarp = createPrevValueVar(coverpointp, exprp);

        if (!transSetp) {
            binp->v3error("Transition bin without transition set");  // LCOV_EXCL_LINE
            return;
        }

        // Get transition items (the sequence: item1 => item2 => item3)
        std::vector<AstCoverTransItem*> items;
        for (AstNode* itemp = transSetp->itemsp(); itemp; itemp = itemp->nextp()) {
            if (AstCoverTransItem* transp = VN_CAST(itemp, CoverTransItem)) {
                items.push_back(transp);
            }
        }

        if (items.empty()) {
            binp->v3error("Transition set without items");
            return;
        }

        // Check for unsupported repetition operators
        // Note: the grammar handles [*], [->], [=] at parse time via COVERIGN warning,
        // resulting in null AstCoverTransItem nodes which are filtered out above.
        // This check is therefore unreachable from normal SV parsing.
        for (AstCoverTransItem* item : items) {  // LCOV_EXCL_START
            if (item->repType() != VTransRepType::NONE) {
                binp->v3warn(E_UNSUPPORTED,
                             "Transition repetition operators ([*], [->], [=]) not yet supported");
                return;
            }
        }  // LCOV_EXCL_STOP

        if (items.size() == 1) {
            // Single item transition not valid (need at least 2 values for =>)
            binp->v3error("Transition requires at least two values");
            return;
        } else if (items.size() == 2) {
            // Simple two-value transition: (val1 => val2)
            // Use optimized direct comparison (no state machine needed)
            AstNodeExpr* cond1p = buildTransitionItemCondition(
                items[0], new AstVarRef{prevVarp->fileline(), prevVarp, VAccess::READ});
            AstNodeExpr* cond2p = buildTransitionItemCondition(items[1], exprp->cloneTree(false));

            if (!cond1p || !cond2p) {
                binp->v3error("Could not build transition conditions");  // LCOV_EXCL_LINE
                return;
            }

            // Combine: prev matches val1 AND current matches val2
            AstNodeExpr* fullCondp = new AstAnd{binp->fileline(), cond1p, cond2p};

            // Apply iff condition if present
            if (AstNodeExpr* iffp = coverpointp->iffp()) {
                fullCondp = new AstAnd{binp->fileline(), iffp->cloneTree(false), fullCondp};
            }

            // Create increment statement
            AstNode* stmtp = new AstAssign{
                binp->fileline(), new AstVarRef{binp->fileline(), hitVarp, VAccess::WRITE},
                new AstAdd{binp->fileline(),
                           new AstVarRef{binp->fileline(), hitVarp, VAccess::READ},
                           new AstConst{binp->fileline(), AstConst::WidthedValue{}, 32, 1}}};

            // For illegal_bins, add an error message
            if (binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                const string errMsg = "Illegal transition bin '" + binp->name()
                                      + "' hit in coverpoint '" + coverpointp->name() + "'";
                AstDisplay* errorp = new AstDisplay{binp->fileline(), VDisplayType::DT_ERROR,
                                                    errMsg, nullptr, nullptr};
                errorp->fmtp()->timeunit(m_covergroupp->timeunit());
                stmtp = stmtp->addNext(errorp);
                stmtp = stmtp->addNext(new AstStop{binp->fileline(), true});
            }

            // Create if statement
            AstIf* const ifp = new AstIf{binp->fileline(), fullCondp, stmtp, nullptr};
            m_sampleFuncp->addStmtsp(ifp);

            UINFO(4, "        Successfully added 2-value transition if statement" << endl);
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
        m_covergroupp->addMembersp(varp);

        UINFO(4, "      Created cross bin variable: " << varName << endl);

        // Track this for coverage computation
        AstCoverBin* pseudoBinp = new AstCoverBin{crossp->fileline(), binName,
                                                  static_cast<AstNode*>(nullptr), false, false};
        m_binInfos.push_back(BinInfo(pseudoBinp, varp, 1, nullptr, crossp));

        // Generate matching code: if (bin1 && bin2 && ... && binN) varName++;
        generateNWayCrossBinMatchCode(crossp, coverpointRefs, bins, varp);
    }

    // Generate matching code for N-way cross bin
    void generateNWayCrossBinMatchCode(AstCoverCross* crossp,
                                       const std::vector<AstCoverpoint*>& coverpointRefs,
                                       const std::vector<AstCoverBin*>& bins, AstVar* hitVarp) {
        UINFO(4, "      Generating " << bins.size() << "-way cross bin match" << endl);

        // Build combined condition by ANDing all bin conditions
        AstNodeExpr* fullCondp = nullptr;

        for (size_t i = 0; i < bins.size(); ++i) {
            AstNodeExpr* exprp = coverpointRefs[i]->exprp();
            if (!exprp) continue;

            AstNodeExpr* condp = buildBinCondition(bins[i], exprp);
            if (!condp) continue;

            if (fullCondp) {
                fullCondp = new AstAnd{crossp->fileline(), fullCondp, condp};
            } else {
                fullCondp = condp;
            }
        }

        if (!fullCondp) return;

        // Generate: if (cond1 && cond2 && ... && condN) { ++varName; }
        AstNodeStmt* incrp = new AstAssign{
            crossp->fileline(), new AstVarRef{crossp->fileline(), hitVarp, VAccess::WRITE},
            new AstAdd{crossp->fileline(),
                       new AstVarRef{crossp->fileline(), hitVarp, VAccess::READ},
                       new AstConst{crossp->fileline(), AstConst::WidthedValue{}, 32, 1}}};

        AstIf* const ifp = new AstIf{crossp->fileline(), fullCondp, incrp};
        m_sampleFuncp->addStmtsp(ifp);
    }

    void generateCrossCode(AstCoverCross* crossp) {
        if (!m_sampleFuncp || !m_constructorp) {
            crossp->v3warn(E_UNSUPPORTED,
                           "Cross coverage without sample() or constructor");  // LCOV_EXCL_LINE
            return;
        }

        UINFO(4, "  Generating code for cross: " << crossp->name() << endl);

        // Resolve coverpoint references and build list
        std::vector<AstCoverpoint*> coverpointRefs;
        AstNode* itemp = crossp->itemsp();
        while (itemp) {
            AstNode* nextp = itemp->nextp();
            AstCoverpointRef* const refp = VN_CAST(itemp, CoverpointRef);
            if (refp) {
                // Find the referenced coverpoint
                AstCoverpoint* foundCpp = nullptr;
                for (AstCoverpoint* cpp : m_coverpoints) {
                    if (cpp->name() == refp->name()) {
                        foundCpp = cpp;
                        break;
                    }
                }

                if (!foundCpp) {
                    refp->v3warn(COVERIGN,
                                 "Ignoring unsupported: cross references unknown coverpoint: "
                                     + refp->name());
                    // Delete the entire cross since we can't generate it
                    VL_DO_DANGLING(crossp->unlinkFrBack()->deleteTree(), crossp);
                    return;
                }

                coverpointRefs.push_back(foundCpp);

                // Delete the reference node - it's no longer needed
                VL_DO_DANGLING(refp->unlinkFrBack()->deleteTree(), refp);
            }
            itemp = nextp;
        }

        if (coverpointRefs.size() < 2) {
            crossp->v3warn(E_UNSUPPORTED,
                           "Cross coverage requires at least 2 coverpoints");  // LCOV_EXCL_LINE
            return;
        }

        UINFO(4, "    Generating " << coverpointRefs.size() << "-way cross" << endl);

        // Collect bins from all coverpoints (excluding ignore/illegal bins)
        std::vector<std::vector<AstCoverBin*>> allCpBins;
        for (AstCoverpoint* cpp : coverpointRefs) {
            std::vector<AstCoverBin*> cpBins;
            for (AstNode* binp = cpp->binsp(); binp; binp = binp->nextp()) {
                AstCoverBin* const cbinp = VN_CAST(binp, CoverBin);
                if (cbinp && cbinp->binsType() == VCoverBinsType::USER) {
                    cpBins.push_back(cbinp);
                }
            }
            UINFO(4, "      Found " << cpBins.size() << " bins in " << cpp->name() << endl);
            allCpBins.push_back(cpBins);
        }

        // Generate cross bins using Cartesian product
        generateCrossBinsRecursive(crossp, coverpointRefs, allCpBins, {}, 0);
    }

    AstNodeExpr* buildBinCondition(AstCoverBin* binp, AstNodeExpr* exprp) {
        // Get the range list from the bin
        AstNode* rangep = binp->rangesp();
        if (!rangep) return nullptr;

        // Check if this is a wildcard bin
        bool isWildcard = (binp->binsType() == VCoverBinsType::BINS_WILDCARD);

        // Build condition by OR-ing all ranges together
        AstNodeExpr* fullCondp = nullptr;

        for (AstNode* currRangep = rangep; currRangep; currRangep = currRangep->nextp()) {
            AstNodeExpr* exprClonep = exprp->cloneTree(false);
            AstNodeExpr* rangeCondp = nullptr;

            if (AstInsideRange* irp = VN_CAST(currRangep, InsideRange)) {
                AstNode* minp = irp->lhsp();
                AstNode* maxp = irp->rhsp();

                if (minp && maxp) {
                    AstNodeExpr* minExprp = VN_CAST(minp, NodeExpr);
                    AstNodeExpr* maxExprp = VN_CAST(maxp, NodeExpr);
                    if (minExprp && maxExprp) {
                        AstConst* minConstp = VN_CAST(minExprp, Const);
                        AstConst* maxConstp = VN_CAST(maxExprp, Const);

                        if (minConstp && maxConstp && minConstp->toSInt() == maxConstp->toSInt()) {
                            // Single value
                            if (isWildcard) {
                                rangeCondp = buildWildcardCondition(binp, exprClonep, minConstp);
                            } else {
                                rangeCondp = new AstEq{binp->fileline(), exprClonep,
                                                       minExprp->cloneTree(false)};
                            }
                        } else {
                            // Range - use signed comparisons if expression is signed
                            AstNodeExpr* gep;
                            AstNodeExpr* lep;
                            if (exprClonep->isSigned()) {
                                AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                                gep = new AstGteS{binp->fileline(), exprClonep,
                                                  minExprp->cloneTree(false)};
                                lep = new AstLteS{binp->fileline(), exprClone2p,
                                                  maxExprp->cloneTree(false)};
                                rangeCondp = new AstAnd{binp->fileline(), gep, lep};
                            } else {
                                // For unsigned, skip >= 0 check as it's always true
                                AstConst* minConstp = VN_CAST(minExprp, Const);
                                AstConst* maxConstp = VN_CAST(maxExprp, Const);
                                const int exprWidth = exprClonep->widthMin();
                                bool skipLowerCheck = (minConstp && minConstp->toUQuad() == 0);
                                bool skipUpperCheck = false;
                                if (maxConstp && exprWidth > 0 && exprWidth <= 64) {
                                    const uint64_t maxVal = (exprWidth == 64)
                                                                ? ~static_cast<uint64_t>(0)
                                                                : ((1ULL << exprWidth) - 1ULL);
                                    skipUpperCheck = (maxConstp->toUQuad() == maxVal);
                                }

                                if (skipLowerCheck && skipUpperCheck) {
                                    rangeCondp
                                        = new AstConst{binp->fileline(), AstConst::BitTrue{}};
                                } else if (skipLowerCheck) {
                                    // Only check upper bound for [0:max]
                                    lep = new AstLte{binp->fileline(), exprClonep,
                                                     maxExprp->cloneTree(false)};
                                    rangeCondp = lep;
                                } else if (skipUpperCheck) {
                                    // Only check lower bound when upper is maximal
                                    gep = new AstGte{binp->fileline(), exprClonep,
                                                     minExprp->cloneTree(false)};
                                    rangeCondp = gep;
                                } else {
                                    AstNodeExpr* const exprClone2p = exprp->cloneTree(false);
                                    lep = new AstLte{binp->fileline(), exprClone2p,
                                                     maxExprp->cloneTree(false)};
                                    gep = new AstGte{binp->fileline(), exprClonep,
                                                     minExprp->cloneTree(false)};
                                    rangeCondp = new AstAnd{binp->fileline(), gep, lep};
                                }
                            }
                        }
                    }
                }
            } else if (AstConst* constp = VN_CAST(currRangep, Const)) {
                if (isWildcard) {
                    rangeCondp = buildWildcardCondition(binp, exprClonep, constp);
                } else {
                    rangeCondp = new AstEq{binp->fileline(), exprClonep, constp->cloneTree(false)};
                }
            }

            if (rangeCondp) {
                fullCondp
                    = fullCondp ? new AstOr{binp->fileline(), fullCondp, rangeCondp} : rangeCondp;
            }
        }

        return fullCondp;
    }

    // Build a wildcard condition: (expr & mask) == (value & mask)
    // where mask has 1s for defined bits and 0s for wildcard bits
    AstNodeExpr* buildWildcardCondition(AstCoverBin* binp, AstNodeExpr* exprp, AstConst* constp) {
        FileLine* fl = binp->fileline();

        // Extract mask from constant (bits that are not X/Z)
        V3Number mask{constp, constp->width()};
        V3Number value{constp, constp->width()};

        for (int bit = 0; bit < constp->width(); ++bit) {
            // If bit is X or Z (don't care), set mask bit to 0
            // Otherwise set to 1 and keep the value
            if (constp->num().bitIs0(bit) || constp->num().bitIs1(bit)) {
                mask.setBit(bit, 1);
                value.setBit(bit, constp->num().bitIs1(bit) ? 1 : 0);
            } else {
                mask.setBit(bit, 0);
                value.setBit(bit, 0);
            }
        }

        // Generate: (expr & mask) == (value & mask)
        AstConst* maskConstp = new AstConst{fl, mask};
        AstConst* valueConstp = new AstConst{fl, value};

        AstNodeExpr* exprMasked = new AstAnd{fl, exprp, maskConstp};
        AstNodeExpr* valueMasked = new AstAnd{fl, valueConstp, maskConstp->cloneTree(false)};

        return new AstEq{fl, exprMasked, valueMasked};
    }

    void generateCoverageComputationCode() {
        UINFO(4, "  Generating coverage computation code" << endl);

        // Invalidate cache: addMembersp() calls in generateCoverpointCode/generateCrossCode
        // have added new members since the last scan, so clear before re-querying.
        m_memberMap.clear();

        // Find get_coverage() and get_inst_coverage() methods
        AstFunc* const getCoveragep
            = VN_CAST(m_memberMap.findMember(m_covergroupp, "get_coverage"), Func);
        AstFunc* const getInstCoveragep
            = VN_CAST(m_memberMap.findMember(m_covergroupp, "get_inst_coverage"), Func);

        if (!getCoveragep || !getInstCoveragep) {
            UINFO(4, "    Warning: Could not find get_coverage methods" << endl);
            return;
        }

        // Even if there are no bins, we still need to generate the coverage methods
        // Empty covergroups should return 100% coverage
        if (m_binInfos.empty()) {
            UINFO(4, "    No bins found, will generate method to return 100%" << endl);
        } else {
            UINFO(6, "    Found " << m_binInfos.size() << " bins for coverage" << endl);
        }

        // Generate code for get_inst_coverage()
        if (getInstCoveragep) { generateCoverageMethodBody(getInstCoveragep); }

        // Generate code for get_coverage() (type-level)
        // NOTE: Full type-level coverage requires instance tracking infrastructure
        // For now, return 0.0 as a placeholder
        if (getCoveragep) {
            AstVar* returnVarp = VN_AS(getCoveragep->fvarp(), Var);
            if (returnVarp) {
                // TODO: Implement proper type-level coverage aggregation
                // This requires tracking all instances and averaging their coverage
                // For now, return 0.0
                getCoveragep->addStmtsp(new AstAssign{
                    getCoveragep->fileline(),
                    new AstVarRef{getCoveragep->fileline(), returnVarp, VAccess::WRITE},
                    new AstConst{getCoveragep->fileline(), AstConst::RealDouble{}, 0.0}});
                UINFO(4, "    Added placeholder get_coverage() (returns 0.0)" << endl);
            }
        }
    }

    void generateCoverageMethodBody(AstFunc* funcp) {
        FileLine* fl = funcp->fileline();

        // Count total bins (excluding ignore_bins and illegal_bins)
        int totalBins = 0;
        for (const BinInfo& bi : m_binInfos) {
            UINFO(6, "      Bin: " << bi.binp->name() << " type=" << (int)bi.binp->binsType()
                                   << " IGNORE=" << (int)VCoverBinsType::BINS_IGNORE
                                   << " ILLEGAL=" << (int)VCoverBinsType::BINS_ILLEGAL << endl);
            if (bi.binp->binsType() != VCoverBinsType::BINS_IGNORE
                && bi.binp->binsType() != VCoverBinsType::BINS_ILLEGAL) {
                totalBins++;
            }
        }

        UINFO(4, "    Total regular bins: " << totalBins << " of " << m_binInfos.size() << endl);

        if (totalBins == 0) {
            // No coverage to compute - return 100%
            UINFO(4, "    Empty covergroup, returning 100.0" << endl);
            AstVar* returnVarp = VN_AS(funcp->fvarp(), Var);

            // Find and replace existing assignment to return variable
            AstAssign* existingReturnAssign = nullptr;
            for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstAssign* assignp = VN_CAST(stmtp, Assign)) {
                    if (AstVarRef* lhsVarRef = VN_CAST(assignp->lhsp(), VarRef)) {
                        if (lhsVarRef->varp() == returnVarp) {
                            existingReturnAssign = assignp;
                            break;
                        }
                    }
                }
            }

            if (existingReturnAssign) {
                // Replace the RHS of existing assignment from 0 to 100.0
                AstNode* oldRhs = existingReturnAssign->rhsp();
                if (oldRhs) VL_DO_DANGLING(oldRhs->unlinkFrBack()->deleteTree(), oldRhs);
                existingReturnAssign->rhsp(new AstConst{fl, AstConst::RealDouble{}, 100.0});
                UINFO(4, "    Replaced return value assignment to 100.0" << endl);
            } else if (returnVarp) {
                // No existing assignment found, add one
                AstAssign* assignp
                    = new AstAssign{fl, new AstVarRef{fl, returnVarp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::RealDouble{}, 100.0}};
                funcp->addStmtsp(assignp);
                UINFO(4, "    Added assignment to return 100.0" << endl);
            }
            return;
        }

        // Create local variable to count covered bins
        AstVar* coveredCountp
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
        AstVar* returnVarp = VN_AS(funcp->fvarp(), Var);
        if (!returnVarp) {
            UINFO(4, "    Warning: No return variable found in " << funcp->name() << endl);
            return;
        }

        // Calculate coverage: (covered_count / total_bins) * 100.0
        // return_var = (double)covered_count / (double)total_bins * 100.0

        // Cast covered_count to real/double
        AstNodeExpr* coveredReal
            = new AstIToRD{fl, new AstVarRef{fl, coveredCountp, VAccess::READ}};

        // Create total bins as a double constant
        AstNodeExpr* totalReal
            = new AstConst{fl, AstConst::RealDouble{}, static_cast<double>(totalBins)};

        // Divide using AstDivD (double division that emits native /)
        AstNodeExpr* divExpr = new AstDivD{fl, coveredReal, totalReal};

        // Multiply by 100 using AstMulD (double multiplication that emits native *)
        AstNodeExpr* hundredConst = new AstConst{fl, AstConst::RealDouble{}, 100.0};
        AstNodeExpr* coverageExpr = new AstMulD{fl, hundredConst, divExpr};

        // Assign to return variable
        funcp->addStmtsp(
            new AstAssign{fl, new AstVarRef{fl, returnVarp, VAccess::WRITE}, coverageExpr});

        UINFO(6, "    Added coverage computation to " << funcp->name() << " with " << totalBins
                                                      << " bins (excluding ignore/illegal)"
                                                      << endl);
    }

    int countBins(AstCoverpoint* nodep) {
        int count = 0;
        for (AstNode* binp = nodep->binsp(); binp; binp = binp->nextp()) { count++; }
        return count;
    }

    void generateCoverageRegistration() {
        // Generate VL_COVER_INSERT calls for each bin in the covergroup
        // This registers the bins with the coverage database so they can be reported

        UINFO(4, "  Generating coverage database registration for " << m_binInfos.size() << " bins"
                                                                    << endl);

        if (m_binInfos.empty()) return;

        // We need to add the registration code to the constructor
        // The registration should happen after member variables are initialized
        if (!m_constructorp) {
            m_covergroupp->v3warn(
                E_UNSUPPORTED,
                "Cannot generate coverage registration without constructor");  // LCOV_EXCL_LINE
            return;
        }

        // For each bin, generate a VL_COVER_INSERT call
        // The calls use CCall nodes to invoke VL_COVER_INSERT macro
        for (const BinInfo& binInfo : m_binInfos) {
            AstVar* varp = binInfo.varp;
            AstCoverBin* binp = binInfo.binp;
            AstCoverpoint* coverpointp = binInfo.coverpointp;
            AstCoverCross* crossp = binInfo.crossp;

            // Skip illegal and ignore bins - they don't count towards coverage
            if (binp->binsType() == VCoverBinsType::BINS_IGNORE
                || binp->binsType() == VCoverBinsType::BINS_ILLEGAL) {
                continue;
            }

            FileLine* fl = binp->fileline();

            // Build hierarchical name: covergroup.coverpoint.bin or covergroup.cross.bin
            std::string hierName = m_covergroupp->name();
            std::string binName = binp->name();

            if (coverpointp) {
                // Coverpoint bin: use coverpoint name or generate from expression
                std::string cpName = coverpointp->name();
                if (cpName.empty()) {
                    // Generate name from expression
                    if (coverpointp->exprp()) {
                        cpName = coverpointp->exprp()->name();
                        if (cpName.empty()) cpName = "cp";
                    } else {
                        cpName = "cp";
                    }
                }
                hierName += "." + cpName;
            } else if (crossp) {
                // Cross bin: use cross name
                std::string crossName = crossp->name();
                if (crossName.empty()) crossName = "cross";
                hierName += "." + crossName;
            }
            hierName += "." + binName;

            // Generate: VL_COVER_INSERT(contextp, hier, &binVar, "page", "v_funccov/...", ...)

            UINFO(6, "    Registering bin: " << hierName << " -> " << varp->name() << endl);

            // Build the coverage insert as a C statement
            // The variable reference needs to be &this->varname, where varname gets mangled to
            // __PVT__varname Use "page" field with v_funccov prefix so type is extracted correctly
            // (consistent with code coverage)
            std::string pageName = "v_funccov/" + m_covergroupp->name();
            std::string insertCall = "VL_COVER_INSERT(vlSymsp->_vm_contextp__->coveragep(), ";
            insertCall += "\"" + hierName + "\", ";
            insertCall += "&(this->__PVT__" + varp->name() + "), ";
            insertCall += "\"page\", \"" + pageName + "\", ";
            insertCall += "\"filename\", \"" + fl->filename() + "\", ";
            insertCall += "\"lineno\", \"" + std::to_string(fl->lineno()) + "\", ";
            insertCall += "\"column\", \"" + std::to_string(fl->firstColumn()) + "\", ";
            insertCall += "\"bin\", \"" + binName + "\");";

            // Create a statement node with the coverage insert call
            AstCStmt* cstmtp = new AstCStmt{fl, insertCall};

            // Add to constructor
            m_constructorp->addStmtsp(cstmtp);

            UINFO(6, "      Added VL_COVER_INSERT call to constructor" << endl);
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        UINFO(9, "Visiting class: " << nodep->name() << " isCovergroup=" << nodep->isCovergroup()
                                    << endl);
        if (nodep->isCovergroup()) {
            VL_RESTORER(m_covergroupp);
            m_covergroupp = nodep;
            m_sampleFuncp = nullptr;
            m_constructorp = nullptr;
            m_coverpoints.clear();
            m_coverCrosses.clear();

            // Extract and store the clocking event from AstCovergroup node
            // The parser creates this node to preserve the event information
            bool hasUnsupportedEvent = false;
            for (AstNode* itemp = nodep->membersp(); itemp;) {
                AstNode* nextp = itemp->nextp();
                if (AstCovergroup* const cgp = VN_CAST(itemp, Covergroup)) {
                    // Store the event in the global map for V3Active to retrieve later
                    if (cgp->eventp()) {
                        // Check if the clocking event references a member variable (unsupported)
                        // Clocking events should be on signals/nets, not class members
                        bool eventUnsupported = false;
                        for (AstNode* senp = cgp->eventp()->sensesp(); senp;
                             senp = senp->nextp()) {
                            if (AstSenItem* const senItemp = VN_CAST(senp, SenItem)) {
                                if (AstVarRef* const varrefp
                                    = VN_CAST(senItemp->sensp(), VarRef)) {
                                    if (varrefp->varp() && varrefp->varp()->isClassMember()) {
                                        cgp->v3warn(COVERIGN, "Ignoring unsupported: covergroup "
                                                              "clocking event on member variable");
                                        eventUnsupported = true;
                                        hasUnsupportedEvent = true;
                                        break;
                                    }
                                }
                            }
                        }

                        if (!eventUnsupported) {
                            // Leave cgp in the class membersp so the SenTree stays
                            // linked in the AST. V3Active will find it via membersp,
                            // use the event, then delete the AstCovergroup itself.
                            UINFO(4, "Keeping covergroup event node for V3Active: "
                                         << nodep->name() << endl);
                            itemp = nextp;
                            continue;
                        }
                    }
                    // Remove the AstCovergroup node - either unsupported event or no event
                    cgp->unlinkFrBack();
                    VL_DO_DANGLING(cgp->deleteTree(), cgp);
                }
                itemp = nextp;
            }

            // If covergroup has unsupported clocking event, skip processing it
            if (hasUnsupportedEvent) return;

            // Find the sample() method and constructor
            m_sampleFuncp = VN_CAST(m_memberMap.findMember(nodep, "sample"), Func);
            m_constructorp = VN_CAST(m_memberMap.findMember(nodep, "new"), Func);
            UINFO(9, "Found sample() method: " << (m_sampleFuncp ? "yes" : "no") << endl);
            UINFO(9, "Found constructor: " << (m_constructorp ? "yes" : "no") << endl);

            iterateChildren(nodep);
            processCovergroup();
        } else {
            iterateChildren(nodep);
        }
    }

    void visit(AstCoverpoint* nodep) override {
        UINFO(9, "Found coverpoint: " << nodep->name() << endl);
        m_coverpoints.push_back(nodep);
        iterateChildren(nodep);
    }

    void visit(AstCoverCross* nodep) override {
        UINFO(9, "Found cross: " << nodep->name() << endl);
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
    UINFO(4, __FUNCTION__ << ": " << endl);
    { FunctionalCoverageVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coveragefunc", 0, dumpTreeEitherLevel() >= 3);
}
