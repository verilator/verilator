// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Persistent context for DFG algorithms
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
//
// Various context objects hold data that need to persist across invocations
// of a DFG algorithms.
//
//*************************************************************************

#ifndef VERILATOR_V3DFGCONTEXT_H_
#define VERILATOR_V3DFGCONTEXT_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3DfgPatternStats.h"
#include "V3DfgPeepholePatterns.h"
#include "V3File.h"
#include "V3Stats.h"
#include "V3String.h"

class V3DfgContext;

//######################################################################
// Base class for all context objects

class V3DfgSubContext VL_NOT_FINAL {
    V3DfgContext& m_ctx;  // The whole context
    const std::string m_label;  // Label to add to stats, etc.
    const std::string m_name;  // Pass/algorithm name, to be used in statistics

protected:
    VL_DEFINE_DEBUG_FUNCTIONS;

    V3DfgSubContext(V3DfgContext& ctx, const std::string& label, const char* name)
        : m_ctx{ctx}
        , m_label{label}
        , m_name{name} {}

    void addStat(const std::string& what, double value) {
        V3Stats::addStat("Optimizations, DFG " + m_label + " " + m_name + ", " + what, value);
    }

public:
    inline const std::string& prefix() const;
    const std::string& label() const { return m_label; }
};

//######################################################################
// Contexts for various algorithms - keep sorted

class V3DfgAstToDfgContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_inputs;  // Number of input processes (logic constructs)
    VDouble0 m_representable;  // Number of combinational equations representable
    VDouble0 m_nonRepCfg;  // Non-representable due to failing to build CFG
    VDouble0 m_nonRepLive;  // Non-representable due to failing liveness analysis
    VDouble0 m_nonRepVar;  // Non-representable due to unsupported variable properties

private:
    V3DfgAstToDfgContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "AstToDfg"} {}
    ~V3DfgAstToDfgContext() {
        addStat("input processes", m_inputs);
        addStat("representable", m_representable);
        addStat("non-representable (cfg)", m_nonRepCfg);
        addStat("non-representable (live)", m_nonRepLive);
        addStat("non-representable (var)", m_nonRepVar);
        // Check the stats are consistent
        UASSERT(m_representable + m_nonRepCfg + m_nonRepLive + m_nonRepVar == m_inputs,
                "Inconsistent statistics");
    }
};
class V3DfgBinToOneHotContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_decodersCreated;  // Number of bianry to one-hot decoders created

private:
    V3DfgBinToOneHotContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "BinToOneHot"} {}
    ~V3DfgBinToOneHotContext() { addStat("decoders created", m_decodersCreated); }
};
class V3DfgBreakCyclesContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_nFixed;  // Number of graphs that became acyclic
    VDouble0 m_nImproved;  // Number of graphs that were imporoved but still cyclic
    VDouble0 m_nUnchanged;  // Number of graphs that were left unchanged
    VDouble0 m_nTrivial;  // Number of graphs that were not changed
    VDouble0 m_nImprovements;  // Number of changes made to graphs

private:
    V3DfgBreakCyclesContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "BreakCycles"} {}
    ~V3DfgBreakCyclesContext() {
        addStat("made acyclic", m_nFixed);
        addStat("improved", m_nImproved);
        addStat("left unchanged", m_nUnchanged);
        addStat("trivial", m_nTrivial);
        addStat("changes applied", m_nImprovements);
    }
};
class V3DfgCseContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_eliminated;  // Number of common sub-expressions eliminated

private:
    V3DfgCseContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "CSE"} {}
    ~V3DfgCseContext() { addStat("expressions eliminated", m_eliminated); }
};

class V3DfgDfgToAstContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_outputVariables;  // Number of output variables
    VDouble0 m_outputVariablesWithDefault;  // Number of outptu variables with a default driver
    VDouble0 m_resultEquations;  // Number of result combinational equations

private:
    V3DfgDfgToAstContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "DfgToAst"} {}
    ~V3DfgDfgToAstContext() {
        addStat("output variables", m_outputVariables);
        addStat("output variables with default driver", m_outputVariablesWithDefault);
        addStat("result equations", m_resultEquations);
    }
};
class V3DfgPeepholeContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    // Enable flags for each optimization
    std::array<bool, VDfgPeepholePattern::_ENUM_END> m_enabled;
    // Count of applications for each optimization (for statistics)
    std::array<VDouble0, VDfgPeepholePattern::_ENUM_END> m_count;

private:
    V3DfgPeepholeContext(V3DfgContext& ctx, const std::string& label) VL_MT_DISABLED;
    ~V3DfgPeepholeContext() VL_MT_DISABLED;
};
class V3DfgRegularizeContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_temporariesOmitted;  // Number of temporaries omitted as cheaper to re-compute
    VDouble0 m_temporariesIntroduced;  // Number of temporaries introduced

    std::vector<AstNode*> m_deleteps;  // AstVar/AstVarScope that can be deleted at the end
    VDouble0 m_usedVarsReplaced;  // Number of used variables replaced with equivalent ones
    VDouble0 m_usedVarsInlined;  // Number of used variables inlined
    VDouble0 m_unusedRemoved;  // Number of unused vertices remoevd

private:
    V3DfgRegularizeContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "Regularize"} {}
    ~V3DfgRegularizeContext() {
        for (AstNode* const nodep : m_deleteps) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        addStat("used variables replaced", m_usedVarsReplaced);
        addStat("used variables inlined", m_usedVarsInlined);
        addStat("unused vertices removed", m_unusedRemoved);

        addStat("temporaries omitted", m_temporariesOmitted);
        addStat("temporaries introduced", m_temporariesIntroduced);
    }
};
class V3DfgSynthesisContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE

    // Stats for conversion
    struct {
        // Inputs
        VDouble0 inputAssignments;  // Number of input assignments
        VDouble0 inputExpressions;  // Number of input equations
        // Successful
        VDouble0 representable;  // Number of representable constructs
        // Unsuccessful
        VDouble0 nonRepImpure;  // Non representable: impure
        VDouble0 nonRepDType;  // Non representable: unsupported data type
        VDouble0 nonRepLValue;  // Non representable: unsupported LValue form
        VDouble0 nonRepVarRef;  // Non representable: unsupported var reference
        VDouble0 nonRepOOBSel;  // Non representable: out of bounds select
        VDouble0 nonRepNode;  // Non representable: unsupported AstNode type
        VDouble0 nonRepUnknown;  // Non representable: unhandled AstNode type
    } m_conv;

    // Stats for synthesis
    struct {
        // Inputs
        VDouble0 inputAlways;  // Number of always blocks attempted
        VDouble0 inputAssign;  // Number of continuous assignments attempted
        // Successful
        VDouble0 synthAlways;  // Number of always blocks successfully synthesized
        VDouble0 synthAssign;  // Number of continuous assignments successfully synthesized
        // Unsuccessful
        VDouble0 nonSynConv;  // Non synthesizable: non representable (above)
        VDouble0 nonSynExtWrite;  // Non synthesizable: has externally written variable
        VDouble0 nonSynLoop;  // Non synthesizable: loop in CFG
        VDouble0 nonSynStmt;  // Non synthesizable: unsupported statement
        VDouble0 nonSynMultidrive;  // Non synthesizable: multidriven value within statement
        VDouble0 nonSynArray;  // Non synthesizable: array type unhandled
        VDouble0 nonSynLatch;  // Non synthesizable: maybe latch
        VDouble0 nonSynJoinInput;  // Non synthesizable: needing to join input variable
        VDouble0 nonSynFalseWrite;  // Non synthesizable: does not write output
        // Reverted
        VDouble0 revertNonSyn;  // Reverted due to being driven from non-synthesizable vertex
        VDouble0 revertMultidrive;  // Reverted due to multiple drivers
        // Additional stats
        VDouble0 cfgTrivial;  // Trivial input CFGs
        VDouble0 cfgSp;  // Series-paralel input CFGs
        VDouble0 cfgDag;  // Generic loop free input CFGs
        VDouble0 cfgCyclic;  // Cyclic input CFGs
        VDouble0 joinUsingPathPredicate;  // Num control flow joins using full path predicate
        VDouble0 joinUsingBranchCondition;  // Num Control flow joins using dominating branch cond
    } m_synt;

private:
    V3DfgSynthesisContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "Synthesis"} {}
    ~V3DfgSynthesisContext() {
        // Conversion statistics
        addStat("conv / input assignments", m_conv.inputAssignments);
        addStat("conv / input expressions", m_conv.inputExpressions);
        addStat("conv / representable inputs", m_conv.representable);
        addStat("conv / non-representable (impure)", m_conv.nonRepImpure);
        addStat("conv / non-representable (dtype)", m_conv.nonRepDType);
        addStat("conv / non-representable (lhs)", m_conv.nonRepLValue);
        addStat("conv / non-representable (varref)", m_conv.nonRepVarRef);
        addStat("conv / non-representable (oobsel)", m_conv.nonRepOOBSel);
        addStat("conv / non-representable (node)", m_conv.nonRepNode);
        addStat("conv / non-representable (unknown)", m_conv.nonRepUnknown);
        VDouble0 nConvNonRep;
        nConvNonRep += m_conv.nonRepImpure;
        nConvNonRep += m_conv.nonRepDType;
        nConvNonRep += m_conv.nonRepLValue;
        nConvNonRep += m_conv.nonRepVarRef;
        nConvNonRep += m_conv.nonRepOOBSel;
        nConvNonRep += m_conv.nonRepNode;
        nConvNonRep += m_conv.nonRepUnknown;
        VDouble0 nConvExpect;
        nConvExpect += m_conv.inputAssignments;
        nConvExpect += m_conv.inputExpressions;
        nConvExpect -= m_conv.representable;
        UASSERT(nConvNonRep == nConvExpect, "Inconsistent statistics / conv");

        // Synthesis statistics
        addStat("synt / always blocks considered", m_synt.inputAlways);
        addStat("synt / always blocks synthesized", m_synt.synthAlways);
        addStat("synt / continuous assignments considered", m_synt.inputAssign);
        addStat("synt / continuous assignments synthesized", m_synt.synthAssign);
        addStat("synt / non-synthesizable (conv)", m_synt.nonSynConv);
        addStat("synt / non-synthesizable (ext write)", m_synt.nonSynExtWrite);
        addStat("synt / non-synthesizable (loop)", m_synt.nonSynLoop);
        addStat("synt / non-synthesizable (stmt)", m_synt.nonSynStmt);
        addStat("synt / non-synthesizable (multidrive)", m_synt.nonSynMultidrive);
        addStat("synt / non-synthesizable (array)", m_synt.nonSynArray);
        addStat("synt / non-synthesizable (latch)", m_synt.nonSynLatch);
        addStat("synt / non-synthesizable (join input)", m_synt.nonSynJoinInput);
        addStat("synt / non-synthesizable (false write)", m_synt.nonSynFalseWrite);
        addStat("synt / reverted (non-synthesizable)", m_synt.revertNonSyn);
        addStat("synt / reverted (multidrive)", m_synt.revertMultidrive);

        VDouble0 nSyntNonSyn;
        nSyntNonSyn += m_synt.nonSynConv;
        nSyntNonSyn += m_synt.nonSynExtWrite;
        nSyntNonSyn += m_synt.nonSynLoop;
        nSyntNonSyn += m_synt.nonSynStmt;
        nSyntNonSyn += m_synt.nonSynMultidrive;
        nSyntNonSyn += m_synt.nonSynArray;
        nSyntNonSyn += m_synt.nonSynLatch;
        nSyntNonSyn += m_synt.nonSynJoinInput;
        nSyntNonSyn += m_synt.nonSynFalseWrite;
        VDouble0 nSyntExpect;
        nSyntExpect += m_synt.inputAlways;
        nSyntExpect += m_synt.inputAssign;
        nSyntExpect -= m_synt.synthAlways;
        nSyntExpect -= m_synt.synthAssign;
        UASSERT(nSyntNonSyn == nSyntExpect, "Inconsistent statistics / synt");

        addStat("synt / input CFG trivial", m_synt.cfgTrivial);
        addStat("synt / input CFG sp", m_synt.cfgSp);
        addStat("synt / input CFG dag", m_synt.cfgDag);
        addStat("synt / input CFG cyclic", m_synt.cfgCyclic);

        addStat("synt / joins using path predicate", m_synt.joinUsingPathPredicate);
        addStat("synt / joins using branch condition", m_synt.joinUsingBranchCondition);
    }
};

//######################################################################
// Top level V3DfgContext

class V3DfgContext final {
    const std::string m_label;  // Label to add to stats, etc.
    const std::string m_prefix;  // Prefix to add to file dumps (derived from label)

public:
    // STATE

    // Global statistics
    VDouble0 m_modules;  // Number of modules optimized

    // Sub contexts - keep sorted by type
    V3DfgAstToDfgContext m_ast2DfgContext{*this, m_label};
    V3DfgBinToOneHotContext m_binToOneHotContext{*this, m_label};
    V3DfgBreakCyclesContext m_breakCyclesContext{*this, m_label};
    V3DfgCseContext m_cseContext0{*this, m_label + " 1st"};
    V3DfgCseContext m_cseContext1{*this, m_label + " 2nd"};
    V3DfgDfgToAstContext m_dfg2AstContext{*this, m_label};
    V3DfgPeepholeContext m_peepholeContext{*this, m_label};
    V3DfgRegularizeContext m_regularizeContext{*this, m_label};
    V3DfgSynthesisContext m_synthContext{*this, m_label};

    // Node pattern collector
    V3DfgPatternStats m_patternStats;

    // CONSTRUCTOR
    explicit V3DfgContext(const std::string& label)
        : m_label{label}
        , m_prefix{VString::removeWhitespace(label) + "-"} {}

    ~V3DfgContext() {
        const string front = "Optimizations, DFG " + label() + " General, ";
        V3Stats::addStat(front + "modules", m_modules);

        // Print the collected patterns
        if (v3Global.opt.stats()) {
            // Label to lowercase, without spaces
            std::string ident = label();
            std::transform(ident.begin(), ident.end(), ident.begin(), [](unsigned char c) {  //
                return c == ' ' ? '_' : std::tolower(c);
            });

            // File to dump to
            const std::string filename = v3Global.opt.hierTopDataDir() + "/"
                                         + v3Global.opt.prefix() + "__stats_dfg_patterns__" + ident
                                         + ".txt";
            // Open, write, close
            const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
            if (ofp->fail()) v3fatal("Can't write file: " << filename);
            m_patternStats.dump(label(), *ofp);
        }
    }

    // ACCESSORS
    const std::string& label() const { return m_label; }
    const std::string& prefix() const { return m_prefix; }
};

const std::string& V3DfgSubContext::prefix() const { return m_ctx.prefix(); }

#endif  //VERILATOR_V3DFGCONTEXT_H_
