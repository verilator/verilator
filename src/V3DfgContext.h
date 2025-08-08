// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Persistent context for DFG algorithms
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

//////////////////////////////////////////////////////////////////////////////
// Base class for all context objects
//////////////////////////////////////////////////////////////////////////////

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

//////////////////////////////////////////////////////////////////////////////
// Contexts for various algorithms - keep sorted
//////////////////////////////////////////////////////////////////////////////

class V3DfgAstToDfgContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    VDouble0 m_coalescedAssignments;  // Number of partial assignments coalesced
    VDouble0 m_inputEquations;  // Number of input combinational equations
    VDouble0 m_representable;  // Number of combinational equations representable
    VDouble0 m_nonRepDType;  // Equations non-representable due to data type
    VDouble0 m_nonRepImpure;  // Equations non-representable due to impure node
    VDouble0 m_nonRepTiming;  // Equations non-representable due to timing control
    VDouble0 m_nonRepLhs;  // Equations non-representable due to lhs
    VDouble0 m_nonRepNode;  // Equations non-representable due to node type
    VDouble0 m_nonRepUnknown;  // Equations non-representable due to unknown node
    VDouble0 m_nonRepVarRef;  // Equations non-representable due to variable reference
    VDouble0 m_nonRepWidth;  // Equations non-representable due to width mismatch

private:
    V3DfgAstToDfgContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "AstToDfg"} {}
    ~V3DfgAstToDfgContext() {
        addStat("coalesced assignments", m_coalescedAssignments);
        addStat("input equations", m_inputEquations);
        addStat("representable", m_representable);
        addStat("non-representable (dtype)", m_nonRepDType);
        addStat("non-representable (impure)", m_nonRepImpure);
        addStat("non-representable (timing)", m_nonRepTiming);
        addStat("non-representable (lhs)", m_nonRepLhs);
        addStat("non-representable (node)", m_nonRepNode);
        addStat("non-representable (unknown)", m_nonRepUnknown);
        addStat("non-representable (var ref)", m_nonRepVarRef);
        addStat("non-representable (width)", m_nonRepWidth);

        // Check the stats are consistent
        UASSERT(m_representable  //
                        + m_nonRepDType  //
                        + m_nonRepImpure  //
                        + m_nonRepTiming  //
                        + m_nonRepLhs  //
                        + m_nonRepNode  //
                        + m_nonRepUnknown  //
                        + m_nonRepVarRef  //
                        + m_nonRepWidth  //
                    == m_inputEquations,
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
    VDouble0 m_resultEquations;  // Number of result combinational equations

private:
    V3DfgDfgToAstContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "DfgToAst"} {}
    ~V3DfgDfgToAstContext() { addStat("result equations", m_resultEquations); }
};
class V3DfgEliminateVarsContext final : public V3DfgSubContext {
    // Only V3DfgContext can create an instance
    friend class V3DfgContext;

public:
    // STATE
    std::vector<AstNode*> m_deleteps;  // AstVar/AstVarScope that can be deleted at the end
    VDouble0 m_varsReplaced;  // Number of variables replaced
    VDouble0 m_varsRemoved;  // Number of variables removed

private:
    V3DfgEliminateVarsContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "EliminateVars"} {}
    ~V3DfgEliminateVarsContext() {
        for (AstNode* const nodep : m_deleteps) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
        addStat("variables replaced", m_varsReplaced);
        addStat("variables removed", m_varsRemoved);
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
    VDouble0 m_temporariesIntroduced;  // Number of temporaries introduced

private:
    V3DfgRegularizeContext(V3DfgContext& ctx, const std::string& label)
        : V3DfgSubContext{ctx, label, "Regularize"} {}
    ~V3DfgRegularizeContext() { addStat("temporaries introduced", m_temporariesIntroduced); }
};

//////////////////////////////////////////////////////////////////////////////
// Top level V3DfgContext
//////////////////////////////////////////////////////////////////////////////

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
    V3DfgEliminateVarsContext m_eliminateVarsContext{*this, m_label};
    V3DfgPeepholeContext m_peepholeContext{*this, m_label};
    V3DfgRegularizeContext m_regularizeContext{*this, m_label};

    // Node pattern collector
    V3DfgPatternStats m_patternStats;

    // CONSTRUCTOR
    explicit V3DfgContext(const std::string& label)
        : m_label{label}
        , m_prefix{VString::removeWhitespace(label) + "-"} {}

    ~V3DfgContext() {
        const string prefix = "Optimizations, DFG " + label() + " General, ";
        V3Stats::addStat(prefix + "modules", m_modules);

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
