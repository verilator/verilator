// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: FSM coverage graph representation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// FSM COVERAGE GRAPH:
//      Provides a V3Graph-based representation for one detected FSM. The
//      graph owns the state/transition topology plus the per-FSM metadata
//      needed to lower that topology into concrete coverage instrumentation
//      immediately after detection.
//
//*************************************************************************

#ifndef VERILATOR_V3FSMGRAPH_H_
#define VERILATOR_V3FSMGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"

#include <unordered_map>
#include <vector>

class AstScope;
class AstVarScope;
class FileLine;
class FsmArcEdge;
class FsmPseudoVertex;
class FsmStateVertex;

// Captures one sensitivity-list entry so a graph-backed build phase can later
// recreate an active block with the same triggering event control.
class FsmSenDesc final {
public:
    // MEMBERS
    uint8_t edgeType = 0;
    string varScopeName;
    string varName;
};

// Captures the simple reset predicate shape that survives to this pass after
// earlier normalization so reset arcs can be reconstructed during lowering.
class FsmResetCondDesc final {
public:
    // MEMBERS
    string varScopeName;
    string varName;
};

class FsmVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(FsmVertex, V3GraphVertex)

public:
    enum class Kind : uint8_t { STATE, RESET_ANY, DEFAULT_ANY };

private:
    Kind m_kind;
    string m_label;
    int m_value = 0;

protected:
    // CONSTRUCTORS
    FsmVertex(V3Graph* graphp, Kind kind, string label, int value) VL_MT_DISABLED
        : V3GraphVertex{graphp}
        , m_kind{kind}
        , m_label{label}
        , m_value{value} {}
    ~FsmVertex() override = default;

public:
    // ACCESSORS
    // Distinguish ordinary states from the synthetic sources used to model
    // reset-entry and default-fallthrough transitions in the same graph.
    Kind kind() const { return m_kind; }
    bool isState() const { return m_kind == Kind::STATE; }
    bool isResetAny() const { return m_kind == Kind::RESET_ANY; }
    bool isDefaultAny() const { return m_kind == Kind::DEFAULT_ANY; }
    // Preserve both the human-readable label and the numeric state value so
    // dumps are understandable and lowering can still rebuild typed compares.
    const string& label() const { return m_label; }
    int value() const { return m_value; }

    string name() const override VL_MT_SAFE { return m_label + "=" + cvtToStr(m_value); }
};

// One graph per detected FSM. Graph-level metadata captures the non-graph
// context needed to lower states/arcs back into the AST after detection.
class FsmGraph final : public V3Graph {
    string m_scopeName;
    string m_stateVarName;
    string m_stateVarInternalName;
    string m_stateVarScopeName;
    std::vector<FsmSenDesc> m_senses;
    FsmResetCondDesc m_resetCond;
    bool m_hasResetCond = false;
    bool m_resetInclude = false;
    bool m_inclCond = false;
    FileLine* m_flp = nullptr;
    std::unordered_map<int, FsmStateVertex*> m_stateVertices;
    FsmPseudoVertex* m_resetVertexp = nullptr;
    FsmPseudoVertex* m_defaultVertexp = nullptr;

public:
    // ACCESSORS
    // Graph-level metadata identifies where this FSM came from and what extra
    // policy is needed when lowering it back into coverage instrumentation.
    const string& scopeName() const { return m_scopeName; }
    void scopeName(const string& name) { m_scopeName = name; }
    const string& stateVarName() const { return m_stateVarName; }
    void stateVarName(const string& name) { m_stateVarName = name; }
    const string& stateVarInternalName() const { return m_stateVarInternalName; }
    void stateVarInternalName(const string& name) { m_stateVarInternalName = name; }
    const string& stateVarScopeName() const { return m_stateVarScopeName; }
    void stateVarScopeName(const string& name) { m_stateVarScopeName = name; }
    const std::vector<FsmSenDesc>& senses() const { return m_senses; }
    std::vector<FsmSenDesc>& senses() { return m_senses; }
    const FsmResetCondDesc& resetCond() const { return m_resetCond; }
    FsmResetCondDesc& resetCond() { return m_resetCond; }
    bool hasResetCond() const { return m_hasResetCond; }
    void hasResetCond(bool flag) { m_hasResetCond = flag; }
    bool resetInclude() const { return m_resetInclude; }
    void resetInclude(bool flag) { m_resetInclude = flag; }
    bool inclCond() const { return m_inclCond; }
    void inclCond(bool flag) { m_inclCond = flag; }
    FileLine* fileline() const { return m_flp; }
    void fileline(FileLine* flp) { m_flp = flp; }
    // Detection interns state vertices by encoded value so both extraction and
    // lowering can treat the graph as the canonical FSM representation.
    FsmStateVertex* findStateVertex(int value) const;
    FsmStateVertex* addStateVertex(string label, int value) VL_MT_DISABLED;
    // Synthetic vertices keep reset/default arcs inside the graph model rather
    // than forcing special transitions back into side tables.
    FsmPseudoVertex* resetAnyVertex() VL_MT_DISABLED;
    FsmPseudoVertex* defaultAnyVertex() VL_MT_DISABLED;
    // Add one transition edge to the graph, choosing the appropriate source
    // vertex kind for ordinary, reset, or default arcs.
    FsmArcEdge* addArc(int fromValue, int toValue, bool isReset, bool isCond, bool isDefault,
                       FileLine* flp) VL_MT_DISABLED;

    // Debug visibility is the main immediate benefit of adopting V3Graph, so
    // make the graph name identify the FSM in a reviewer-friendly way.
    string name() const VL_MT_SAFE {
        return "FSM " + (m_stateVarName.empty() ? m_stateVarScopeName : m_stateVarName);
    }
};

// One vertex per FSM state. Keeping label and numeric value together makes the
// graph directly useful for debug dumps and later lowering.
class FsmStateVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmStateVertex, FsmVertex)
public:
    // CONSTRUCTORS
    FsmStateVertex(FsmGraph* graphp, string label, int value) VL_MT_DISABLED
        : FsmVertex{graphp, Kind::STATE, label, value} {}
    ~FsmStateVertex() override = default;

    // Debug visibility is one of the reasons to move to V3Graph, so keep the
    // vertex name concise and reviewer-readable.
    string dotColor() const override { return "lightblue"; }
    string dotShape() const override { return "ellipse"; }
};

// Synthetic vertices represent transition sources that are not ordinary FSM
// states, such as reset entry arcs and default-fallthrough arcs.
class FsmPseudoVertex final : public FsmVertex {
    VL_RTTI_IMPL(FsmPseudoVertex, FsmVertex)

public:
    // CONSTRUCTORS
    FsmPseudoVertex(FsmGraph* graphp, Kind kind, string label) VL_MT_DISABLED
        : FsmVertex{graphp, kind, label, 0} {}
    ~FsmPseudoVertex() override = default;

    // Pseudo vertices are markers rather than numeric states, so omit the
    // synthetic "=0" suffix and show only the reviewer-facing label.
    string name() const override VL_MT_SAFE { return label(); }
    string dotColor() const override { return isResetAny() ? "darkgreen" : "orange"; }
    string dotShape() const override { return "diamond"; }
};

// One edge per extracted transition. The flags mirror the current FSM coverage
// reporting distinctions so a later lowering step can preserve behavior.
class FsmArcEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(FsmArcEdge, V3GraphEdge)
    bool m_isReset = false;
    bool m_isCond = false;
    bool m_isDefault = false;
    FileLine* m_flp = nullptr;

public:
    // CONSTRUCTORS
    FsmArcEdge(FsmGraph* graphp, FsmVertex* fromp, FsmStateVertex* top, bool isReset,
               bool isCond, bool isDefault, FileLine* flp) VL_MT_DISABLED
        : V3GraphEdge{graphp, fromp, top, 1}
        , m_isReset{isReset}
        , m_isCond{isCond}
        , m_isDefault{isDefault}
        , m_flp{flp} {}
    ~FsmArcEdge() override = default;

    // ACCESSORS
    bool isReset() const { return m_isReset; }
    bool isCond() const { return m_isCond; }
    bool isDefault() const { return m_isDefault; }
    FileLine* fileline() const { return m_flp; }

    string dotLabel() const override {
        if (m_isReset) return "reset";
        if (m_isDefault) return "default";
        if (m_isCond) return "cond";
        return "";
    }
    string dotColor() const override {
        if (m_isReset) return "darkgreen";
        if (m_isDefault) return "orange";
        if (m_isCond) return "blue";
        return "black";
    }
};

#endif
