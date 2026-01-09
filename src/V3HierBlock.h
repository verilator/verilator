// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Plan for Hierarchical Verilation
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

#ifndef VERILATOR_V3HIERBLOCK_H_
#define VERILATOR_V3HIERBLOCK_H_

#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Graph.h"

#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

class AstNetlist;
class AstNodeModule;
class AstParamTypeDType;
class AstVar;

//######################################################################

class V3HierGraph final : public V3Graph {
public:
    V3HierGraph() = default;
    ~V3HierGraph() = default;
    VL_UNCOPYABLE(V3HierGraph);
    VL_UNMOVABLE(V3HierGraph);

    // Write command line arguments to .f files for child Verilation run
    void writeCommandArgsFiles(bool forMkJson) const VL_MT_DISABLED;
    void writeParametersFiles() const VL_MT_DISABLED;
    static string topCommandArgsFilename(bool forMkJson) VL_MT_DISABLED;
};

class V3HierBlock final : public V3GraphVertex {
    VL_RTTI_IMPL(V3HierBlock, V3GraphVertex)

    // TYPES
    // Parameter name, stringified value
    using StrGParam = std::pair<string, string>;
    using StrGParams = std::vector<StrGParam>;

    // MEMBERS
    const AstModule* const m_modp;  // Hierarchical block module
    // Value parameters that are overridden by #(.param(value)) syntax.
    const std::vector<AstVar*> m_params;
    // Types parameters that are overridden by #(.param(value)) syntax.
    const std::vector<AstParamTypeDType*> m_typeParams;

    // METHODS
    static StrGParams stringifyParams(const std::vector<AstVar*>& params,
                                      bool forGOption) VL_MT_DISABLED;

public:
    // CONSTRUCTORs
    V3HierBlock(V3HierGraph* graphp, const AstModule* modp, const std::vector<AstVar*>& params,
                const std::vector<AstParamTypeDType*>& typeParams)
        : V3GraphVertex{graphp}
        , m_modp{modp}
        , m_params{params}
        , m_typeParams{typeParams} {}
    ~V3HierBlock() VL_MT_DISABLED = default;
    VL_UNCOPYABLE(V3HierBlock);
    VL_UNMOVABLE(V3HierBlock);

    const AstModule* modp() const { return m_modp; }

    // For emitting Makefile and build definition JSON
    VStringList commandArgs(bool forMkJson) const VL_MT_DISABLED;
    VStringList hierBlockArgs() const VL_MT_DISABLED;
    string hierPrefix() const VL_MT_DISABLED;
    string hierSomeFilename(bool withDir, const char* prefix,
                            const char* suffix) const VL_MT_DISABLED;
    string hierWrapperFilename(bool withDir) const VL_MT_DISABLED;
    string hierMkFilename(bool withDir) const VL_MT_DISABLED;
    string hierLibFilename(bool withDir) const VL_MT_DISABLED;
    string hierGeneratedFilenames(bool withDir) const VL_MT_DISABLED;
    // Returns the original HDL file if it is not included in v3Global.opt.vFiles().
    string vFileIfNecessary() const VL_MT_DISABLED;
    // Write command line arguments to .f file for this hierarchical block
    void writeCommandArgsFile(bool forMkJson) const VL_MT_DISABLED;
    void writeParametersFile() const VL_MT_DISABLED;
    string commandArgsFilename(bool forMkJson) const VL_MT_DISABLED;
    string typeParametersFilename() const VL_MT_DISABLED;

    // For Graphviz dumps only
    std::string name() const override { return m_modp->prettyNameQ(); }
    std::string dotShape() const override { return "box"; }
};

//######################################################################
// Pass to create hierarcical block graph

class V3Hierarchical final {
public:
    static void createGraph(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // guard
