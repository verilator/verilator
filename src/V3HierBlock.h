// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Plan for Hierarchical Verilation
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

#ifndef VERILATOR_V3HIERBLOCK_H_
#define VERILATOR_V3HIERBLOCK_H_

#include "verilatedos.h"

#include "V3Options.h"

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

class V3HierBlockParams final {
public:
    using GParams = std::vector<AstVar*>;
    using GTypeParams = std::vector<AstParamTypeDType*>;

private:
    GParams m_params;
    GTypeParams m_typeParams;

public:
    void add(AstVar* param) { m_params.push_back(param); }
    void add(AstParamTypeDType* param) { m_typeParams.push_back(param); }

    const GParams& gparams() const { return m_params; };
    const GTypeParams& gTypeParams() const { return m_typeParams; };
    GParams& gparams() { return m_params; };
    GTypeParams& gTypeParams() { return m_typeParams; };

    void swap(V3HierBlockParams& other) {
        m_params.swap(other.m_params);
        m_typeParams.swap(other.m_typeParams);
    }
};

class V3HierBlock final {
public:
    using HierBlockSet = std::unordered_set<V3HierBlock*>;

private:
    // TYPES
    // Parameter name, stringified value
    using StrGParam = std::pair<string, string>;
    using StrGParams = std::vector<StrGParam>;

    // MEMBERS
    const AstNodeModule* const m_modp;  // Hierarchical block module
    // Hierarchical blocks that directly or indirectly instantiate this block
    HierBlockSet m_parents;
    // Hierarchical blocks that this block directly or indirectly instantiates
    HierBlockSet m_children;
    // Parameters that are overridden by #(.param(value)) syntax.
    const V3HierBlockParams m_params;

    // METHODS
    VL_UNCOPYABLE(V3HierBlock);
    static StrGParams stringifyParams(const V3HierBlockParams::GParams& params,
                                      bool forGOption) VL_MT_DISABLED;

public:
    V3HierBlock(const AstNodeModule* modp, const V3HierBlockParams& params)
        : m_modp{modp}
        , m_params{params} {}

    ~V3HierBlock() VL_MT_DISABLED;

    void addParent(V3HierBlock* parentp) { m_parents.insert(parentp); }
    bool hasParent() const { return !m_parents.empty(); }
    void addChild(V3HierBlock* childp) { m_children.insert(childp); }
    bool hasChild() const { return !m_children.empty(); }
    const HierBlockSet& parents() const { return m_parents; }
    const HierBlockSet& children() const { return m_children; }
    const V3HierBlockParams& params() const { return m_params; }
    const AstNodeModule* modp() const { return m_modp; }

    // For emitting Makefile and CMakeLists.txt
    V3StringList commandArgs(bool forCMake) const VL_MT_DISABLED;
    V3StringList hierBlockArgs() const VL_MT_DISABLED;
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
    void writeCommandArgsFile(bool forCMake) const VL_MT_DISABLED;
    void writeParametersFile() const VL_MT_DISABLED;
    string commandArgsFilename(bool forCMake) const VL_MT_DISABLED;
    string typeParametersFilename() const VL_MT_DISABLED;
};

//######################################################################

// Holds relationship between AstNodeModule and V3HierBlock
class V3HierBlockPlan final {
    using HierMap = std::unordered_map<const AstNodeModule*, V3HierBlock*>;
    HierMap m_blocks;

    V3HierBlockPlan() = default;
    VL_UNCOPYABLE(V3HierBlockPlan);

public:
    using iterator = HierMap::iterator;
    using const_iterator = HierMap::const_iterator;
    using HierVector = std::vector<const V3HierBlock*>;

    void add(const AstNodeModule* modp, const V3HierBlockParams& params) VL_MT_DISABLED;
    void registerUsage(const AstNodeModule* parentp, const AstNodeModule* childp) VL_MT_DISABLED;

    const_iterator begin() const { return m_blocks.begin(); }
    const_iterator end() const { return m_blocks.end(); }
    bool empty() const { return m_blocks.empty(); }

    // Returns all hierarchical blocks that sorted in leaf-first order.
    // Latter block refers only already appeared hierarchical blocks.
    HierVector hierBlocksSorted() const VL_MT_DISABLED;

    // Write command line arguments to .f files for child Verilation run
    void writeCommandArgsFiles(bool forCMake) const VL_MT_DISABLED;
    void writeParametersFiles() const VL_MT_DISABLED;
    static string topCommandArgsFilename(bool forCMake) VL_MT_DISABLED;

    static void createPlan(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // guard
