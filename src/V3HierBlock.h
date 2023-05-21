// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Plan for Hierarchical Verilation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
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
#include "V3ThreadSafety.h"

#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

class AstNetlist;
class AstNodeModule;
class AstVar;

//######################################################################

class V3HierBlock final {
public:
    using GParams = std::vector<AstVar*>;
    using HierBlockSet = std::unordered_set<V3HierBlock*>;

private:
    // TYPES
    // Parameter name, stringified value
    using StrGParams = std::vector<std::pair<std::string, std::string>>;

    // MEMBERS
    const AstNodeModule* const m_modp;  // Hierarchical block module
    // Hierarchical blocks that directly or indirectly instantiate this block
    HierBlockSet m_parents;
    // Hierarchical blocks that this block directly or indirectly instantiates
    HierBlockSet m_children;
    // Parameters that are overridden by #(.param(value)) syntax.
    const GParams m_gparams;

    // METHODS
    VL_UNCOPYABLE(V3HierBlock);
    static StrGParams stringifyParams(const GParams& gparams, bool forGOption) VL_MT_DISABLED;

public:
    V3HierBlock(const AstNodeModule* modp, const GParams& gparams)
        : m_modp{modp}
        , m_gparams{gparams} {}
    ~V3HierBlock() VL_MT_DISABLED;

    void addParent(V3HierBlock* parentp) { m_parents.insert(parentp); }
    void addChild(V3HierBlock* childp) { m_children.insert(childp); }
    bool hasChild() const { return !m_children.empty(); }
    const HierBlockSet& parents() const { return m_parents; }
    const HierBlockSet& children() const { return m_children; }
    const GParams& gparams() const { return m_gparams; }
    const AstNodeModule* modp() const { return m_modp; }

    // For emitting Makefile and CMakeLists.txt
    V3StringList commandArgs(bool forCMake) const VL_MT_DISABLED;
    V3StringList hierBlockArgs() const VL_MT_DISABLED;
    string hierPrefix() const VL_MT_DISABLED;
    string hierSomeFile(bool withDir, const char* prefix, const char* suffix) const VL_MT_DISABLED;
    string hierWrapper(bool withDir) const VL_MT_DISABLED;
    string hierMk(bool withDir) const VL_MT_DISABLED;
    string hierLib(bool withDir) const VL_MT_DISABLED;
    string hierGenerated(bool withDir) const VL_MT_DISABLED;
    // Returns the original HDL file if it is not included in v3Global.opt.vFiles().
    string vFileIfNecessary() const VL_MT_DISABLED;
    // Write command line arguments to .f file for this hierarchical block
    void writeCommandArgsFile(bool forCMake) const VL_MT_DISABLED;
    string commandArgsFileName(bool forCMake) const VL_MT_DISABLED;
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

    void add(const AstNodeModule* modp, const std::vector<AstVar*>& gparams) VL_MT_DISABLED;
    void registerUsage(const AstNodeModule* parentp, const AstNodeModule* childp) VL_MT_DISABLED;

    const_iterator begin() const { return m_blocks.begin(); }
    const_iterator end() const { return m_blocks.end(); }
    bool empty() const { return m_blocks.empty(); }

    // Returns all hierarchical blocks that sorted in leaf-first order.
    // Latter block refers only already appeared hierarchical blocks.
    HierVector hierBlocksSorted() const VL_MT_DISABLED;

    // Write command line arguments to .f files for child Verilation run
    void writeCommandArgsFiles(bool forCMake) const VL_MT_DISABLED;
    static string topCommandArgsFileName(bool forCMake) VL_MT_DISABLED;

    static void createPlan(AstNetlist* nodep) VL_MT_DISABLED;
};

#endif  // guard
