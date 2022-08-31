// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Plan for Hierarchical Verilation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#ifndef VERILATOR_V3HIERBLOCK_H_
#define VERILATOR_V3HIERBLOCK_H_

#include "verilatedos.h"

#include "V3Global.h"

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
    static StrGParams stringifyParams(const GParams& gparams, bool forGOption);

public:
    V3HierBlock(const AstNodeModule* modp, const GParams& gparams)
        : m_modp{modp}
        , m_gparams{gparams} {}
    ~V3HierBlock();
    VL_DEBUG_FUNC;  // Declare debug()

    void addParent(V3HierBlock* parentp) { m_parents.insert(parentp); }
    void addChild(V3HierBlock* childp) { m_children.insert(childp); }
    bool hasChild() const { return !m_children.empty(); }
    const HierBlockSet& parents() const { return m_parents; }
    const HierBlockSet& children() const { return m_children; }
    const GParams& gparams() const { return m_gparams; }
    const AstNodeModule* modp() const { return m_modp; }

    // For emitting Makefile and CMakeLists.txt
    V3StringList commandArgs(bool forCMake) const;
    V3StringList hierBlockArgs() const;
    string hierPrefix() const;
    string hierSomeFile(bool withDir, const char* prefix, const char* suffix) const;
    string hierWrapper(bool withDir) const;
    string hierMk(bool withDir) const;
    string hierLib(bool withDir) const;
    string hierGenerated(bool withDir) const;
    // Returns the original HDL file if it is not included in v3Global.opt.vFiles().
    string vFileIfNecessary() const;
    // Write command line argumuents to .f file for this hierarchical block
    void writeCommandArgsFile(bool forCMake) const;
    string commandArgsFileName(bool forCMake) const;
};

//######################################################################

// Holds relashonship between AstNodeModule and V3HierBlock
class V3HierBlockPlan final {
    using HierMap = std::unordered_map<const AstNodeModule*, V3HierBlock*>;
    HierMap m_blocks;

    V3HierBlockPlan() = default;
    VL_UNCOPYABLE(V3HierBlockPlan);

public:
    using iterator = HierMap::iterator;
    using const_iterator = HierMap::const_iterator;
    using HierVector = std::vector<const V3HierBlock*>;
    VL_DEBUG_FUNC;  // Declare debug()

    void add(const AstNodeModule* modp, const std::vector<AstVar*>& gparams);
    void registerUsage(const AstNodeModule* parentp, const AstNodeModule* childp);

    const_iterator begin() const { return m_blocks.begin(); }
    const_iterator end() const { return m_blocks.end(); }
    bool empty() const { return m_blocks.empty(); }

    // Returns all hierarchical blocks that sorted in leaf-first order.
    // Latter block refers only already appeared hierarchical blocks.
    HierVector hierBlocksSorted() const;

    // Write command line arguments to .f files for child Verilation run
    void writeCommandArgsFiles(bool forCMake) const;
    static string topCommandArgsFileName(bool forCMake);

    static void createPlan(AstNetlist* nodep);
};

#endif  // guard
