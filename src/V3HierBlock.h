// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Plan for Hierarchical Verilation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3HIERBLOCK_H_
#define _V3HIERBLOCK_H_ 1

#include "verilatedos.h"

#include <map>
#include <set>
#include <string>
#include <vector>

class AstNodeModule;
class AstNetlist;
class AstVar;

//######################################################################

class V3HierBlock {
public:
    typedef std::vector<AstVar*> GParams;
    typedef std::set<V3HierBlock*> HierBlockSet;
    typedef std::set<const AstNodeModule*> NodeModuleSet;

private:
    // Hierarchy block module
    const AstNodeModule* m_modp;
    // Hierarchy blocks that directly or indirectly instantiate this block
    HierBlockSet m_parents;
    // Hierarchy blocks that this block directly or indirectly instantiates
    HierBlockSet m_children;
    // Parameters that are overridden by #(.param(value)) syntax.
    GParams m_gparams;

    VL_UNCOPYABLE(V3HierBlock);

public:
    V3HierBlock(const AstNodeModule* modp, const GParams& gparams)
        : m_modp(modp)
        , m_gparams(gparams) {}
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
    V3StringList commandOptions(bool forCMake) const;
    V3StringList hierBlockOptions() const;
    string hierPrefix() const;
    string hierSomeFile(bool withDir, const char* prefix, const char* suffix) const;
    string hierWrapper(bool withDir) const;
    string hierMk(bool withDir) const;
    string hierLib(bool withDir) const;
    string hierGenerated(bool withDir) const;
    // Write command line opriont to .f file for this hierarchy block
    void writeCommandFile(bool forCMake) const;
    string commandFileName(bool forCMake) const;
};

//######################################################################

// Holds relashonship between AstNodeModule and V3HierBlock
class V3HierBlockPlan {
    class Visitor;
    typedef std::map<const AstNodeModule*, V3HierBlock*> HierMap;
    HierMap m_blocks;

    V3HierBlockPlan();
    VL_UNCOPYABLE(V3HierBlockPlan);

public:
    typedef HierMap::iterator iterator;
    typedef HierMap::const_iterator const_iterator;
    typedef std::vector<const V3HierBlock*> HierVector;
    VL_DEBUG_FUNC;  // Declare debug()

    bool isHierBlock(const AstNodeModule* modp) const;
    void add(const AstNodeModule* modp, const std::vector<AstVar*>& gparams);
    void registerUsage(const AstNodeModule* parentp, const AstNodeModule* childp);

    const_iterator begin() const { return m_blocks.begin(); }
    const_iterator end() const { return m_blocks.end(); }
    bool empty() const { return m_blocks.empty(); }

    // Returns all hierarchy blocks that sorted in leaf-first order.
    // Latter block refers only already appeared hierarchy blocks.
    HierVector hierBlocksSorted() const;

    // Write command line opriont to .f files for child Verilation run
    void writeCommandFiles(bool forCMake) const;
    string topCommandFileName(bool forCMake) const;

    static void createPlan(AstNetlist* nodep);
};

#endif  // guard
