// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hierarchical verilation for large designs
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// Hierarchical Verilation is useful for large designs.
// It reduces
//   - time and memory for Verilation
//   - compilation time especially when a hierarchy block is used many times
//
// Hierarchical Verilation internally creates protect-lib for each hierarchy block.
// Upper modules read wrapper for the protect-lib instead of the actual design.
//
// Hierarchical Verilation runs as the following step
// 1) Find modules marked by /*verilator hier_block*/ metacomment
// 2) Generate ${prefix}_hier.mk to create protected-lib for hierarchy blocks and
//    final Verilation to process the top module, that refers wrappers
// 3) Call child Verilator process via ${prefix}_hier.mk
//
// There are 3 kinds of Verilator run.
// a) To create ${prefix}_hier.mk
// b) To create protect-lib for each hierarchy block
// c) To load wrappers and Verilate the top module
//
// Then user can build Verilated module as usual.
//
// Here is more detailed internal process.
// 1) Parser adds AstPragmaType::HIER_BLOCK of AstPragma to modules
//    that are marked with /*verilator hier_block*/ metacomment in Verilator run a).
// 2) AstModule with HIER_BLOCK pragma is marked modp->hier_block(true)
//    in V3LinkResolve.cpp during run a).
// 3) In V3LinkCells.cpp, the following things are done during run b) and c).
//    3-1) Delete the upper modules of the hierarchy block because the top module in run b) is
//         hierarchy block, not the top module of run c).
//    3-2) If the top module of the run b) or c) instantiates other hierarchy blocks that is
//         parameterized,
//         module and task names are renamed to the original name to be compatible with the
//         hier module to be called.
//
//         Parameterized modules have unique name by V3Param.cpp. The unique name contains '__' and
//         Verilator encodes '__' when loading such symbols.
// 4) V3LinkDot.cpp checks dotted access across hierarchy block boundary.
// 5) In V3Dead.cpp, some parameters of parameterized modules are protected not to be deleted even
//    if the parameter is not referred. This protection is necessary to match step 6) below.
// 6) In V3Param.cpp, use protect-lib wrapper of parameterized module in b) and c).
//    If a hierarchy block is a parameterized module and instantiated in multiple locations,
//    all parameters must exactly match.
// 7) In V3HierBlock.cpp, relationship among hierarchy blocks are checked in run a).
//    (which block uses other blocks..)
// 8) In V3EmitMk.cpp, ${prefix}_hier.mk is created in run a).
//
// There are two hidden command options.
//   --hierarchical-mode is added to Verilator run b).
//   --hierarchy-block module_name,mangled_name,name0,value0,name1,value1,...
//       module_name  :The original modulename
//       mangled_name :Mangled name of parameterized modules (named in V3Param.cpp).
//                     Same as module_name for non-parameterized hierarchy block.
//       name         :The name of the parameter
//       value        :Overridden value of the parameter
//
//       Used for b) and c).
//       This options is repeated for all instantiating hierarchy blocks.

#include <memory>
#include <sstream>
#include <utility>
#include <vector>

#include "V3Ast.h"
#include "V3Error.h"
#include "V3HierBlock.h"
#include "V3Stats.h"

typedef std::vector<std::pair<string, string> > StrGParams;

static string escapeIntegerForShell(const string& str) {
    string result;
    result.reserve(str.size() + 1);
    for (size_t i = 0; i < str.size(); ++i) {
        if (str[i] == '\'') result.push_back('\\');
        result.push_back(str[i]);
    }
    return result;
}

static string escapeStringForShell(const string& str) {
    string result;
    const char squoate = '\'';
    const char dquoate = '"';
    result.reserve(str.size() + 2);
    // String literal for -G option must be surrounded by double quote (")
    result.push_back(squoate);
    result.push_back(dquoate);
    result.push_back(squoate);

    result.push_back(squoate);
    for (size_t i = 0; i < str.size(); ++i) {
        if (str[i] == squoate) {
            result.push_back(squoate);  // terminate
            result.push_back(dquoate);  // "
            result.push_back(squoate);  // str[i]
            result.push_back(dquoate);  // "
            result.push_back(squoate);  // start
        } else {
            result.push_back(str[i]);
        }
    }
    result.push_back(squoate);

    result.push_back(squoate);
    result.push_back(dquoate);
    result.push_back(squoate);
    return result;
}

static string escapeEscape(const string& s) {
    string result;
    result.reserve(s.length());
    for (string::const_iterator it = s.begin(); it != s.end(); ++it) {
        if (*it == '\\') result.push_back(*it);
        result.push_back(*it);
    }
    return result;
}

static string escapeStringForCMake(const string& str) {
    int num_eq = 0;
    for (string::size_type i = 0; i < str.length(); ++i) {
        if (str[i] == '=') ++num_eq;
    }
    string eq;
    eq.resize(num_eq, '=');
    return '[' + eq + '[' + str + ']' + eq + ']';
}

static StrGParams stringifyParams(const V3HierBlock::GParams& gparams, bool forCMake,
                                  bool forGOption) {
    StrGParams strParams;
    for (V3HierBlock::GParams::const_iterator gparamIt = gparams.begin();
         gparamIt != gparams.end(); ++gparamIt) {
        if (AstConst* constp = VN_CAST((*gparamIt)->valuep(), Const)) {
            // Only constant parameter needs to be set to -G because already checked in
            // V3Param.cpp. See also ParamVisitor::checkSupportedParam() in the file.
            if (constp->isDouble()) {
                // 64 bit width of hex can be expressed with 16 chars.
                // 32 chars must be long enough for hexadecial floating point
                // considering prefix of '0x', '.', and 'P'.
                std::vector<char> hexFpStr(32, '\0');
                const int len = VL_SNPRINTF(hexFpStr.data(), hexFpStr.size(), "%a",
                                            constp->num().toDouble());
                UASSERT_OBJ(0 < len && static_cast<size_t>(len) < hexFpStr.size(), constp,
                            " is not properly converted to string");
                strParams.push_back(std::make_pair((*gparamIt)->name(), hexFpStr.data()));
            } else if (constp->isString()) {
                string s = constp->num().toString();
                if (!forGOption) { s = escapeEscape(s); }
                s = forCMake ? ('"' + s + '"') : escapeStringForShell(s);
                strParams.push_back(std::make_pair((*gparamIt)->name(), s));
            } else {  // Either signed or unsigned integer.
                string s = constp->num().ascii(true, true);
                if (!forCMake) s = escapeIntegerForShell(s);
                strParams.push_back(std::make_pair((*gparamIt)->name(), s));
            }
        }
    }
    return strParams;
}

//######################################################################
//
V3HierBlock::~V3HierBlock() {
    UASSERT(m_children.empty(), "at least one module must be a leaf");
    for (HierBlockSet::const_iterator child = m_children.begin(); child != m_children.end();
         ++child) {
        const bool deleted = (*child)->m_children.erase(this);
        UASSERT_OBJ(deleted, m_modp, " is not registered");
    }
}

V3StringList V3HierBlock::commandOptions(bool forCMake) const {
    V3StringList opts;
    const string prefix = "V" + modp()->name();
    opts.push_back(" --prefix " + prefix);
    opts.push_back(" --mod-prefix " + prefix);
    opts.push_back(" --top-module " + modp()->name());
    opts.push_back(" --protect-lib " + modp()->name());  // mangled name
    opts.push_back(" --protect-key " + v3Global.opt.protectKeyDefaulted());
    opts.push_back(" --hierarchical-mode");

    const StrGParams gparamsStr = stringifyParams(gparams(), forCMake, true);
    for (StrGParams::const_iterator paramIt = gparamsStr.begin(); paramIt != gparamsStr.end();
         ++paramIt) {
        opts.push_back("-G" + paramIt->first + "=" + paramIt->second + "");
        if (forCMake) opts.back() = escapeStringForCMake(opts.back());
    }
    return opts;
}

V3StringList V3HierBlock::hierBlockOptions(bool forCMake) const {
    V3StringList opts;
    const StrGParams gparamsStr = stringifyParams(gparams(), forCMake, false);
    opts.push_back("--hierarchy-block ");
    string s = modp()->origName();  // origName
    s += "," + modp()->name();  // mangledName
    for (StrGParams::const_iterator paramIt = gparamsStr.begin(); paramIt != gparamsStr.end();
         ++paramIt) {
        s += "," + paramIt->first;
        s += "," + paramIt->second;
    }
    if (forCMake) s = escapeStringForCMake(s);
    opts.back() += s;
    return opts;
}

string V3HierBlock::hierPrefix() const { return "V" + modp()->name(); }

string V3HierBlock::hierSomeFile(bool withDir, const char* prefix, const char* suffix) const {
    string s;
    if (withDir) s = hierPrefix() + '/';
    s += prefix + modp()->name() + suffix;
    return s;
}

string V3HierBlock::hierWrapper(bool withDir) const { return hierSomeFile(withDir, "", ".sv"); }

string V3HierBlock::hierMk(bool withDir) const { return hierSomeFile(withDir, "V", ".mk"); }

string V3HierBlock::hierLib(bool withDir) const { return hierSomeFile(withDir, "lib", ".a"); }

string V3HierBlock::hierGenerated(bool withDir) const {
    return hierWrapper(withDir) + ' ' + hierMk(withDir);
}

//######################################################################
class V3HierBlockPlan::Visitor : public AstNVisitor {
    typedef std::set<const AstModule*> ModuleSet;
    V3HierBlockPlan* const m_planp;
    AstModule* m_modp;
    ModuleSet m_referred;  // Modules that have hier_block pragma
    ModuleSet m_checked;  // Modules that are already checked;
    V3HierBlock::GParams m_gparams;  // list of variables that is AstVarType::GPARAM

    virtual void visit(AstNode* nodep) VL_OVERRIDE { iterateChildren(nodep); }
    virtual void visit(AstModule* nodep) VL_OVERRIDE {
        // Don't visit twice
        if (m_checked.find(nodep) != m_checked.end()) return;
        UINFO(5, "Checking " << nodep->prettyNameQ() << " from "
                             << (m_modp ? m_modp->prettyNameQ() : string("null")) << std::endl);
        AstModule* const prevModulep = m_modp;
        ModuleSet prevReferred;
        V3HierBlock::GParams prevGParams;
        if (nodep->hierBlock()) {
            m_modp = nodep;
            prevReferred.swap(m_referred);
        }
        prevGParams.swap(m_gparams);

        iterateChildren(nodep);

        if (nodep->hierBlock()) {
            m_planp->add(nodep, m_gparams);
            for (ModuleSet::const_iterator it = m_referred.begin(); it != m_referred.end(); ++it) {
                m_planp->registerUsage(nodep, *it);
            }
            m_modp = prevModulep;
            m_referred.swap(prevReferred);
        }
        m_gparams.swap(prevGParams);
        m_checked.insert(nodep);
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        // Visit used module here to know that the module is hier_block or not.
        // This visitor behaves almost depth first search
        if (AstModule* modp = VN_CAST(nodep->modp(), Module)) {
            iterate(modp);
            m_referred.insert(modp);
        }
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (nodep->isGParam() && nodep->overriddenParam()) m_gparams.push_back(nodep);
    }

public:
    Visitor(V3HierBlockPlan* planp, AstNetlist* netlist)
        : m_planp(planp)
        , m_modp(NULL) {

        iterateChildren(netlist);
    }
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################

V3HierBlockPlan::V3HierBlockPlan() {}

bool V3HierBlockPlan::isHierBlock(const AstNodeModule* modp) const {
    return m_blocks.find(modp) != m_blocks.end();
}

void V3HierBlockPlan::add(const AstNodeModule* modp, const std::vector<AstVar*>& gparams) {
    iterator it = m_blocks.find(modp);
    if (it == m_blocks.end()) {
        V3HierBlock* hblockp = new V3HierBlock(modp, gparams);
        UINFO(3, "Add " << modp->prettyNameQ() << " with " << gparams.size() << " parameters"
                        << std::endl);
        m_blocks.insert(std::make_pair(modp, hblockp));
    }
}

void V3HierBlockPlan::registerUsage(const AstNodeModule* parentp, const AstNodeModule* childp) {
    iterator parent = m_blocks.find(parentp);
    UASSERT_OBJ(parent != m_blocks.end(), parentp, "must be added");
    iterator child = m_blocks.find(childp);
    if (child != m_blocks.end()) {
        UINFO(3, "Found usage relation " << parentp->prettyNameQ() << " uses "
                                         << childp->prettyNameQ() << std::endl);
        parent->second->addChild(child->second);
        child->second->addParent(parent->second);
    }
}

void V3HierBlockPlan::createPlan(AstNetlist* nodep) {
    // When processing a hierarchy block, no need to create a plan anymore.
    if (v3Global.opt.hierMode()) return;

    AstNodeModule* modp = nodep->topModulep();
    if (modp->hierBlock()) {
        modp->v3warn(HIERBLOCK, "Top module illegally marked hierarchy block, ignoring marking\n"
        + V3Error::warnMore() + "... Suggest remove verilator hier_block on this module");
        modp->hierBlock(false);
    }

    vl_unique_ptr<V3HierBlockPlan> planp(new V3HierBlockPlan());
    { Visitor visitor(planp.get(), nodep); }
    V3Stats::addStat("HierBlock, Hierarchy block", v3Global.opt.hierBlocks().size());

    // No hierarchy block is found, nothing to do.
    if (planp->empty()) return;

    v3Global.hierPlanp(planp.release());
}

V3HierBlockPlan::HierVector V3HierBlockPlan::hierBlocksSorted() const {
    typedef std::map<const V3HierBlock*, std::set<const V3HierBlock*> > ChildrenMap;
    ChildrenMap childrenOfHierBlock;

    HierVector sorted;
    for (const_iterator it = begin(); it != end(); ++it) {
        if (!it->second->hasChild()) {  // No children, already leaf
            sorted.push_back(it->second);
        } else {
            ChildrenMap::value_type::second_type& childrenSet
                = childrenOfHierBlock[it->second];  // insert
            const V3HierBlock::HierBlockSet& c = it->second->children();
            childrenSet.insert(c.begin(), c.end());
        }
    }

    // Use index instead of iterator because new elements will be added in this loop
    for (size_t i = 0; i < sorted.size(); ++i) {
        // This hblockp is already leaf.
        const V3HierBlock* hblockp = sorted[i];
        const V3HierBlock::HierBlockSet& p = hblockp->parents();
        for (V3HierBlock::HierBlockSet::const_iterator it = p.begin(); it != p.end(); ++it) {
            // Delete hblockp from parrents. If a parent does not have a child anymore, then it is
            // a leaf too.
            const ChildrenMap::iterator parentIt = childrenOfHierBlock.find(*it);
            UASSERT_OBJ(parentIt != childrenOfHierBlock.end(), (*it)->modp(), "must be included");
            const V3HierBlock::HierBlockSet::size_type erased = parentIt->second.erase(hblockp);
            UASSERT_OBJ(erased == 1, hblockp->modp(),
                        " must be a child of " << parentIt->first->modp());
            if (parentIt->second.empty()) {  // Now parentIt is leaf
                sorted.push_back(parentIt->first);
                childrenOfHierBlock.erase(parentIt);
            }
        }
    }
    return sorted;
}
