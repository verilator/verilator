// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Symbol table
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3SYMTABLE_H_
#define VERILATOR_V3SYMTABLE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3String.h"

#include <cstdarg>
#include <iomanip>
#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

class VSymGraph;
class VSymEnt;

//######################################################################
// Symbol table

using VSymConstMap = std::unordered_set<const VSymEnt*>;

class VSymEnt final {
    // Symbol table that can have a "superior" table for resolving upper references
    // MEMBERS
    using IdNameMap = std::multimap<std::string, VSymEnt*>;
    IdNameMap m_idNameMap;  // Hash of variables by name
    AstNode* m_nodep;  // Node that entry belongs to
    VSymEnt* m_fallbackp;  // Table "above" this one in name scope, for fallback resolution
    VSymEnt* m_parentp;  // Table that created this table, dot notation needed to resolve into it
    AstNodeModule* m_classOrPackagep;  // Package node is in (for V3LinkDot, unused here)
    string m_symPrefix;  // String to prefix symbols with (for V3LinkDot, unused here)
    bool m_exported;  // Allow importing
    bool m_imported;  // Was imported
#ifdef VL_DEBUG
    static int debug() {
        static int level = -1;
        if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel("V3LinkDot.cpp");
        return level;
    }
#else
    static constexpr int debug() { return 0; }  // NOT runtime, too hot of a function
#endif
public:
    using const_iterator = IdNameMap::const_iterator;
    const_iterator begin() const { return m_idNameMap.begin(); }
    const_iterator end() const { return m_idNameMap.end(); }

    void dumpIterate(std::ostream& os, VSymConstMap& doneSymsr, const string& indent,
                     int numLevels, const string& searchName) const {
        os << indent << "+ " << std::left << std::setw(30)
           << (searchName == "" ? "\"\"" : searchName) << std::setw(0) << std::right;
        os << "  se" << cvtToHex(this) << std::setw(0);
        os << "  fallb=se" << cvtToHex(m_fallbackp);
        if (m_symPrefix != "") os << "  symPrefix=" << m_symPrefix;
        os << "  n=" << nodep();
        os << '\n';
        if (VL_UNCOVERABLE(doneSymsr.find(this) != doneSymsr.end())) {
            os << indent << "| ^ duplicate, so no children printed\n";  // LCOV_EXCL_LINE
        } else {
            doneSymsr.insert(this);
            for (IdNameMap::const_iterator it = m_idNameMap.begin(); it != m_idNameMap.end();
                 ++it) {
                if (numLevels >= 1) {
                    it->second->dumpIterate(os, doneSymsr, indent + "| ", numLevels - 1,
                                            it->first);
                }
            }
        }
    }
    void dump(std::ostream& os, const string& indent = "", int numLevels = 1) const {
        VSymConstMap doneSyms;
        dumpIterate(os, doneSyms, indent, numLevels, "TOP");
    }

    // METHODS
    VSymEnt(VSymGraph* graphp, const VSymEnt* symp);  // Below
    VSymEnt(VSymGraph* graphp, AstNode* nodep);  // Below
    ~VSymEnt() {
        // Change links so we coredump if used
#ifdef VL_DEBUG
        m_nodep = reinterpret_cast<AstNode*>(1);
        m_fallbackp = reinterpret_cast<VSymEnt*>(1);
        m_parentp = reinterpret_cast<VSymEnt*>(1);
        m_classOrPackagep = reinterpret_cast<AstNodeModule*>(1);
#endif
    }
#if defined(VL_DEBUG) && !defined(VL_LEAK_CHECKS)
    // For testing, leak so above destructor 1 assignments work
    void operator delete(void* objp, size_t size) {}
#endif
    void fallbackp(VSymEnt* entp) { m_fallbackp = entp; }
    VSymEnt* fallbackp() const { return m_fallbackp; }
    void parentp(VSymEnt* entp) { m_parentp = entp; }
    VSymEnt* parentp() const { return m_parentp; }
    void classOrPackagep(AstNodeModule* entp) { m_classOrPackagep = entp; }
    AstNodeModule* classOrPackagep() const { return m_classOrPackagep; }
    AstNode* nodep() const { return m_nodep; }
    string symPrefix() const { return m_symPrefix; }
    void symPrefix(const string& name) { m_symPrefix = name; }
    bool exported() const { return m_exported; }
    void exported(bool flag) { m_exported = flag; }
    bool imported() const { return m_imported; }
    void imported(bool flag) { m_imported = flag; }
    void insert(const string& name, VSymEnt* entp) {
        UINFO(9, "     SymInsert se" << cvtToHex(this) << " '" << name << "' se" << cvtToHex(entp)
                                     << "  " << entp->nodep() << endl);
        if (name != "" && m_idNameMap.find(name) != m_idNameMap.end()) {
            if (!V3Error::errorCount()) {  // Else may have just reported warning
                if (debug() >= 9 || V3Error::debugDefault()) dump(cout, "- err-dump: ", 1);
                entp->nodep()->v3fatalSrc("Inserting two symbols with same name: " << name);
            }
        } else {
            m_idNameMap.emplace(name, entp);
        }
    }
    void reinsert(const string& name, VSymEnt* entp) {
        const auto it = m_idNameMap.find(name);
        if (name != "" && it != m_idNameMap.end()) {
            UINFO(9, "     SymReinsert se" << cvtToHex(this) << " '" << name << "' se"
                                           << cvtToHex(entp) << "  " << entp->nodep() << endl);
            it->second = entp;  // Replace
        } else {
            insert(name, entp);
        }
    }
    VSymEnt* findIdFlat(const string& name) const {
        // Find identifier without looking upward through symbol hierarchy
        // First, scan this begin/end block or module for the name
        const auto it = m_idNameMap.find(name);
        UINFO(9, "     SymFind   se"
                     << cvtToHex(this) << " '" << name << "' -> "
                     << (it == m_idNameMap.end()
                             ? "NONE"
                             : "se" + cvtToHex(it->second) + " n=" + cvtToHex(it->second->nodep()))
                     << endl);
        if (it != m_idNameMap.end()) return (it->second);
        return nullptr;
    }
    VSymEnt* findIdFallback(const string& name) const {
        // Find identifier looking upward through symbol hierarchy
        // First, scan this begin/end block or module for the name
        if (VSymEnt* const entp = findIdFlat(name)) return entp;
        // Then scan the upper begin/end block or module for the name
        if (m_fallbackp) return m_fallbackp->findIdFallback(name);
        return nullptr;
    }
    void candidateIdFlat(VSpellCheck* spellerp, const VNodeMatcher* matcherp) const {
        // Suggest alternative symbol candidates without looking upward through symbol hierarchy
        for (IdNameMap::const_iterator it = m_idNameMap.begin(); it != m_idNameMap.end(); ++it) {
            const AstNode* const itemp = it->second->nodep();
            if (itemp && (!matcherp || matcherp->nodeMatch(itemp))) {
                spellerp->pushCandidate(itemp->prettyName());
            }
        }
    }
    void candidateIdFallback(VSpellCheck* spellerp, const VNodeMatcher* matcherp) const {
        // Suggest alternative symbol candidates with looking upward through symbol hierarchy
        // Note VSpellCheck wants the most important (closest) items pushed first
        candidateIdFlat(spellerp, matcherp);
        // Then suggest the upper begin/end block or module
        if (m_fallbackp) m_fallbackp->candidateIdFallback(spellerp, matcherp);
    }

private:
    void importOneSymbol(VSymGraph* graphp, const string& name, const VSymEnt* srcp,
                         bool honorExport) {
        if ((!honorExport || srcp->exported())
            && !findIdFlat(name)) {  // Don't insert over existing entry
            VSymEnt* const symp = new VSymEnt(graphp, srcp);
            symp->exported(false);  // Can't reimport an import without an export
            symp->imported(true);
            reinsert(name, symp);
        }
    }
    void exportOneSymbol(VSymGraph* graphp, const string& name, const VSymEnt* srcp) const {
        if (srcp->exported()) {
            if (VSymEnt* const symp = findIdFlat(name)) {  // Should already exist in current table
                if (!symp->exported()) symp->exported(true);
            }
        }
    }

public:
    void importFromClass(VSymGraph* graphp, const VSymEnt* srcp) {
        // Import tokens from source symbol table into this symbol table
        // Used for classes in early parsing only to handle "extends"
        for (IdNameMap::const_iterator it = srcp->m_idNameMap.begin();
             it != srcp->m_idNameMap.end(); ++it) {
            importOneSymbol(graphp, it->first, it->second, false);
        }
    }
    void importFromPackage(VSymGraph* graphp, const VSymEnt* srcp, const string& id_or_star) {
        // Import tokens from source symbol table into this symbol table
        if (id_or_star != "*") {
            const auto it = srcp->m_idNameMap.find(id_or_star);
            if (it != srcp->m_idNameMap.end()) {
                importOneSymbol(graphp, it->first, it->second, true);
            }
        } else {
            for (IdNameMap::const_iterator it = srcp->m_idNameMap.begin();
                 it != srcp->m_idNameMap.end(); ++it) {
                importOneSymbol(graphp, it->first, it->second, true);
            }
        }
    }
    void exportFromPackage(VSymGraph* graphp, const VSymEnt* srcp, const string& id_or_star) {
        // Export tokens from source symbol table into this symbol table
        if (id_or_star != "*") {
            const auto it = vlstd::as_const(srcp->m_idNameMap).find(id_or_star);
            if (it != srcp->m_idNameMap.end()) exportOneSymbol(graphp, it->first, it->second);
        } else {
            for (IdNameMap::const_iterator it = srcp->m_idNameMap.begin();
                 it != srcp->m_idNameMap.end(); ++it) {
                exportOneSymbol(graphp, it->first, it->second);
            }
        }
    }
    void exportStarStar(VSymGraph* graphp) {
        // Export *:*: Export all tokens from imported packages
        for (IdNameMap::const_iterator it = m_idNameMap.begin(); it != m_idNameMap.end(); ++it) {
            VSymEnt* const symp = it->second;
            if (!symp->exported()) symp->exported(true);
        }
    }
    void importFromIface(VSymGraph* graphp, const VSymEnt* srcp, bool onlyUnmodportable = false) {
        // Import interface tokens from source symbol table into this symbol table, recursively
        UINFO(9, "     importIf  se" << cvtToHex(this) << " from se" << cvtToHex(srcp) << endl);
        for (IdNameMap::const_iterator it = srcp->m_idNameMap.begin();
             it != srcp->m_idNameMap.end(); ++it) {
            const string& name = it->first;
            VSymEnt* const subSrcp = it->second;
            const AstVar* const varp = VN_CAST(subSrcp->nodep(), Var);
            if (!onlyUnmodportable || (varp && varp->isParam())) {
                VSymEnt* const subSymp = new VSymEnt(graphp, subSrcp);
                reinsert(name, subSymp);
                // And recurse to create children
                subSymp->importFromIface(graphp, subSrcp);
            }
        }
    }
    void cellErrorScopes(AstNode* lookp, string prettyName = "") {
        if (prettyName == "") prettyName = lookp->prettyName();
        string scopes;
        for (IdNameMap::iterator it = m_idNameMap.begin(); it != m_idNameMap.end(); ++it) {
            AstNode* const itemp = it->second->nodep();
            if (VN_IS(itemp, Cell) || (VN_IS(itemp, Module) && VN_AS(itemp, Module)->isTop())) {
                if (scopes != "") scopes += ", ";
                scopes += AstNode::prettyName(it->first);
            }
        }
        if (scopes == "") scopes = "<no instances found>";
        std::cerr << V3Error::warnMore() << "... Known scopes under '" << prettyName
                  << "': " << scopes << endl;
        if (debug()) dump(std::cerr, "       KnownScope: ", 1);
    }
};

//######################################################################
// Symbol tables

class VSymGraph final {
    // Collection of symbol tables
    // TYPES
    using SymStack = std::vector<VSymEnt*>;

    // MEMBERS
    VSymEnt* m_symRootp;  // Root symbol table
    SymStack m_symsp;  // All symbol tables, to cleanup

    // CONSTRUCTORS
    VL_UNCOPYABLE(VSymGraph);

public:
    explicit VSymGraph(AstNetlist* nodep) { m_symRootp = new VSymEnt(this, nodep); }
    ~VSymGraph() {
        for (const VSymEnt* entp : m_symsp) delete entp;
    }

    // METHODS
    VSymEnt* rootp() const { return m_symRootp; }
    // Debug
    void dump(std::ostream& os, const string& indent = "") {
        VSymConstMap doneSyms;
        os << "SymEnt Dump:\n";
        m_symRootp->dumpIterate(os, doneSyms, indent, 9999, "$root");
        bool first = true;
        for (SymStack::iterator it = m_symsp.begin(); it != m_symsp.end(); ++it) {
            if (doneSyms.find(*it) == doneSyms.end()) {
                if (first) {
                    first = false;
                    os << "%%Warning: SymEnt Orphans:\n";
                }
                (*it)->dumpIterate(os, doneSyms, indent, 9999, "Orphan");
            }
        }
    }
    void dumpFilePrefixed(const string& nameComment) {
        if (v3Global.opt.dumpTree()) {
            const string filename = v3Global.debugFilename(nameComment) + ".txt";
            UINFO(2, "Dumping " << filename << endl);
            const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
            if (logp->fail()) v3fatal("Can't write " << filename);
            dump(*logp, "");
        }
    }

protected:
    friend class VSymEnt;
    void pushNewEnt(VSymEnt* entp) { m_symsp.push_back(entp); }
};

//######################################################################

inline VSymEnt::VSymEnt(VSymGraph* graphp, AstNode* nodep)
    : m_nodep(nodep) {
    // No argument to set fallbackp, as generally it's wrong to set it in the new call,
    // Instead it needs to be set on a "findOrNew()" return, as it may have been new'ed
    // by an earlier search insertion.
    m_fallbackp = nullptr;
    m_parentp = nullptr;
    m_classOrPackagep = nullptr;
    m_exported = true;
    m_imported = false;
    graphp->pushNewEnt(this);
}

inline VSymEnt::VSymEnt(VSymGraph* graphp, const VSymEnt* symp)
    : m_nodep(symp->m_nodep) {
    m_fallbackp = symp->m_fallbackp;
    m_parentp = symp->m_parentp;
    m_classOrPackagep = symp->m_classOrPackagep;
    m_exported = symp->m_exported;
    m_imported = symp->m_imported;
    graphp->pushNewEnt(this);
}

#endif  // guard
