// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// Visitor to build library mapping patterns from --libmap files, which may
// be overridden on command line with --work. Patterns are relative to
// libmap file location.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LibMap.h"

#include "V3Graph.h"
#include "V3Options.h"
#include "V3Os.h"
#include "V3Parse.h"
#include "V3SymTable.h"

#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class LibMapVisitor final : public VNVisitor {
    // STATE
    string m_lib;  // Library currently being mapped
    string m_rel;  // Relative path of current libmap file

    // VISITORS
    void visit(AstParseRef* nodep) override {
        if (!m_lib.empty()) {
            const string& pattern = nodep->name();
            v3Global.libMapp()->addPattern(pattern, m_lib, m_rel);
        }
    }

    void visit(AstLibrary* nodep) override {
        VL_RESTORER(m_lib);
        VL_RESTORER(m_rel);
        m_lib = nodep->name();
        m_rel = V3Os::filenameDir(nodep->fileline()->filename());
        iterateChildren(nodep);
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    LibMapVisitor(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// LibMap class functions

string V3LibMap::matchMapping(const string& filename) {
    // Check explicit mappings first
    for (const auto& mapping : m_explicitMappings) {
        const string& filepath = V3Os::filenameRelativePath(filename, mapping.base());
        if (VString::wildmatch(filepath, mapping.pattern())) { return mapping.libname(); }
    }
    // Then check wildcard mappings
    for (const auto& mapping : m_wildcardMappings) {
        const string& filepath = V3Os::filenameRelativePath(filename, mapping.base());
        if (VString::wildmatch(filepath, mapping.pattern())) { return mapping.libname(); }
    }
    // Then check directory mappings
    for (const auto& mapping : m_directoryMappings) {
        const string& filepath = V3Os::filenameRelativePath(filename, mapping.base());
        const string& dirpart = V3Os::filenameDir(filepath);
        if (VString::wildmatch(dirpart, mapping.pattern())) { return mapping.libname(); }
    }
    return "work";
}

void V3LibMap::addPattern(const string& pattern, const string& libname, const string& base) {
    UINFO(4, __FUNCTION__ << ": pattern '" << pattern << "' => library '" << libname << "'");

    bool isIncDir = pattern.back() == '/';
    const string& nondir = V3Os::filenameNonDir(pattern);
    const string& cleanPattern = V3Os::filenameCleanup(pattern);

    if (isIncDir) {
        m_directoryMappings.push_back({cleanPattern, libname, base});
    } else if (nondir.find('*') != string::npos || nondir.find('?') != string::npos) {
        m_wildcardMappings.push_back({cleanPattern, libname, base});
    } else {
        m_explicitMappings.push_back({cleanPattern, libname, base});
    }
}

void V3LibMap::map(AstNetlist* nodep) {
    UINFO(4, __FUNCTION__ << ": ");
    { LibMapVisitor{nodep}; }
}
