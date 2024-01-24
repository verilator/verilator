// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common implementations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3File.h"
#include "V3HierBlock.h"
#include "V3LinkCells.h"
#include "V3Parse.h"
#include "V3ParseSym.h"
#include "V3Stats.h"

//######################################################################
// V3Global

void V3Global::boot() {
    UASSERT(!m_rootp, "call once");
    m_rootp = new AstNetlist;
}

void V3Global::shutdown() {
    VL_DO_CLEAR(delete m_hierPlanp, m_hierPlanp = nullptr);  // delete nullptr is safe
#ifdef VL_LEAK_CHECKS
    if (m_rootp) VL_DO_CLEAR(m_rootp->deleteTree(), m_rootp = nullptr);
#endif
}

void V3Global::checkTree() const { rootp()->checkTree(); }

void V3Global::readFiles() {
    // NODE STATE
    //   AstNode::user4p()      // VSymEnt*    Package and typedef symbol names
    const VNUser4InUse inuser4;

    VInFilter filter{v3Global.opt.pipeFilter()};
    V3ParseSym parseSyms{v3Global.rootp()};  // Symbol table must be common across all parsing

    V3Parse parser{v3Global.rootp(), &filter, &parseSyms};

    // Parse the std package
    if (v3Global.opt.std()) {
        parser.parseFile(new FileLine{V3Options::getStdPackagePath()},
                         V3Options::getStdPackagePath(), false,
                         "Cannot find verilated_std.sv containing built-in std:: definitions: ");
    }

    // Read top module
    const V3StringList& vFiles = v3Global.opt.vFiles();
    for (const string& filename : vFiles) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filename, false,
                         "Cannot find file containing module: ");
    }

    // Read libraries
    // To be compatible with other simulators,
    // this needs to be done after the top file is read
    const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
    for (const string& filename : libraryFiles) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filename, true,
                         "Cannot find file containing library module: ");
    }

    // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));
    V3Error::abortIfErrors();

    if (!v3Global.opt.preprocOnly()) {
        // Resolve all modules cells refer to
        V3LinkCells::link(v3Global.rootp(), &filter, &parseSyms);
    }
}

void V3Global::removeStd() {
    // Delete the std package if unused
    if (!usesStdPackage()) {
        if (AstNodeModule* stdp = v3Global.rootp()->stdPackagep()) {
            v3Global.rootp()->stdPackagep(nullptr);
            VL_DO_DANGLING(stdp->unlinkFrBack()->deleteTree(), stdp);
        }
    }
}

string V3Global::debugFilename(const string& nameComment, int newNumber) {
    ++m_debugFileNumber;
    if (newNumber) m_debugFileNumber = newNumber;
    return opt.hierTopDataDir() + "/" + opt.prefix() + "_" + digitsFilename(m_debugFileNumber)
           + "_" + nameComment;
}
string V3Global::digitsFilename(int number) {
    std::stringstream ss;
    ss << std::setfill('0') << std::setw(3) << number;
    return ss.str();
}

void V3Global::dumpCheckGlobalTree(const string& stagename, int newNumber, bool doDump) {
    const string treeFilename = v3Global.debugFilename(stagename + ".tree", newNumber);
    v3Global.rootp()->dumpTreeFile(treeFilename, doDump);
    if (v3Global.opt.dumpTreeDot()) {
        v3Global.rootp()->dumpTreeDotFile(treeFilename + ".dot", doDump);
    }
    if (v3Global.opt.stats()) V3Stats::statsStage(stagename);
}

const std::string& V3Global::ptrToId(const void* p) {
    const auto pair = m_ptrToId.emplace(p, "");
    if (pair.second) {
        std::ostringstream os;
        if (p) {
            os << "(";
            unsigned id = m_ptrToId.size();
            do { os << static_cast<char>('A' + id % 26); } while (id /= 26);
            os << ")";
        } else {
            os << "0";
        }
        pair.first->second = os.str();
    }
    return pair.first->second;
}
