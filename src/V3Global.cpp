// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Common implementations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstMT.h"

#include "V3Global.h"

#include "V3EmitV.h"
#include "V3Error.h"
#include "V3File.h"
#include "V3HierBlock.h"
#include "V3LinkCells.h"
#include "V3Parse.h"
#include "V3Stats.h"
#include "V3ThreadPool.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// AddressSanitizer default options

#ifdef VL_ASAN
extern "C" const char* __asan_default_options() {
    // See https://github.com/google/sanitizers/wiki/SanitizerCommonFlags
    // or 'env ASAN_OPTIONS=help=1 ./verilator_bin'
    return ""
#ifndef VL_LEAK_CHECKS
           ":detect_leaks=0"
#endif
        ;
}
#endif

//######################################################################
// V3Global

void V3Global::boot() {
    UASSERT(!m_rootp, "call once");
    m_rootp = new AstNetlist;
}

void V3Global::shutdown() {
    VL_DO_CLEAR(delete m_hierPlanp, m_hierPlanp = nullptr);  // delete nullptr is safe
    VL_DO_CLEAR(delete m_threadPoolp, m_threadPoolp = nullptr);  // delete nullptr is safe
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

    V3Parse parser{v3Global.rootp(), &filter};

    // Parse the std waivers
    if (v3Global.opt.stdWaiver()) {
        parser.parseFile(
            new FileLine{V3Options::getStdWaiverPath()}, V3Options::getStdWaiverPath(), false,
            "work", "Cannot find verilated_std_waiver.vlt containing built-in lint waivers: ");
    }
    // Read .vlt files
    for (const VFileLibName& filelib : v3Global.opt.vltFiles()) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filelib.filename(), false,
                         filelib.libname(), "Cannot find file containing .vlt file: ");
    }

    // Parse the std package
    if (v3Global.opt.stdPackage()) {
        parser.parseFile(new FileLine{V3Options::getStdPackagePath()},
                         V3Options::getStdPackagePath(), false, "work",
                         "Cannot find verilated_std.sv containing built-in std:: definitions: ");
    }

    // Read top module
    for (const auto& filelib : v3Global.opt.vFiles()) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filelib.filename(), false,
                         filelib.libname(), "Cannot find file containing module: ");
    }

    // Read libraries
    // To be compatible with other simulators,
    // this needs to be done after the top file is read
    for (const auto& filelib : v3Global.opt.libraryFiles()) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filelib.filename(), true,
                         filelib.libname(), "Cannot find file containing library module: ");
    }

    // Read hierarchical type parameter file
    for (const auto& filelib : v3Global.opt.hierParamFile()) {
        parser.parseFile(new FileLine{FileLine::commandLineFilename()}, filelib.filename(), false,
                         filelib.libname(),
                         "Cannot open file containing hierarchical parameter declarations: ");
    }

    // v3Global.rootp()->dumpTreeFile(v3Global.debugFilename("parse.tree"));
    V3Error::abortIfErrors();

    if (!v3Global.opt.preprocOnly() || v3Global.opt.preprocResolve()) {
        // Resolve all modules cells refer to
        V3LinkCells::link(v3Global.rootp(), &filter);
    }

    V3Global::dumpCheckGlobalTree("cells", false, dumpTreeEitherLevel() >= 9);
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
    if (dumpTreeLevel()) v3Global.rootp()->dumpTreeFile(treeFilename, doDump);
    if (dumpTreeJsonLevel()) {
        v3Global.rootp()->dumpTreeJsonFile(treeFilename + ".json", doDump);
    }
    if (v3Global.opt.dumpTreeDot()) {
        v3Global.rootp()->dumpTreeDotFile(treeFilename + ".dot", doDump);
    }
    if (v3Global.opt.stats()) V3Stats::statsStage(stagename);

    if (doDump && v3Global.opt.debugEmitV()) V3EmitV::debugEmitV(treeFilename + ".v");
    if (v3Global.opt.debugCheck() || dumpTreeEitherLevel()) {
        // Error check
        v3Global.rootp()->checkTree();
        // Broken isn't part of check tree because it can munge iterp's
        // set by other steps if it is called in the middle of other operations
        V3Broken::brokenAll(v3Global.rootp());
    }
}

void V3Global::idPtrMapDumpJson(std::ostream& os) {
    std::string sep = "\n  ";
    os << "\"pointers\": {";
    for (const auto& itr : m_ptrToId) {
        os << sep << '"' << itr.second << "\": \"" << cvtToHex(itr.first) << '"';
        sep = ",\n  ";
    }
    os << "\n }";
}

void V3Global::saveJsonPtrFieldName(const std::string& fieldName) {
    m_jsonPtrNames.insert(fieldName);
}

void V3Global::ptrNamesDumpJson(std::ostream& os) {
    std::string sep = "\n  ";
    os << "\"ptrFieldNames\": [";
    for (const auto& itr : m_jsonPtrNames) {
        os << sep << '"' << itr << '"';
        sep = ",\n  ";
    }
    os << "\n ]";
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

std::vector<std::string> V3Global::verilatedCppFiles() {
    std::vector<std::string> result;
    result.emplace_back("verilated.cpp");
    if (v3Global.dpi()) result.emplace_back("verilated_dpi.cpp");
    if (v3Global.opt.vpi()) result.emplace_back("verilated_vpi.cpp");
    if (v3Global.opt.savable()) result.emplace_back("verilated_save.cpp");
    if (v3Global.opt.coverage()) result.emplace_back("verilated_cov.cpp");
    if (v3Global.opt.trace()) result.emplace_back(v3Global.opt.traceSourceBase() + "_c.cpp");
    if (v3Global.usesProbDist()) result.emplace_back("verilated_probdist.cpp");
    if (v3Global.usesTiming()) result.emplace_back("verilated_timing.cpp");
    if (v3Global.useRandomizeMethods()) result.emplace_back("verilated_random.cpp");
    result.emplace_back("verilated_threads.cpp");
    if (v3Global.opt.usesProfiler()) result.emplace_back("verilated_profiler.cpp");
    return result;
}
