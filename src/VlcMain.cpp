// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: main()
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

// clang-format off
#include "config_build.h"
#ifndef HAVE_CONFIG_BUILD
# error "Something failed during ./configure as config_build.h is incomplete. Perhaps you used autoreconf, don't."
#endif
// clang-format on

#include "verilatedos.h"

// Cheat for speed and compile .cpp files into one object
#define V3ERROR_NO_GLOBAL_
#include "V3Error.cpp"
#include "V3String.cpp"
#define V3OPTION_PARSER_NO_VOPTION_BOOL
#include "V3OptionParser.cpp"
#include "V3Os.cpp"
#include "VlcTop.cpp"

#include "VlcOptions.h"
#include "VlcTop.h"

#include <algorithm>
#include <fstream>

//######################################################################
// VlcOptions

void VlcOptions::addReadFile(const string& filename) { m_readFiles.insert(filename); }

string VlcOptions::version() {
    string ver = DTVERSION;
    ver += " rev " + cvtToStr(DTVERSION_rev);
    return ver;
}

void VlcOptions::parseOptsList(int argc, char** argv) {
    V3OptionParser parser;
    V3OptionParser::AppendHelper DECL_OPTION{parser};
    V3OPTION_PARSER_DECL_TAGS;

    DECL_OPTION("-annotate-all", OnOff, &m_annotateAll);
    DECL_OPTION("-rank", OnOff, &m_rank);
    DECL_OPTION("-unlink", OnOff, &m_unlink);
    DECL_OPTION("-annotate-min", Set, &m_annotateMin);
    DECL_OPTION("-annotate", Set, &m_annotateOut);
    DECL_OPTION("-debug", CbCall, []() { V3Error::debugDefault(3); });
    DECL_OPTION("-debugi", CbVal, [](int v) { V3Error::debugDefault(v); });
    DECL_OPTION("-V", CbCall, []() {
        showVersion(true);
        std::exit(0);
    });
    DECL_OPTION("-version", CbCall, []() {
        showVersion(false);
        std::exit(0);
    });
    DECL_OPTION("-write", Set, &m_writeFile);
    DECL_OPTION("-write-info", Set, &m_writeInfoFile);
    parser.finalize();

    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
    for (int i = 0; i < argc;) {
        UINFO(9, " Option: " << argv[i] << endl);
        if (argv[i][0] == '-') {
            if (const int consumed = parser.parse(i, argc, argv)) {
                i += consumed;
            } else {
                v3fatal("Invalid option: " << argv[i] << parser.getSuggestion(argv[i]));
                ++i;  // LCOV_EXCL_LINE
            }
        } else {
            addReadFile(argv[i]);
            ++i;
        }
    }
}

void VlcOptions::showVersion(bool verbose) {
    cout << version();
    cout << endl;
    if (!verbose) return;

    cout << endl;
    cout << "Copyright 2003-2022 by Wilson Snyder.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout << endl;
    cout << "See https://verilator.org for documentation\n";
}

//######################################################################

int main(int argc, char** argv, char** /*env*/) {
    // General initialization
    std::ios::sync_with_stdio();

    VlcTop top;

    // Command option parsing
    top.opt.parseOptsList(argc - 1, argv + 1);

    if (top.opt.readFiles().empty()) top.opt.addReadFile("vlt_coverage.dat");

    {
        const VlStringSet& readFiles = top.opt.readFiles();
        for (const auto& filename : readFiles) top.readCoverage(filename);
    }

    if (debug() >= 9) {
        top.tests().dump(true);
        top.points().dump();
    }

    V3Error::abortIfWarnings();
    if (!top.opt.annotateOut().empty()) top.annotate(top.opt.annotateOut());

    if (top.opt.rank()) {
        top.rank();
        top.tests().dump(false);
    }

    if (!top.opt.writeFile().empty() || !top.opt.writeInfoFile().empty()) {
        if (!top.opt.writeFile().empty()) top.writeCoverage(top.opt.writeFile());
        if (!top.opt.writeInfoFile().empty()) top.writeInfo(top.opt.writeInfoFile());
        V3Error::abortIfWarnings();
        if (top.opt.unlink()) {
            const VlStringSet& readFiles = top.opt.readFiles();
            for (const auto& filename : readFiles) { unlink(filename.c_str()); }
        }
    }

    // Final writing shouldn't throw warnings, but...
    V3Error::abortIfWarnings();

    UINFO(1, "Done, Exiting...\n");
}

// Local Variables:
// compile-command: "v4make bin/verilator_coverage --debugi 9 test_regress/t/t_vlcov_data_*.dat"
// End:
