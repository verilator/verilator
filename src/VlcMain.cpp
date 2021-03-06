// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: main()
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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

bool VlcOptions::onoff(const char* sw, const char* arg, bool& flag) {
    // if sw==arg, then return true (found it), and flag=true
    // if sw=="-no-arg", then return true (found it), and flag=false
    // if sw=="-noarg", then return true (found it), and flag=false
    // else return false
    if (arg[0] != '-') v3fatalSrc("OnOff switches must have leading dash.");
    if (0 == strcmp(sw, arg)) {
        flag = true;
        return true;
    } else if (0 == strncmp(sw, "-no", 3) && (0 == strcmp(sw + 3, arg + 1))) {
        flag = false;
        return true;
    } else if (0 == strncmp(sw, "-no-", 4) && (0 == strcmp(sw + 4, arg + 1))) {
        flag = false;
        return true;
    }
    return false;
}

void VlcOptions::parseOptsList(int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
#define shift \
    do { ++i; } while (false)
    for (int i = 0; i < argc;) {
        UINFO(9, " Option: " << argv[i] << endl);
        if (argv[i][0] == '-') {
            const char* sw = argv[i];
            bool flag = true;
            // Allow gnu -- switches
            if (sw[0] == '-' && sw[1] == '-') ++sw;
            // Single switches
            if (onoff(sw, "-annotate-all", flag /*ref*/)) {
                m_annotateAll = flag;
            } else if (onoff(sw, "-rank", flag /*ref*/)) {
                m_rank = flag;
            } else if (onoff(sw, "-unlink", flag /*ref*/)) {
                m_unlink = flag;
            }
            // Parameterized switches
            else if (!strcmp(sw, "-annotate-min") && (i + 1) < argc) {
                shift;
                m_annotateMin = atoi(argv[i]);
            } else if (!strcmp(sw, "-annotate") && (i + 1) < argc) {
                shift;
                m_annotateOut = argv[i];
            } else if (!strcmp(sw, "-debug")) {
                V3Error::debugDefault(3);
            } else if (!strcmp(sw, "-debugi") && (i + 1) < argc) {
                shift;
                V3Error::debugDefault(atoi(argv[i]));
            } else if (!strcmp(sw, "-V")) {
                showVersion(true);
                exit(0);
            } else if (!strcmp(sw, "-version")) {
                showVersion(false);
                exit(0);
            } else if (!strcmp(sw, "-write") && (i + 1) < argc) {
                shift;
                m_writeFile = argv[i];
            } else if (!strcmp(sw, "-write-info") && (i + 1) < argc) {
                shift;
                m_writeInfoFile = argv[i];
            } else {
                v3fatal("Invalid option: " << argv[i]);
            }
            shift;
        }  // - options
        else {
            addReadFile(argv[i]);
            shift;
        }
    }
#undef shift
}

void VlcOptions::showVersion(bool verbose) {
    cout << version();
    cout << endl;
    if (!verbose) return;

    cout << endl;
    cout << "Copyright 2003-2021 by Wilson Snyder.  Verilator is free software; you can\n";
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
