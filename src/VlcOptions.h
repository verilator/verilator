// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Command line options
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

#ifndef _VLCOPTIONS_H_
#define _VLCOPTIONS_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "config_rev.h"

#include <map>
#include <set>
#include <vector>

//######################################################################
// V3Options - Command line options

typedef std::set<string> VlStringSet;

class VlcOptions {
    // MEMBERS (general options)
    // clang-format off
    string m_annotateOut;       // main switch: --annotate I<output_directory>
    bool m_annotateAll=false;         // main switch: --annotate-all
    int m_annotateMin=10;          // main switch: --annotate-min I<count>
    VlStringSet m_readFiles;    // main switch: --read
    bool m_rank=false;                // main switch: --rank
    bool m_unlink=false;              // main switch: --unlink
    string m_writeFile;         // main switch: --write
    string m_writeInfoFile;     // main switch: --write-info
    // clang-format on

private:
    // METHODS
    static void showVersion(bool verbose);
    static bool onoff(const char* sw, const char* arg, bool& flag);

public:
    // CONSTRUCTORS
    VlcOptions() {}
    ~VlcOptions() {}

    // METHODS
    void parseOptsList(int argc, char** argv);
    void addReadFile(const string& filename);

    // ACCESSORS (options)
    const VlStringSet& readFiles() const { return m_readFiles; }
    string annotateOut() const { return m_annotateOut; }
    bool annotateAll() const { return m_annotateAll; }
    int annotateMin() const { return m_annotateMin; }
    bool rank() const { return m_rank; }
    bool unlink() const { return m_unlink; }
    string writeFile() const { return m_writeFile; }
    string writeInfoFile() const { return m_writeInfoFile; }

    // METHODS (from main)
    static string version();
};

//######################################################################

#endif  // guard
