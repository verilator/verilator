// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Command line options
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
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

#ifndef _VLCOPTIONS_H_
#define _VLCOPTIONS_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include <string>
#include <vector>
#include <map>
#include <set>

#include "config_rev.h"

//######################################################################
// V3Options - Command line options

typedef vector<string> VlStringList;
typedef set<string> VlStringSet;

class VlcOptions {
    // MEMBERS (general options)
    string	m_annotateOut;	// main switch: --annotate I<output_directory>
    bool	m_annotateAll;	// main switch: --annotate-all
    int		m_annotateMin;	// main switch: --annotate-min I<count>
    VlStringSet	m_readFiles;	// main switch: --read
    bool	m_rank;		// main switch: --rank
    bool	m_unlink;	// main switch: --unlink
    string	m_writeFile;	// main switch: --write

private:
    // METHODS
    void showVersion(bool verbose);
    bool onoff(const char* sw, const char* arg, bool& flag);

public:
    // CREATORS
    VlcOptions() {
	m_annotateAll = false;
	m_annotateMin = 10;
	m_rank = false;
	m_unlink = false;
    }
    ~VlcOptions() {}
    void setDebugMode(int level);

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
    
    // METHODS (from main)
    static string version();
};

//######################################################################

#endif // guard
