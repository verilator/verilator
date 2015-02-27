// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: Top global container
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

#ifndef _VLCTOP_H_
#define _VLCTOP_H_ 1

#include "config_build.h"
#include "verilatedos.h"
#include "VlcOptions.h"
#include "VlcTest.h"
#include "VlcPoint.h"
#include "VlcSource.h"

//######################################################################
// VlcTop - Top level options container

class VlcTop {
public:
    // PUBLIC MEMBERS
    VlcOptions opt;		//< Runtime options
private:
    // MEMBERS
    VlcTests	m_tests;	//< List of all tests (all coverage files)
    VlcPoints	m_points;	//< List of all points
    VlcSources	m_sources;	//< List of all source files to annotate

    // METHODS
    void createDir(const string& dirname);
    void annotateCalc();
    void annotateCalcNeeded();
    void annotateOutputFiles(const string& dirname);

public:
    // CONSTRUCTORS
    VlcTop() {}
    ~VlcTop() {}

    // ACCESSORS
    VlcTests& tests() { return m_tests; }
    VlcPoints& points() { return m_points; }
    VlcSources& sources() { return m_sources; }

    // METHODS
    void annotate(const string& dirname);
    void readCoverage(const string& filename, bool nonfatal=false);
    void writeCoverage(const string& filename);

    void rank();
};

//######################################################################

#endif // guard
