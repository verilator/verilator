// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: verilator_coverage: main()
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

// Cheat for speed and compile .cpp files into one object
#define _V3ERROR_NO_GLOBAL_ 1
#include "V3Error.cpp"
#include "V3String.cpp"
#include "V3Os.cpp"
#include "VlcTop.cpp"

#include "VlcOptions.h"
#include "VlcTop.h"

#include <fstream>
#include <algorithm>
#include <unistd.h>

//######################################################################
// VlcOptions

void VlcOptions::addReadFile(const string& filename) {
    if (m_readFiles.find(filename) == m_readFiles.end()) {
	m_readFiles.insert(filename);
    }
}

string VlcOptions::version() {
    string ver = DTVERSION;
    ver += " rev "+cvtToStr(DTVERSION_rev);
    return ver;
}

bool VlcOptions::onoff(const char* sw, const char* arg, bool& flag) {
    // if sw==arg, then return true (found it), and flag=true
    // if sw=="-no-arg", then return true (found it), and flag=false
    // if sw=="-noarg", then return true (found it), and flag=false
    // else return false
    if (arg[0]!='-') v3fatalSrc("OnOff switches must have leading dash.\n");
    if (0==strcmp(sw,arg)) { flag=true; return true; }
    else if (0==strncmp(sw,"-no",3) && (0==strcmp(sw+3,arg+1))) { flag=false; return true; }
    else if (0==strncmp(sw,"-no-",4) && (0==strcmp(sw+4,arg+1))) { flag=false; return true; }
    return false;
}

void VlcOptions::parseOptsList(int argc, char** argv) {
    // Parse parameters
    // Note argc and argv DO NOT INCLUDE the filename in [0]!!!
    // May be called recursively when there are -f files.
#define shift { ++i; }
    for (int i=0; i<argc; )  {
	UINFO(9, " Option: "<<argv[i]<<endl);
	if (argv[i][0]=='-') {
	    const char *sw = argv[i];
	    bool flag = true;
	    // Allow gnu -- switches
	    if (sw[0]=='-' && sw[1]=='-') ++sw;
	    if (0) {}
	    // Single switches
	    else if ( onoff   (sw, "-annotate-all", flag/*ref*/) ) { m_annotateAll = flag; }
	    else if ( onoff   (sw, "-rank", flag/*ref*/) ) { m_rank = flag; }
	    else if ( onoff   (sw, "-unlink", flag/*ref*/) )	{ m_unlink = flag; }
	    // Parameterized switches
	    else if ( !strcmp (sw, "-annotate") && (i+1)<argc ) {
		shift;
		m_annotateOut = argv[i];
	    }
	    else if ( !strcmp (sw, "-debug") ) {
		V3Error::debugDefault(3);
	    }
	    else if ( !strcmp (sw, "-debugi") && (i+1)<argc ) {
		shift;
		V3Error::debugDefault(atoi(argv[i]));
	    }
	    else if ( !strcmp (sw, "-V") ) {
		showVersion(true);
		exit(0);
	    }
	    else if ( !strcmp (sw, "-version") ) {
		showVersion(false);
		exit(0);
	    }
	    else if ( !strcmp (sw, "-write") && (i+1)<argc ) {
		shift;
		m_writeFile = argv[i];
	    }
	    else {
		v3fatal ("Invalid option: "<<argv[i]);
	    }
	    shift;
	} // - options
	else if (1) {
	    addReadFile(argv[i]);
	    shift;
	}
	else {
	    v3fatal ("Invalid argument: "<<argv[i]);
	    shift;
	}
    }
#undef shift
}

void VlcOptions::showVersion(bool verbose) {
    cout <<version();
    cout <<endl;
    if (!verbose) return;

    cout <<endl;
    cout << "Copyright 2003-2015 by Wilson Snyder.  Verilator is free software; you can\n";
    cout << "redistribute it and/or modify the Verilator internals under the terms of\n";
    cout << "either the GNU Lesser General Public License Version 3 or the Perl Artistic\n";
    cout << "License Version 2.0.\n";

    cout <<endl;
    cout << "See http://www.veripool.org/verilator for documentation\n";
}

//######################################################################

int main(int argc, char** argv, char** env) {
    // General initialization
    ios::sync_with_stdio();

    VlcTop top;

    // Command option parsing
    top.opt.parseOptsList(argc-1, argv+1);

    if (top.opt.readFiles().empty()) {
	top.opt.addReadFile("vlt_coverage.pl");
    }

    const VlStringSet& readFiles = top.opt.readFiles();
    for (VlStringSet::iterator it = readFiles.begin(); it != readFiles.end(); ++it) {
	string filename = *it;
	top.readCoverage(filename);
    }

    if (debug() >= 9) {
	top.tests().dump(true);
	top.points().dump();
    }

    V3Error::abortIfWarnings();
    if (top.opt.annotateOut() != "") {
        top.annotate(top.opt.annotateOut());
    }

    if (top.opt.rank()) {
	top.rank();
	top.tests().dump(false);
    }

    if (top.opt.writeFile() != "") {
	top.writeCoverage(top.opt.writeFile());
	V3Error::abortIfWarnings();
        if (top.opt.unlink()) {
	    const VlStringSet& readFiles = top.opt.readFiles();
	    for (VlStringSet::iterator it = readFiles.begin(); it != readFiles.end(); ++it) {
		string filename = *it;
		unlink(filename.c_str());
	    }
        }
    }
    
    // Final writing shouldn't throw warnings, but...
    V3Error::abortIfWarnings();

    UINFO(1,"Done, Exiting...\n");
}

// Local Variables:
// compile-command: "v4make bin/verilator_coverage --debugi 9 test_regress/t/t_vlcov_data_*.dat"
// End:

