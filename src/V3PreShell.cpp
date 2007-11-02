// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Preprocessing wrapper
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2004-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <iostream>
#include <algorithm>
#include <list>
#include <set>

#include "V3Global.h"
#include "V3PreShell.h"
#include "V3PreProc.h"
#include "V3File.h"

//######################################################################

class V3PreShellImp {
protected:
    friend class V3PreShell;

    static V3PreShellImp s_preImp;
    static V3PreProc*	s_preprocp;

    //int debug() { return 9; }

    //---------------------------------------
    // METHODS

    void boot(char** env) {
	// Create the implementation pointer
	if (env) {}
	if (!s_preprocp) {
	    FileLine* cmdfl = new FileLine("COMMAND_LINE",0);
	    s_preprocp = V3PreProc::createPreProc(cmdfl);
	    s_preprocp->debug(debug());
	    // Default defines
	    FileLine* prefl = new FileLine("INTERNAL_VERILATOR_DEFINE",0);
	    s_preprocp->define(prefl,"verilator", "1");  // LEAK_OK
	    s_preprocp->define(prefl,"verilator3", "1");  // LEAK_OK
	    s_preprocp->define(prefl,"systemc_clock", "/*verilator systemc_clock*/");  // LEAK_OK
	    s_preprocp->define(prefl,"coverage_block_off", "/*verilator coverage_block_off*/");  // LEAK_OK
	}
    }

    void preproc (FileLine* fl, const string& modname, const string& vppFilename) {
	// Preprocess the given module, putting output in vppFilename
	unlink(vppFilename.c_str());
	UINFONL(1,"  Preprocessing "<<modname<<endl);

	// Open
	ofstream* ofp = NULL;
	ostream* osp;
	if (v3Global.opt.preprocOnly()) {
	    osp = &cout;
	} else if (!v3Global.opt.keepTempFiles()) {  // Must match unlink rule in V3Read.cpp
	    osp = ofp = V3File::new_ofstream_nodepend(vppFilename);
	} else {
	    osp = ofp = V3File::new_ofstream(vppFilename);
	}
	if (osp->fail()) {
	    fl->v3error("Cannot write preprocessor output: "+vppFilename);
	    return;
	}

	// Preprocess
	preprocOpen(fl, modname, "Cannot find file containing module: ");
	while (!s_preprocp->isEof()) {
	    string line = s_preprocp->getline();
	    *osp << line;
	}

	// Close
	if (ofp) {
	    ofp->close();
	    delete ofp;
	    osp = ofp = NULL;
	}
    }

    void preprocInclude (FileLine* fl, const string& modname) {
	preprocOpen(fl, modname, "Cannot find include file: ");
    }

    void preprocOpen (FileLine* fl, const string& modname, const string& errmsg) {
	// Allow user to put `defined names on the command line instead of filenames,
	// then convert them properly.
	string ppmodname = s_preprocp->removeDefines (modname);

	// Open include or master file
	string filename = v3Global.opt.filePath (fl, ppmodname, errmsg);
	if (filename=="") return;  // Not found

	UINFO(2,"    Reading "<<filename<<endl);
	s_preprocp->openFile(fl, filename);
    }

    // CONSTRUCTORS
    V3PreShellImp() {}
};

V3PreShellImp V3PreShellImp::s_preImp;
V3PreProc* V3PreShellImp::s_preprocp = NULL;

//######################################################################
// Perl class functions

void V3PreShell::boot(char** env) {
    V3PreShellImp::s_preImp.boot(env);
}
void V3PreShell::preproc(FileLine* fl, const string& modname, const string& vppFilename) {
    V3PreShellImp::s_preImp.preproc(fl, modname, vppFilename);
}
void V3PreShell::preprocInclude(FileLine* fl, const string& modname) {
    V3PreShellImp::s_preImp.preprocInclude(fl, modname);
}
void V3PreShell::define(const string& name, const string& value) {
    FileLine* prefl = new FileLine("COMMAND_LINE_DEFINE",0);
    V3PreShellImp::s_preprocp->define(prefl, name,value,"");
}
void V3PreShell::undef(const string& name) {
    V3PreShellImp::s_preprocp->undef(name);
}
