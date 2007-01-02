// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Emit Makefile
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
#include <math.h>
#include <map>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3EmitMk.h"
#include "V3EmitCBase.h"

//######################################################################
// Emit statements and math operators

class EmitMkVisitor : public EmitCBaseVisitor {
public:
    //int debug() { return 9; }

    // METHODS
    void emitClassMake() {
	// Generate the makefile
	V3OutMkFile of (v3Global.opt.makeDir()+"/"+ v3Global.opt.prefix() + "_classes.mk");
	of.putsHeader();
	of.puts("\n");

	of.puts("VM_TRACE = "); of.puts(v3Global.opt.trace()?"1":"0"); of.puts("\n");
	of.puts("\n");

	for (int support=0; support<2; support++) {
	    for (int slow=0; slow<2; slow++) {
		of.puts(support?"VM_SUPPORT":"VM_CLASSES");
		of.puts(slow?"_SLOW":"_FAST");
		of.puts(" += \\\n");
		for (AstCFile* nodep = v3Global.rootp()->filesp(); nodep; nodep=nodep->nextp()->castCFile()) {
		    if (nodep->source() && nodep->slow()==slow && nodep->support()==support) {
			of.puts("\t"+V3Options::filenameNonDirExt(nodep->name())+" \\\n");
		    }
		}
		of.puts("\n");
	    }
	}
	of.puts("\n");
	of.putsHeader();
    }

    void emitOverallMake() {
	// Generate the makefile
	V3OutMkFile of (v3Global.opt.makeDir()+"/"+ v3Global.opt.prefix() + ".mk");
	of.putsHeader();
	of.puts("\n");

	if (v3Global.opt.exe()) {
	    of.puts("default: "+v3Global.opt.prefix()+"\n");
	} else {
	    of.puts("default: "+v3Global.opt.prefix()+"__ALL.a\n");
	}
	of.puts("\n# Constants...\n");
	of.puts("PERL = "+V3Options::getenvStr("PERL","perl")+"\n");
	of.puts("VERILATOR_ROOT = "+V3Options::getenvStr("VERILATOR_ROOT","")+"\n");
	of.puts("SYSTEMPERL = "+V3Options::getenvStr("SYSTEMPERL","")+"\n");

	of.puts("\n# Switches...\n");
	of.puts(string("VM_SP = ")+(v3Global.opt.systemPerl()?"1":"0")+"\n");
	of.puts(string("VM_SC = ")+((v3Global.opt.systemC()&&!v3Global.opt.systemPerl())?"1":"0")+"\n");
	of.puts(string("VM_SP_OR_SC = ")+(v3Global.opt.systemC()?"1":"0")+"\n");
	of.puts(string("VM_PCLI = ")+(v3Global.opt.systemC()?"0":"1")+"\n");
	of.puts(string("VM_SC_TARGET_ARCH = ")+V3Options::getenvStr("SYSTEMC_ARCH","")+"\n");

	of.puts("\n# Vars...\n");
	of.puts(string("VM_PREFIX = ")+v3Global.opt.prefix()+"\n");
	of.puts(string("VM_MODPREFIX = ")+v3Global.opt.modPrefix()+"\n");

	// Imply generating verilated.o
	if (v3Global.opt.exe()) {
	    v3Global.opt.addCppFile("verilated.cpp");
	    if (v3Global.opt.trace()) {
		v3Global.opt.addCppFile("SpTraceVcdC.cpp");
	    }
	}

	V3StringSet dirs;

	of.puts("VM_USER_CLASSES = \\\n");
	for (V3StringSet::iterator it = v3Global.opt.cppFiles().begin();
	     it != v3Global.opt.cppFiles().end(); ++it) {
	    string cppfile = *it;
	    of.puts("\t"+V3Options::filenameNonExt(cppfile)+" \\\n");
	    string dir = V3Options::filenameDir(cppfile);
	    if (dirs.find(dir) == dirs.end()) dirs.insert(dir);
	}
	of.puts("\n");

	of.puts("VM_USER_DIR = \\\n");
	for (V3StringSet::iterator it = dirs.begin(); it!=dirs.end(); ++it) {
	    of.puts("\t"+*it+" \\\n");
	}
	of.puts("\n");

	of.puts("\n# Default rules...\n");
	of.puts("include "+v3Global.opt.prefix()+"_classes.mk\n");
	of.puts("include $(VERILATOR_ROOT)/include/verilated.mk\n");

	of.puts("\n# Local rules...\n");
	if (v3Global.opt.exe()) {
	    of.puts("VPATH += $(VM_USER_DIR)\n");
	    of.puts("\n");
	    for (V3StringSet::iterator it = v3Global.opt.cppFiles().begin();
		 it != v3Global.opt.cppFiles().end(); ++it) {
		string cppfile = *it;
		string basename = V3Options::filenameNonExt(cppfile);
		of.puts(basename+".o: "+cppfile+"\n");
		of.puts("\t$(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<\n");
	    }

	    of.puts("\n# Link rules...\n");
	    of.puts(v3Global.opt.prefix()+": $(VK_USER_OBJS) $(SP_SRCS) $(VM_PREFIX)__ALL.a\n");
	    of.puts("\t$(CXX) $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) -o $@ $(LIBS) 2>&1 | c++filt\n");
	    of.puts("\n");
	}

	of.puts("\n");
	of.putsHeader();
    }

    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->v3fatalSrc("No visitors implemented.");
    }

public:
    EmitMkVisitor(AstNetlist*) {
	emitClassMake();
	emitOverallMake();
    }
    virtual ~EmitMkVisitor() {}
};

//######################################################################
// Gate class functions

void V3EmitMk::emitmk(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitMkVisitor visitor (nodep);
}
