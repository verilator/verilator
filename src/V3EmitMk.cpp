// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Makefile
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Os.h"
#include "V3EmitMk.h"
#include "V3EmitCBase.h"

//######################################################################
// Emit statements and math operators

class EmitMk {
public:

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void putMakeClassEntry(V3OutMkFile& of, const string& name) {
        of.puts("\t"+V3Os::filenameNonDirExt(name)+" \\\n");
    }

    void emitClassMake() {
        // Generate the makefile
        V3OutMkFile of (v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_classes.mk");
        of.putsHeader();
        of.puts("# DESCR" "IPTION: Verilator output: Make include file with class lists\n");
        of.puts("#\n");
        of.puts("# This file lists generated Verilated files, for including in higher level makefiles.\n");
        of.puts("# See "+v3Global.opt.prefix()+".mk"+" for the caller.\n");

        of.puts("\n### Switches...\n");
        of.puts("# Coverage output mode?  0/1 (from --coverage)\n");
        of.puts("VM_COVERAGE = "); of.puts(v3Global.opt.coverage()?"1":"0"); of.puts("\n");
        of.puts("# Parallel builds?  0/1 (from --output-split)\n");
        of.puts("VM_PARALLEL_BUILDS = ");
        of.puts(v3Global.opt.outputSplit() ? "1" : "0"); of.puts("\n");
        of.puts("# Threaded output mode?  0/1/N threads (from --threads)\n");
        of.puts("VM_THREADS = "); of.puts(cvtToStr(v3Global.opt.threads())); of.puts("\n");
        of.puts("# Tracing output mode?  0/1 (from --trace)\n");
        of.puts("VM_TRACE = "); of.puts(v3Global.opt.trace()?"1":"0"); of.puts("\n");
        of.puts("# Tracing threaded output mode?  0/1 (from --trace-fst-thread)\n");
        of.puts("VM_TRACE_THREADED = "); of.puts(v3Global.opt.traceFormat().threaded()
                                                 ?"1":"0"); of.puts("\n");

        of.puts("\n### Object file lists...\n");
        for (int support=0; support<3; ++support) {
            for (int slow=0; slow<2; ++slow) {
                if (support==2) of.puts("# Global classes, need linked once per executable");
                else if (support) of.puts("# Generated support classes");
                else of.puts("# Generated module classes");
                if (slow) of.puts(", non-fast-path, compile with low/medium optimization\n");
                else of.puts(", fast-path, compile with highest optimization\n");
                of.puts(support==2?"VM_GLOBAL":support==1?"VM_SUPPORT":"VM_CLASSES");
                of.puts(slow?"_SLOW":"_FAST");
                of.puts(" += \\\n");
                if (support==2 && !slow) {
                    putMakeClassEntry(of, "verilated.cpp");
                    if (v3Global.dpi()) {
                        putMakeClassEntry(of, "verilated_dpi.cpp");
                    }
                    if (v3Global.opt.vpi()) {
                        putMakeClassEntry(of, "verilated_vpi.cpp");
                    }
                    if (v3Global.opt.savable()) {
                        putMakeClassEntry(of, "verilated_save.cpp");
                    }
                    if (v3Global.opt.coverage()) {
                        putMakeClassEntry(of, "verilated_cov.cpp");
                    }
                    if (v3Global.opt.trace()) {
                        putMakeClassEntry(of, v3Global.opt.traceSourceBase() + "_c.cpp");
                        if (v3Global.opt.systemC()) {
                            if (v3Global.opt.traceFormat() != TraceFormat::VCD) {
                                v3error("Unsupported: This trace format is not supported in SystemC, use VCD format.");
                            } else {
                                putMakeClassEntry(of, v3Global.opt.traceSourceLang() + ".cpp");
                            }
                        }
                    }
                    if (v3Global.opt.mtasks()) {
                        putMakeClassEntry(of, "verilated_threads.cpp");
                    }
                }
                else if (support==2 && slow) {
                }
                else {
                    for (AstNodeFile* nodep = v3Global.rootp()->filesp();
                         nodep; nodep = VN_CAST(nodep->nextp(), NodeFile)) {
                        AstCFile* cfilep = VN_CAST(nodep, CFile);
                        if (cfilep && cfilep->source()
                            && cfilep->slow()==(slow!=0)
                            && cfilep->support()==(support!=0)) {
                            putMakeClassEntry(of, cfilep->name());
                        }
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
        V3OutMkFile of (v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+".mk");
        of.putsHeader();
        of.puts("# DESCR" "IPTION: Verilator output: Makefile for building Verilated archive or executable\n");
        of.puts("#\n");
        of.puts("# Execute this makefile from the object directory:\n");
        of.puts("#    make -f "+v3Global.opt.prefix()+".mk"+"\n");
        of.puts("\n");

        if (v3Global.opt.exe()) {
            of.puts("default: "+v3Global.opt.exeName()+"\n");
        } else if (!v3Global.opt.protectLib().empty()) {
            of.puts("default: lib"+v3Global.opt.protectLib()+"\n");
        } else {
            of.puts("default: "+v3Global.opt.prefix()+"__ALL.a\n");
        }
        of.puts("\n### Constants...\n");
        of.puts("# Perl executable (from $PERL)\n");
        of.puts("PERL = "+V3Options::getenvPERL()+"\n");
        of.puts("# Path to Verilator kit (from $VERILATOR_ROOT)\n");
        of.puts("VERILATOR_ROOT = "+V3Options::getenvVERILATOR_ROOT()+"\n");
        of.puts("# SystemC include directory with systemc.h (from $SYSTEMC_INCLUDE)\n");
        of.puts(string("SYSTEMC_INCLUDE ?= ")+V3Options::getenvSYSTEMC_INCLUDE()+"\n");
        of.puts("# SystemC library directory with libsystemc.a (from $SYSTEMC_LIBDIR)\n");
        of.puts(string("SYSTEMC_LIBDIR ?= ")+V3Options::getenvSYSTEMC_LIBDIR()+"\n");

        of.puts("\n### Switches...\n");
        of.puts("# SystemC output mode?  0/1 (from --sc)\n");
        of.puts(string("VM_SC = ")+((v3Global.opt.systemC())?"1":"0")+"\n");
        of.puts("# Legacy or SystemC output mode?  0/1 (from --sc)\n");
        of.puts(string("VM_SP_OR_SC = $(VM_SC)\n"));
        of.puts("# Deprecated\n");
        of.puts(string("VM_PCLI = ")+(v3Global.opt.systemC()?"0":"1")+"\n");
        of.puts("# Deprecated: SystemC architecture to find link library path (from $SYSTEMC_ARCH)\n");
        of.puts(string("VM_SC_TARGET_ARCH = ")+V3Options::getenvSYSTEMC_ARCH()+"\n");

        of.puts("\n### Vars...\n");
        of.puts("# Design prefix (from --prefix)\n");
        of.puts(string("VM_PREFIX = ")+v3Global.opt.prefix()+"\n");
        of.puts("# Module prefix (from --prefix)\n");
        of.puts(string("VM_MODPREFIX = ")+v3Global.opt.modPrefix()+"\n");

        of.puts("# User CFLAGS (from -CFLAGS on Verilator command line)\n");
        of.puts("VM_USER_CFLAGS = \\\n");
        if (!v3Global.opt.protectLib().empty()) {
            of.puts("\t-fPIC \\\n");
        }
        const V3StringList& cFlags = v3Global.opt.cFlags();
        for (V3StringList::const_iterator it = cFlags.begin(); it != cFlags.end(); ++it) {
            of.puts("\t"+*it+" \\\n");
        }
        of.puts("\n");

        of.puts("# User LDLIBS (from -LDFLAGS on Verilator command line)\n");
        of.puts("VM_USER_LDLIBS = \\\n");
        const V3StringList& ldLibs = v3Global.opt.ldLibs();
        for (V3StringList::const_iterator it = ldLibs.begin(); it != ldLibs.end(); ++it) {
            of.puts("\t"+*it+" \\\n");
        }
        of.puts("\n");

        V3StringSet dirs;
        of.puts("# User .cpp files (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_CLASSES = \\\n");
        const V3StringSet& cppFiles = v3Global.opt.cppFiles();
        for (V3StringSet::const_iterator it = cppFiles.begin(); it != cppFiles.end(); ++it) {
            string cppfile = *it;
            of.puts("\t"+V3Os::filenameNonExt(cppfile)+" \\\n");
            string dir = V3Os::filenameDir(cppfile);
            dirs.insert(dir);
        }
        of.puts("\n");

        of.puts("# User .cpp directories (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_DIR = \\\n");
        for (V3StringSet::iterator it = dirs.begin(); it!=dirs.end(); ++it) {
            of.puts("\t"+*it+" \\\n");
        }
        of.puts("\n");

        of.puts("\n### Default rules...\n");
        of.puts("# Include list of all generated classes\n");
        of.puts("include "+v3Global.opt.prefix()+"_classes.mk\n");
        of.puts("# Include global rules\n");
        of.puts("include $(VERILATOR_ROOT)/include/verilated.mk\n");

        if (v3Global.opt.exe()) {
            of.puts("\n### Executable rules... (from --exe)\n");
            of.puts("VPATH += $(VM_USER_DIR)\n");
            of.puts("\n");
            for (V3StringSet::const_iterator it = cppFiles.begin(); it != cppFiles.end(); ++it) {
                string cppfile = *it;
                string basename = V3Os::filenameNonExt(cppfile);
                // NOLINTNEXTLINE(performance-inefficient-string-concatenation)
                of.puts(basename+".o: "+cppfile+"\n");
                of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<\n");
            }

            of.puts("\n### Link rules... (from --exe)\n");
            of.puts(v3Global.opt.exeName()+": $(VK_USER_OBJS) $(VK_GLOBAL_OBJS) $(VM_PREFIX)__ALL.a\n");
            of.puts("\t$(LINK) $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) -o $@ $(LIBS) $(SC_LIBS)\n");
            of.puts("\n");
        }

        if (!v3Global.opt.protectLib().empty()) {
            of.puts("\n### Library rules... (from --protect-lib)\n");
            of.puts("# Using -fPIC objects for both static and dynamic libraries "
                    "(which appears to work)\n");
            of.puts(v3Global.opt.protectLibName(false)+": $(VK_OBJS) $(VK_GLOBAL_OBJS)\n");
            of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o "+
                    v3Global.opt.protectLib()+".o "+v3Global.opt.protectLib()+".cpp\n");
            of.puts("\tar rc $@ $^ "+v3Global.opt.protectLib()+".o\n");
            of.puts("\n");

            of.puts(v3Global.opt.protectLibName(true)+": $(VM_PREFIX)__ALL.a $(VK_GLOBAL_OBJS)\n");
            of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -shared -o $@ "+v3Global.opt.protectLib()+".cpp $^\n");
            of.puts("\n");

            of.puts("lib"+v3Global.opt.protectLib()+": "+v3Global.opt.protectLibName(false)+
                    " "+v3Global.opt.protectLibName(true)+"\n");
        }

        of.puts("\n");
        of.putsHeader();
    }

public:
    explicit EmitMk() {
        emitClassMake();
        emitOverallMake();
    }
    virtual ~EmitMk() {}
};

//######################################################################
// Gate class functions

void V3EmitMk::emitmk() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    EmitMk emitter;
}
