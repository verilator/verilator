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
#include "V3HierBlock.h"
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
        of.puts("\t" + V3Os::filenameNonDirExt(name) + " \\\n");
    }

    void emitClassMake() {
        // Generate the makefile
        V3OutMkFile of(v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "_classes.mk");
        of.putsHeader();
        of.puts("# DESCR"
                "IPTION: Verilator output: Make include file with class lists\n");
        of.puts("#\n");
        of.puts("# This file lists generated Verilated files, for including "
                "in higher level makefiles.\n");
        of.puts("# See " + v3Global.opt.prefix() + ".mk" + " for the caller.\n");

        of.puts("\n### Switches...\n");
        of.puts("# C11 constructs required?  0/1 (from --threads, "
                "--trace-threads or use of classes)\n");
        of.puts("VM_C11 = ");
        of.puts(v3Global.needC11() || v3Global.opt.threads() ? "1" : "0");
        of.puts("\n");
        of.puts("# Coverage output mode?  0/1 (from --coverage)\n");
        of.puts("VM_COVERAGE = ");
        of.puts(v3Global.opt.coverage() ? "1" : "0");
        of.puts("\n");
        of.puts("# Parallel builds?  0/1 (from --output-split)\n");
        of.puts("VM_PARALLEL_BUILDS = ");
        of.puts(v3Global.useParallelBuild() ? "1" : "0");
        of.puts("\n");
        of.puts("# Threaded output mode?  0/1/N threads (from --threads)\n");
        of.puts("VM_THREADS = ");
        of.puts(cvtToStr(v3Global.opt.threads()));
        of.puts("\n");
        of.puts("# Tracing output mode?  0/1 (from --trace/--trace-fst)\n");
        of.puts("VM_TRACE = ");
        of.puts(v3Global.opt.trace() ? "1" : "0");
        of.puts("\n");
        of.puts("# Tracing threaded output mode?  0/1/N threads (from --trace-thread)\n");
        of.puts("VM_TRACE_THREADS = ");
        of.puts(cvtToStr(v3Global.opt.trueTraceThreads()));
        of.puts("\n");
        of.puts("# Separate FST writer thread? 0/1 (from --trace-fst with --trace-thread > 0)\n");
        of.puts("VM_TRACE_FST_WRITER_THREAD = ");
        of.puts(v3Global.opt.traceThreads() && v3Global.opt.traceFormat().fst() ? "1" : "0");
        of.puts("\n");

        of.puts("\n### Object file lists...\n");
        for (int support = 0; support < 3; ++support) {
            for (int slow = 0; slow < 2; ++slow) {
                if (support == 2) {
                    of.puts("# Global classes, need linked once per executable");
                } else if (support) {
                    of.puts("# Generated support classes");
                } else {
                    of.puts("# Generated module classes");
                }
                if (slow) {
                    of.puts(", non-fast-path, compile with low/medium optimization\n");
                } else {
                    of.puts(", fast-path, compile with highest optimization\n");
                }
                of.puts(support == 2 ? "VM_GLOBAL" : support == 1 ? "VM_SUPPORT" : "VM_CLASSES");
                of.puts(slow ? "_SLOW" : "_FAST");
                of.puts(" += \\\n");
                if (support == 2 && v3Global.opt.hierMode()) {
                    // Do nothing because VM_GLOBAL is necessary per executable. Top module will
                    // have them.
                } else if (support == 2 && !slow) {
                    putMakeClassEntry(of, "verilated.cpp");
                    if (v3Global.dpi()) { putMakeClassEntry(of, "verilated_dpi.cpp"); }
                    if (v3Global.opt.vpi()) { putMakeClassEntry(of, "verilated_vpi.cpp"); }
                    if (v3Global.opt.savable()) { putMakeClassEntry(of, "verilated_save.cpp"); }
                    if (v3Global.opt.coverage()) { putMakeClassEntry(of, "verilated_cov.cpp"); }
                    if (v3Global.opt.trace()) {
                        putMakeClassEntry(of, v3Global.opt.traceSourceBase() + "_c.cpp");
                        if (v3Global.opt.systemC()) {
                            if (v3Global.opt.traceFormat() != TraceFormat::VCD) {
                                v3warn(E_UNSUPPORTED,
                                       "Unsupported: This trace format is not supported "
                                       "in SystemC, use VCD format.");
                            } else {
                                putMakeClassEntry(of, v3Global.opt.traceSourceLang() + ".cpp");
                            }
                        }
                    }
                    if (v3Global.opt.mtasks()) { putMakeClassEntry(of, "verilated_threads.cpp"); }
                } else if (support == 2 && slow) {
                } else {
                    for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
                         nodep = VN_CAST(nodep->nextp(), NodeFile)) {
                        AstCFile* cfilep = VN_CAST(nodep, CFile);
                        if (cfilep && cfilep->source() && cfilep->slow() == (slow != 0)
                            && cfilep->support() == (support != 0)) {
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
        V3OutMkFile of(v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".mk");
        of.putsHeader();
        of.puts("# DESCR"
                "IPTION: Verilator output: "
                "Makefile for building Verilated archive or executable\n");
        of.puts("#\n");
        of.puts("# Execute this makefile from the object directory:\n");
        of.puts("#    make -f " + v3Global.opt.prefix() + ".mk" + "\n");
        of.puts("\n");

        if (v3Global.opt.exe()) {
            of.puts("default: " + v3Global.opt.exeName() + "\n");
        } else if (!v3Global.opt.protectLib().empty()) {
            of.puts("default: lib" + v3Global.opt.protectLib() + "\n");
        } else {
            of.puts("default: " + v3Global.opt.prefix() + "__ALL.a\n");
        }
        of.puts("\n### Constants...\n");
        of.puts("# Perl executable (from $PERL)\n");
        of.puts("PERL = " + V3Options::getenvPERL() + "\n");
        of.puts("# Path to Verilator kit (from $VERILATOR_ROOT)\n");
        of.puts("VERILATOR_ROOT = " + V3Options::getenvVERILATOR_ROOT() + "\n");
        of.puts("# SystemC include directory with systemc.h (from $SYSTEMC_INCLUDE)\n");
        of.puts(string("SYSTEMC_INCLUDE ?= ") + V3Options::getenvSYSTEMC_INCLUDE() + "\n");
        of.puts("# SystemC library directory with libsystemc.a (from $SYSTEMC_LIBDIR)\n");
        of.puts(string("SYSTEMC_LIBDIR ?= ") + V3Options::getenvSYSTEMC_LIBDIR() + "\n");

        // Only check it if we really need the value
        if (v3Global.opt.usingSystemCLibs() && !V3Options::systemCFound()) {
            v3fatal("Need $SYSTEMC_INCLUDE in environment or when Verilator configured,\n"
                    "and need $SYSTEMC_LIBDIR in environment or when Verilator configured\n"
                    "Probably System-C isn't installed, see http://www.systemc.org\n");
        }

        of.puts("\n### Switches...\n");
        of.puts("# SystemC output mode?  0/1 (from --sc)\n");
        of.puts(string("VM_SC = ") + ((v3Global.opt.systemC()) ? "1" : "0") + "\n");
        of.puts("# Legacy or SystemC output mode?  0/1 (from --sc)\n");
        of.puts(string("VM_SP_OR_SC = $(VM_SC)\n"));
        of.puts("# Deprecated\n");
        of.puts(string("VM_PCLI = ") + (v3Global.opt.systemC() ? "0" : "1") + "\n");
        of.puts(
            "# Deprecated: SystemC architecture to find link library path (from $SYSTEMC_ARCH)\n");
        of.puts(string("VM_SC_TARGET_ARCH = ") + V3Options::getenvSYSTEMC_ARCH() + "\n");

        of.puts("\n### Vars...\n");
        of.puts("# Design prefix (from --prefix)\n");
        of.puts(string("VM_PREFIX = ") + v3Global.opt.prefix() + "\n");
        of.puts("# Module prefix (from --prefix)\n");
        of.puts(string("VM_MODPREFIX = ") + v3Global.opt.modPrefix() + "\n");

        of.puts("# User CFLAGS (from -CFLAGS on Verilator command line)\n");
        of.puts("VM_USER_CFLAGS = \\\n");
        if (!v3Global.opt.protectLib().empty()) of.puts("\t-fPIC \\\n");
        const V3StringList& cFlags = v3Global.opt.cFlags();
        for (V3StringList::const_iterator it = cFlags.begin(); it != cFlags.end(); ++it) {
            of.puts("\t" + *it + " \\\n");
        }
        of.puts("\n");

        of.puts("# User LDLIBS (from -LDFLAGS on Verilator command line)\n");
        of.puts("VM_USER_LDLIBS = \\\n");
        const V3StringList& ldLibs = v3Global.opt.ldLibs();
        for (V3StringList::const_iterator it = ldLibs.begin(); it != ldLibs.end(); ++it) {
            of.puts("\t" + *it + " \\\n");
        }
        of.puts("\n");

        V3StringSet dirs;
        of.puts("# User .cpp files (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_CLASSES = \\\n");
        const V3StringSet& cppFiles = v3Global.opt.cppFiles();
        for (V3StringSet::const_iterator it = cppFiles.begin(); it != cppFiles.end(); ++it) {
            string cppfile = *it;
            of.puts("\t" + V3Os::filenameNonExt(cppfile) + " \\\n");
            string dir = V3Os::filenameDir(cppfile);
            dirs.insert(dir);
        }
        of.puts("\n");

        of.puts("# User .cpp directories (from .cpp's on Verilator command line)\n");
        of.puts("VM_USER_DIR = \\\n");
        for (V3StringSet::iterator it = dirs.begin(); it != dirs.end(); ++it) {
            of.puts("\t" + *it + " \\\n");
        }
        of.puts("\n");

        of.puts("\n### Default rules...\n");
        of.puts("# Include list of all generated classes\n");
        of.puts("include " + v3Global.opt.prefix() + "_classes.mk\n");
        const V3HierBlockOptSet& hierOptions = v3Global.opt.hierBlocks();
        if (!v3Global.opt.hierMode() && !hierOptions.empty()) {  // Only in top module
            of.puts("# Include rules for hierarchy blocks\n");
            of.puts("include " + v3Global.opt.prefix() + "_hier.mk\n");
        }
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
                of.puts(basename + ".o: " + cppfile + "\n");
                of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -c -o $@ $<\n");
            }

            of.puts("\n### Link rules... (from --exe)\n");
            of.puts(v3Global.opt.exeName()
                    + ": $(VK_USER_OBJS) $(VK_GLOBAL_OBJS) $(VM_PREFIX)__ALL.a $(VM_HIER_LIBS)\n");
            of.puts("\t$(LINK) $(LDFLAGS) $^ $(LOADLIBES) $(LDLIBS) $(LIBS) $(SC_LIBS) -o $@\n");
            of.puts("\n");
        }

        if (!v3Global.opt.protectLib().empty()) {
            const string protectLibDeps = "$(VK_OBJS) $(VK_GLOBAL_OBJS) "
                                          + v3Global.opt.protectLib() + ".o $(VM_HIER_LIBS)";
            of.puts("\n### Library rules from --protect-lib\n");
            // The rule to create .a is defined in verilated.mk, so just define dependency here.
            of.puts(v3Global.opt.protectLibName(false) + ": " + protectLibDeps + "\n");
            of.puts("\n");
            of.puts(v3Global.opt.protectLibName(true) + ": " + protectLibDeps + "\n");
            of.puts("\t$(OBJCACHE) $(CXX) $(CXXFLAGS) $(CPPFLAGS) $(OPT_FAST) -shared -o $@ $^\n");
            of.puts("\n");

            of.puts("lib" + v3Global.opt.protectLib() + ": " + v3Global.opt.protectLibName(false)
                    + " " + v3Global.opt.protectLibName(true) + "\n");
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
class EmitMkHierVerilation {
    const V3HierBlockPlan* const m_planp;
    void emitCommonOpts(V3OutMkFile& of) const {
        const string cwd = V3Os::filenameRealPath(".");
        of.puts("# Verilation of hierarchy blocks are executed in this directory\n");
        of.puts("VM_HIER_RUN_DIR := " + cwd + "\n");
        of.puts("# Common options for hierarchy blocks\n");
        of.puts("VM_HIER_COMMON_OPTS := --cc " + v3Global.opt.allArgsStringForHierBlock(false)
                + "\n");
        of.puts("VM_HIER_TOP_OPTS := --cc " + v3Global.opt.allArgsStringForHierBlock(true) + "\n");
        of.puts("VM_HIER_VERILATOR := " + v3Global.opt.getenvVERILATOR_ROOT()
                + "/bin/verilator\n");
        of.puts("VM_HIER_INPUT_FILES := \\\n");
        const V3StringList& vFiles = v3Global.opt.vFiles();
        for (V3StringList::const_iterator it = vFiles.begin(); it != vFiles.end(); ++it) {
            of.puts("\t" + V3Os::filenameRealPath(*it) + " \\\n");
        }
        of.puts("\n");
        const V3StringSet& libraryFiles = v3Global.opt.libraryFiles();
        of.puts("VM_HIER_VERILOG_LIBS := \\\n");
        for (V3StringSet::const_iterator it = libraryFiles.begin(); it != libraryFiles.end();
             ++it) {
            of.puts("\t" + V3Os::filenameRealPath(*it) + " \\\n");
        }
        of.puts("\n");
    }
    void emitOpts(V3OutMkFile& of, const V3StringList& opts) const {
        for (V3StringList::const_iterator it = opts.begin(); it != opts.end(); ++it) {
            of.puts("\t\t" + *it + " \\\n");
        }
    }
    void emit(V3OutMkFile& of) const {
        of.puts("# Hierarchical Verilation -*- Makefile -*-\n");
        of.puts("# DESCR"
                "IPTION: Verilator output: Makefile for hierarchical verilatrion\n");
        of.puts("#\n");
        of.puts("# The main makefile " + v3Global.opt.prefix() + ".mk calls this makefile\n");
        of.puts("\n");
        of.puts("ifndef VM_HIER_VERILATION_INCLUDED\n");
        of.puts("VM_HIER_VERILATION_INCLUDED = 1\n\n");

        of.puts(".SUFFIXES:\n");
        of.puts(".PHONY: hier_build hier_verilation\n");

        of.puts("# Libraries of hierarchy blocks\n");
        of.puts("VM_HIER_LIBS := \\\n");
        for (V3HierBlockPlan::const_iterator it = m_planp->begin(); it != m_planp->end(); ++it) {
            of.puts("\t" + it->second->hierLib(true) + " \\\n");
        }
        of.puts("\n");

        // Build hierarchical libraries as soon as possible to get maximum parallelism
        of.puts("hier_build: $(VM_HIER_LIBS) " + v3Global.opt.prefix() + ".mk\n");
        of.puts("\t$(MAKE) -f " + v3Global.opt.prefix() + ".mk\n");
        of.puts("hier_verilation: " + v3Global.opt.prefix() + ".mk\n");
        emitCommonOpts(of);

        // Top level module
        {
            of.puts("\n# Verilate the top module\n");
            of.puts(v3Global.opt.prefix()
                    + ".mk: $(VM_HIER_INPUT_FILES) $(VM_HIER_VERILOG_LIBS) ");
            for (V3HierBlockPlan::const_iterator it = m_planp->begin(); it != m_planp->end();
                 ++it) {
                of.puts(it->second->hierWrapper(true) + " ");
            }
            of.puts("\n");
            of.puts("\tcd $(VM_HIER_RUN_DIR) && $(VM_HIER_VERILATOR) $(VM_HIER_TOP_OPTS) \\\n");
            // Load wrappers first not to be overwritten by the original HDL
            for (V3HierBlockPlan::const_iterator it = m_planp->begin(); it != m_planp->end();
                 ++it) {
                of.puts("\t\t" + v3Global.opt.makeDir() + "/" + it->second->hierWrapper(true)
                        + " \\\n");
            }
            of.puts("\t\t$(VM_HIER_INPUT_FILES) \\\n");
            of.puts("\t\t$(addprefix -v ,$(VM_HIER_VERILOG_LIBS)) \\\n");
            of.puts("\t\t");
            const V3StringSet& cppFiles = v3Global.opt.cppFiles();
            for (V3StringSet::const_iterator it = cppFiles.begin(); it != cppFiles.end(); ++it) {
                of.puts(*it + " ");
            }
            of.puts("\\\n");
            for (V3HierBlockPlan::const_iterator it = m_planp->begin(); it != m_planp->end();
                 ++it) {
                emitOpts(of, it->second->hierBlockOptions(false));
            }
            of.puts("\t\t--top-module " + v3Global.rootp()->topModulep()->name());
            of.puts("\t\t--prefix " + v3Global.opt.prefix() + " \\\n");
            of.puts("\t\t-Mdir " + v3Global.opt.makeDir() + " \\\n");
            of.puts("\t\t--mod-prefix " + v3Global.opt.modPrefix() + "\\");
            if (!v3Global.opt.protectLib().empty()) {
                of.puts("\n");
                of.puts("\t\t--protect-lib " + v3Global.opt.protectLib() + "\\\n");
                of.puts("\t\t--protect-key " + v3Global.opt.protectKeyDefaulted() + "\\");
            }
            of.puts("\n");
        }

        // Rules to process hierarchy blocks
        of.puts("\n# Verilate hierarchy blocks\n");
        for (V3HierBlockPlan::const_iterator it = m_planp->begin(); it != m_planp->end(); ++it) {
            const string prefix = it->second->hierPrefix();
            of.puts(it->second->hierGenerated(true));
            of.puts(": $(VM_HIER_INPUT_FILES) $(VM_HIER_VERILOG_LIBS) ");
            const V3HierBlock::HierBlockSet& children = it->second->children();
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                of.puts((*child)->hierWrapper(true) + " ");
            }
            of.puts("\n");
            of.puts("\tcd $(VM_HIER_RUN_DIR) && $(VM_HIER_VERILATOR) $(VM_HIER_COMMON_OPTS) \\\n");
            // Load wrappers first not to be overwritten by the original HDL
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                of.puts("\t\t" + v3Global.opt.makeDir() + "/" + (*child)->hierWrapper(true)
                        + " \\\n");
            }
            of.puts("\t\t$(VM_HIER_INPUT_FILES) \\\n");
            of.puts("\t\t$(addprefix -v ,$(VM_HIER_VERILOG_LIBS)) \\\n");
            emitOpts(of, it->second->commandOptions(false));
            emitOpts(of, it->second->hierBlockOptions(false));
            of.puts("\t\t-Mdir " + v3Global.opt.makeDir() + "/" + prefix + " \\\n");
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                emitOpts(of, (*child)->hierBlockOptions(false));
            }
            of.puts("\n");

            // Rule to build lib*.a
            of.puts(it->second->hierLib(true));
            of.puts(": ");
            of.puts(it->second->hierMk(true));
            of.puts(" ");
            for (V3HierBlock::HierBlockSet::const_iterator child = children.begin();
                 child != children.end(); ++child) {
                of.puts((*child)->hierLib(true));
                of.puts(" ");
            }
            of.puts("\n\t$(MAKE) -f " + it->second->hierMk(false) + " -C " + prefix);
            of.puts(" VM_PREFIX=" + prefix);
            of.puts("\n\n");
        }
        of.puts("endif  # Guard\n");
    }

public:
    explicit EmitMkHierVerilation(const V3HierBlockPlan* planp)
        : m_planp(planp) {
        V3OutMkFile of(v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + "_hier.mk");
        emit(of);
    }
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Gate class functions

void V3EmitMk::emitmk() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitMk emitter;
}

void V3EmitMk::emitHierVerilation(const V3HierBlockPlan* planp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    EmitMkHierVerilation emitter(planp);
}
