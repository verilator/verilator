// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit CMake file list
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
#include "V3EmitCMake.h"
#include "V3EmitCBase.h"

#include <memory>

//######################################################################
// Emit statements

class CMakeEmitter {

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // STATIC FUNCTIONS

    // Concatenate all strings in 'strs' with ' ' between them.
    template<typename List>
    static string cmake_list(const List& strs) {
        string s;
        if (strs.begin() != strs.end()) {
            s.append("\"");
            s.append(*strs.begin());
            s.append("\"");
            for (typename List::const_iterator it = ++strs.begin(); it != strs.end(); ++it) {
                s.append(" \"");
                s.append(*it);
                s.append("\"");
            }
        }
        return s;
    }

    // Print CMake variable set command: output raw_value unmodified
    // cache_type should be empty for a normal variable
    // "BOOL", "FILEPATH", "PATH", "STRING" or "INTERNAL" for a CACHE variable
    // See https://cmake.org/cmake/help/latest/command/set.html
    static void cmake_set_raw(std::ofstream& of, const string& name, const string& raw_value,
                            const string& cache_type = "", const string& docstring = "") {
        of << "set(" << name << " " << raw_value;
        if (!cache_type.empty()) {
            of << " CACHE " << cache_type << " \"" << docstring << "\"";
        }
        of << ")\n";
    }

    static void cmake_set(std::ofstream& of, const string& name, const string& value,
                            const string& cache_type = "", const string& docstring = "") {
        string raw_value = "\"" + value + "\"";
        cmake_set_raw(of, name, raw_value, cache_type, docstring);
    }

    //Swap all backslashes for forward slashes, because of Windows
    static string deslash(const string& s) {
        std::string res = s;
        for (string::iterator it = res.begin(); it != res.end(); ++it) {
            if (*it == '\\')
                *it = '/';
        }
        return res;
    }

    static void emitOverallCMake() {
        const vl_unique_ptr<std::ofstream>
            of (V3File::new_ofstream(v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+".cmake"));
        string name = v3Global.opt.prefix();

        *of << "# Verilated -*- CMake -*-\n";
        *of << "# DESCR" "IPTION: Verilator output: CMake include script with class lists\n";
        *of << "#\n";
        *of << "# This CMake script lists generated Verilated files, for including in higher level CMake scripts.\n";
        *of << "# This file is meant to be consumed by the verilate() function,\n";
        *of << "# which becomes available after executing `find_package(verilator).\n";

        *of << "\n### Constants...\n";
        cmake_set(*of, "PERL", deslash(V3Options::getenvPERL()),
                  "FILEPATH", "Perl executable (from $PERL)");
        cmake_set(*of, "VERILATOR_ROOT", deslash(V3Options::getenvVERILATOR_ROOT()),
                  "PATH", "Path to Verilator kit (from $VERILATOR_ROOT)");

        *of << "\n### Compiler flags...\n";

        *of << "# User CFLAGS (from -CFLAGS on Verilator command line)\n";
        cmake_set_raw(*of, name + "_USER_CFLAGS", cmake_list(v3Global.opt.cFlags()));

        *of << "# User LDLIBS (from -LDFLAGS on Verilator command line)\n";
        cmake_set_raw(*of, name + "_USER_LDLIBS", cmake_list(v3Global.opt.ldLibs()));

        *of << "\n### Switches...\n";

        *of << "# SystemC output mode?  0/1 (from --sc)\n";
        cmake_set_raw(*of, name + "_SC", v3Global.opt.systemC() ? "1" : "0");
        *of << "# Coverage output mode?  0/1 (from --coverage)\n";
        cmake_set_raw(*of, name + "_COVERAGE", v3Global.opt.coverage()?"1":"0");
        *of << "# Threaded output mode?  0/1/N threads (from --threads)\n";
        cmake_set_raw(*of, name + "_THREADS", cvtToStr(v3Global.opt.threads()));
        *of << "# VCD Tracing output mode?  0/1 (from --trace)\n";
        cmake_set_raw(*of, name + "_TRACE_VCD", (v3Global.opt.trace() && (v3Global.opt.traceFormat() == TraceFormat::VCD))?"1":"0");
        *of << "# FST Tracing output mode? 0/1 (from --fst-trace)\n";
        cmake_set_raw(*of, name + "_TRACE_FST", (v3Global.opt.trace() && (v3Global.opt.traceFormat() != TraceFormat::VCD)) ? "1":"0");

        *of << "\n### Sources...\n";
        std::vector<string> classes_fast, classes_slow, support_fast, support_slow, global;
        for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
             nodep = VN_CAST(nodep->nextp(), NodeFile)) {
            AstCFile* cfilep = VN_CAST(nodep, CFile);
            if (cfilep && cfilep->source()) {
                if (cfilep->support()) {
                    if (cfilep->slow()) {
                        support_slow.push_back(cfilep->name());
                    } else {
                        support_fast.push_back(cfilep->name());
                    }
                } else {
                    if (cfilep->slow()) {
                        classes_slow.push_back(cfilep->name());
                    } else {
                        classes_fast.push_back(cfilep->name());
                    }
                }
            }
        }

        global.push_back("${VERILATOR_ROOT}/include/verilated.cpp");
        if (v3Global.dpi()) {
            global.push_back("${VERILATOR_ROOT}/include/verilated_dpi.cpp");
        }
        if (v3Global.opt.vpi()) {
            global.push_back("${VERILATOR_ROOT}/include/verilated_vpi.cpp");
        }
        if (v3Global.opt.savable()) {
            global.push_back("${VERILATOR_ROOT}/include/verilated_save.cpp");
        }
        if (v3Global.opt.coverage()) {
            global.push_back("${VERILATOR_ROOT}/include/verilated_cov.cpp");
        }
        if (v3Global.opt.trace()) {
            global.push_back("${VERILATOR_ROOT}/include/"
                             + v3Global.opt.traceSourceBase() + "_c.cpp");
            if (v3Global.opt.systemC()) {
                if (v3Global.opt.traceFormat() != TraceFormat::VCD) {
                    v3error("Unsupported: This trace format is not supported in SystemC, use VCD format.");
                }
                global.push_back("${VERILATOR_ROOT}/include/"
                                    + v3Global.opt.traceSourceLang() + ".cpp");
            }
        }
        if (v3Global.opt.mtasks()) {
            global.push_back("${VERILATOR_ROOT}/include/verilated_threads.cpp");
        }
        if (!v3Global.opt.protectLib().empty()) {
            global.push_back(v3Global.opt.makeDir()+"/"+v3Global.opt.protectLib()+".cpp");
        }

        *of << "# Global classes, need linked once per executable\n";
        cmake_set_raw(*of, name + "_GLOBAL", deslash(cmake_list(global)));
        *of << "# Generated module classes, non-fast-path, compile with low/medium optimization\n";
        cmake_set_raw(*of, name + "_CLASSES_SLOW", deslash(cmake_list(classes_slow)));
        *of << "# Generated module classes, fast-path, compile with highest optimization\n";
        cmake_set_raw(*of, name + "_CLASSES_FAST", deslash(cmake_list(classes_fast)));
        *of << "# Generated support classes, non-fast-path, compile with low/medium optimization\n";
        cmake_set_raw(*of, name + "_SUPPORT_SLOW", deslash(cmake_list(support_slow)));
        *of << "# Generated support classes, fast-path, compile with highest optimization\n";
        cmake_set_raw(*of, name + "_SUPPORT_FAST", deslash(cmake_list(support_fast)));

        *of << "# All dependencies\n";
        cmake_set_raw(*of, name + "_DEPS", deslash(cmake_list(V3File::getAllDeps())));

        *of << "# User .cpp files (from .cpp's on Verilator command line)\n";
        cmake_set_raw(*of, name + "_USER_CLASSES", deslash(cmake_list(v3Global.opt.cppFiles())));
    }
public:
    explicit CMakeEmitter() {
        emitOverallCMake();
    }
    virtual ~CMakeEmitter() {}
};

void V3EmitCMake::emit() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CMakeEmitter emitter;
}
