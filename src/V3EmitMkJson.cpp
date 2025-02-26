// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Json file list
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitMkJson.h"

#include "V3EmitCBase.h"
#include "V3HierBlock.h"
#include "V3Os.h"

#include <memory>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Emit statements

class JsonEmitter final {

    // METHODS

    // STATIC FUNCTIONS

    template <typename T_List>
    static void append_source_list(const std::unique_ptr<std::ofstream>& of, const std::string& name, const T_List& sources, bool isLast = false) {
        *of << "\t\t\"" << name << "\": [\n";

        for (auto it = sources.begin(); it != sources.end(); ++it) {
            if (it == sources.begin()) {
                *of << "\t\t\t\"";
            } else {
                *of << ",\n\t\t\t\"";
            }
            *of << *it << "\"";
        }

        if (!sources.empty()) {
            *of << "\n";
        }

        *of << "\t\t]";

        if (!isLast) {
            *of << ",\n";
        }

        *of << "\n";
    }

    static void emitOverallJson() {
        const std::unique_ptr<std::ofstream> of{
            V3File::new_ofstream(v3Global.opt.makeDir() + "/" + v3Global.opt.prefix() + ".json")};
        const string name = v3Global.opt.prefix();

        *of << "{\n";

        *of << "\t\"system\": {\n";
        *of << "\t\t\"perl\": \"" << V3Options::getenvPERL() << "\",\n";
        *of << "\t\t\"python3\": \"" << V3Options::getenvPYTHON3() << "\",\n";
        *of << "\t\t\"verilator_root\": \"" << V3Options::getenvVERILATOR_ROOT() << "\",\n";
        *of << "\t\t\"verilator_solver\": \"" << V3Options::getenvVERILATOR_SOLVER() << "\"\n\t},\n\n";

        *of << "\t\"compilier\": {\n";
        *of << "\t\t\"cflags\": [";

        for (size_t i = 0; i < v3Global.opt.cFlags().size(); i++) {
            if (i != 0) {
                *of << ", ";
            }
            *of << v3Global.opt.cFlags()[i];
        }

        *of << "],\n";
        *of << "\t\t\"ldlibs\": [";

        for (size_t i = 0; i < v3Global.opt.ldLibs().size(); i++) {
            if (i != 0) {
                *of << ", ";
            }
            *of << v3Global.opt.ldLibs()[i];
        }

        *of << "]\n\t},\n\n";

        *of << "\t\"switches\": {\n";
        *of << "\t\t\"systemC\": " << (v3Global.opt.systemC() ? "true" : "false") << ",\n";
        *of << "\t\t\"coverage\": " << (v3Global.opt.coverage() ? "true" : "false") << ",\n";
        *of << "\t\t\"use_timing\": " << (v3Global.usesTiming() ? "true" : "false") << ",\n";
        *of << "\t\t\"threads\": " << v3Global.opt.threads() << ",\n";
        *of << "\t\t\"trace\": \"" << (v3Global.opt.trace() ? (v3Global.opt.traceFormat().vcd() ? "vcd" : "fst") : "off") << "\"\n\t},\n\n";

        std::vector<string> classesFast;
        std::vector<string> classesSlow;
        std::vector<string> supportFast;
        std::vector<string> supportSlow;
        std::vector<string> global;
        for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
             nodep = VN_AS(nodep->nextp(), NodeFile)) {
            const AstCFile* const cfilep = VN_CAST(nodep, CFile);
            if (cfilep && cfilep->source()) {
                if (cfilep->support()) {
                    if (cfilep->slow()) {
                        supportSlow.push_back(cfilep->name());
                    } else {
                        supportFast.push_back(cfilep->name());
                    }
                } else {
                    if (cfilep->slow()) {
                        classesSlow.push_back(cfilep->name());
                    } else {
                        classesFast.push_back(cfilep->name());
                    }
                }
            }
        }

        global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated.cpp");
        if (v3Global.dpi()) {  //
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_dpi.cpp");
        }
        if (v3Global.opt.vpi()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_vpi.cpp");
        }
        if (v3Global.opt.savable()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_save.cpp");
        }
        if (v3Global.opt.coverage()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_cov.cpp");
        }
        if (v3Global.opt.trace()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/" + v3Global.opt.traceSourceBase()
                                + "_c.cpp");
        }
        if (v3Global.usesProbDist()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_probdist.cpp");
        }
        if (v3Global.usesTiming()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_timing.cpp");
        }
        if (v3Global.useRandomizeMethods()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_random.cpp");
        }
        global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_threads.cpp");
        if (v3Global.opt.usesProfiler()) {
            global.emplace_back(V3Options::getenvVERILATOR_ROOT() + "/include/verilated_profiler.cpp");
        }
        if (!v3Global.opt.libCreate().empty()) {
            global.emplace_back(v3Global.opt.makeDir() + "/" + v3Global.opt.libCreate() + ".cpp");
        }

        *of << "\t\"sources\": {\n";

        append_source_list(of, "global", global);

        append_source_list(of, "classes_slow", classesSlow);

        append_source_list(of, "classes_fast", classesFast);

        append_source_list(of, "support_slow", supportSlow);

        append_source_list(of, "support_fast", supportFast);

        append_source_list(of, "deps", V3File::getAllDeps());

        append_source_list(of, "user_classes", v3Global.opt.cppFiles(), true);

        *of << "\t}\n";

        *of << "}\n";

        if (const V3HierBlockPlan* const planp = v3Global.hierPlanp()) {
            *of << "# Verilate hierarchical blocks\n";
            // Sorted hierarchical blocks in order of leaf-first.
            const V3HierBlockPlan::HierVector& hierBlocks = planp->hierBlocksSorted();
            *of << "get_target_property(TOP_TARGET_NAME \"${TARGET}\" NAME)\n";
            for (V3HierBlockPlan::HierVector::const_iterator it = hierBlocks.begin();
                 it != hierBlocks.end(); ++it) {
                const V3HierBlock* hblockp = *it;
                const V3HierBlock::HierBlockSet& children = hblockp->children();
                const string prefix = hblockp->hierPrefix();
                *of << "add_library(" << prefix << " STATIC)\n";
                *of << "target_link_libraries(${TOP_TARGET_NAME}  PRIVATE " << prefix << ")\n";
                if (!children.empty()) {
                    *of << "target_link_libraries(" << prefix << " INTERFACE";
                    for (const auto& childr : children) *of << " " << (childr)->hierPrefix();
                    *of << ")\n";
                }
                *of << "verilate(" << prefix << " PREFIX " << prefix << " TOP_MODULE "
                    << hblockp->modp()->name() << " DIRECTORY "
                    << v3Global.opt.makeDir() + "/" + prefix << " SOURCES ";
                for (const auto& childr : children) {
                    *of << " " << v3Global.opt.makeDir() + "/" + childr->hierWrapperFilename(true);
                }
                *of << " ";
                const string vFile = hblockp->vFileIfNecessary();
                if (!vFile.empty()) *of << vFile << " ";
                const V3StringList& vFiles = v3Global.opt.vFiles();
                for (const string& i : vFiles) *of << V3Os::filenameRealPath(i) << " ";
                *of << " VERILATOR_ARGS ";
                *of << "-f " << hblockp->commandArgsFilename(true)
                    << " -CFLAGS -fPIC"  // hierarchical block will be static, but may be linked
                                         // with .so
                    << ")\n";
            }
            *of << "\n# Verilate the top module that refers to lib-create wrappers of above\n";
            *of << "verilate(${TOP_TARGET_NAME} PREFIX " << v3Global.opt.prefix() << " TOP_MODULE "
                << v3Global.rootp()->topModulep()->name() << " DIRECTORY "
                << v3Global.opt.makeDir() << " SOURCES ";
            for (const auto& itr : *planp) {
                *of << " " << v3Global.opt.makeDir() + "/" + itr.second->hierWrapperFilename(true);
            }
            //*of << " " << Json_list(v3Global.opt.vFiles());
            *of << " VERILATOR_ARGS ";
            *of << "-f " << planp->topCommandArgsFilename(true);
            *of << ")\n";
        }
    }

public:
    explicit JsonEmitter() { emitOverallJson(); }
    virtual ~JsonEmitter() = default;
};

void V3EmitMkJson::emit() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    const JsonEmitter emitter;
}
