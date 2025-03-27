// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit JSON manifest file
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

class V3EmitMkJsonEmitter final {
    class Printer final {
        // MEMBERS
    private:
        const std::unique_ptr<std::ofstream>& m_of;
        std::stack<char>
            m_scope;  // Stack of ']' and '}' to be used to close currently open scopes
        std::string m_prefix;  // Prefix emitted before each line in the current scope (indent *
                               // scope depth)
        std::string m_indent;  // Single indent
        bool m_empty = true;  // Indicates that the current scope is empty

        // METHODS
    public:
        explicit Printer(const std::unique_ptr<std::ofstream>& of,
                         const std::string& indent = "    ")
            : m_of(of)
            , m_indent(indent) {
            begin();
        }

        ~Printer() { end(); }

        Printer& begin(const std::string& name, char type = '{') {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << "\"" << name << "\": " << type << "\n";
            m_prefix += m_indent;
            m_scope.push(type == '{' ? '}' : ']');
            m_empty = true;
            return *this;
        }

        Printer& put(const std::string& name, const std::string& value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << "\"" << name << "\": \"" << value << "\"";
            m_empty = false;
            return *this;
        }

        Printer& put(const std::string& name, bool value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << "\"" << name << "\": " << (value ? "true" : "false");
            m_empty = false;
            return *this;
        }

        Printer& put(const std::string& name, int value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << "\"" << name << "\": " << value;
            m_empty = false;
            return *this;
        }

        Printer& begin(char type = '{') {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << type << "\n";
            m_prefix += m_indent;
            m_scope.push(type == '{' ? '}' : ']');
            m_empty = true;
            return *this;
        }

        Printer& put(const std::string& value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << "\"" << value << "\"";
            m_empty = false;
            return *this;
        }

        Printer& put(bool value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << (value ? "true" : "false");
            m_empty = false;
            return *this;
        }

        Printer& put(int value) {
            if (!m_empty) *m_of << ",\n";
            *m_of << m_prefix << value;
            m_empty = false;
            return *this;
        }

        template <typename T>
        Printer& putList(const std::string& name, const T& list) {
            if (list.empty()) return *this;
            begin(name, '[');
            for (auto it = list.begin(); it != list.end(); ++it) put(*it);
            return end();
        }

        Printer& end() {
            assert(m_prefix.length() >= m_indent.length());
            m_prefix.erase(m_prefix.end() - m_indent.length(), m_prefix.end());
            assert(!m_scope.empty());
            *m_of << "\n" << m_prefix << m_scope.top();
            m_scope.pop();
            return *this;
        }

        Printer& operator+=(Printer& cursor) {
            // Meaningless syntax sugar, at least for now
            return *this;
        }
    };

    // METHODS

    // STATIC FUNCTIONS
    static void emitManifest() {
        const std::string makeDir
            = V3Os::filenameSlashPath(V3Os::filenameRealPath(v3Global.opt.makeDir()));

        const std::unique_ptr<std::ofstream> of{
            V3File::new_ofstream(makeDir + "/" + v3Global.opt.prefix() + ".json")};

        const std::string trace
            = v3Global.opt.trace() ? (v3Global.opt.traceFormat().vcd() ? "vcd" : "fst") : "off";

        std::vector<string> classesFast;
        std::vector<string> classesSlow;
        std::vector<string> supportFast;
        std::vector<string> supportSlow;
        std::vector<string> global;
        std::vector<string> deps;
        std::vector<string> cppFiles;

        for (AstNodeFile* nodep = v3Global.rootp()->filesp(); nodep;
             nodep = VN_AS(nodep->nextp(), NodeFile)) {
            const AstCFile* const cfilep = VN_CAST(nodep, CFile);
            if (cfilep && cfilep->source()) {
                const std::string filename
                    = V3Os::filenameSlashPath(V3Os::filenameRealPath(cfilep->name()));
                if (cfilep->support()) {
                    if (cfilep->slow()) {
                        supportSlow.emplace_back(filename);
                    } else {
                        supportFast.emplace_back(filename);
                    }
                } else {
                    if (cfilep->slow()) {
                        classesSlow.emplace_back(filename);
                    } else {
                        classesFast.emplace_back(filename);
                    }
                }
            }
        }

        const std::string verilatorRoot
            = V3Os::filenameSlashPath(V3Os::filenameRealPath(V3Options::getenvVERILATOR_ROOT()));
        global.emplace_back(verilatorRoot + "/include/verilated.cpp");
        if (v3Global.dpi()) {  //
            global.emplace_back(verilatorRoot + "/include/verilated_dpi.cpp");
        }
        if (v3Global.opt.vpi()) {
            global.emplace_back(verilatorRoot + "/include/verilated_vpi.cpp");
        }
        if (v3Global.opt.savable()) {
            global.emplace_back(verilatorRoot + "/include/verilated_save.cpp");
        }
        if (v3Global.opt.coverage()) {
            global.emplace_back(verilatorRoot + "/include/verilated_cov.cpp");
        }
        if (v3Global.opt.trace()) {
            global.emplace_back(verilatorRoot + "/include/" + v3Global.opt.traceSourceBase()
                                + "_c.cpp");
        }
        if (v3Global.usesProbDist()) {
            global.emplace_back(verilatorRoot + "/include/verilated_probdist.cpp");
        }
        if (v3Global.usesTiming()) {
            global.emplace_back(verilatorRoot + "/include/verilated_timing.cpp");
        }
        if (v3Global.useRandomizeMethods()) {
            global.emplace_back(verilatorRoot + "/include/verilated_random.cpp");
        }
        global.emplace_back(verilatorRoot + "/include/verilated_threads.cpp");
        if (v3Global.opt.usesProfiler()) {
            global.emplace_back(verilatorRoot + "/include/verilated_profiler.cpp");
        }
        if (!v3Global.opt.libCreate().empty()) {
            global.emplace_back(makeDir + "/" + v3Global.opt.libCreate() + ".cpp");
        }

        for (const auto& dep : V3File::getAllDeps())
            deps.emplace_back(V3Os::filenameSlashPath(V3Os::filenameRealPath(dep)));
        for (const auto& cppFile : v3Global.opt.cppFiles())
            cppFiles.emplace_back(V3Os::filenameSlashPath(V3Os::filenameRealPath(cppFile)));

        Printer manifest(of);
        Printer& cursor = manifest.put("version", 1)
                              .begin("system")
                              .put("perl", V3Options::getenvPERL())
                              .put("python3", V3Options::getenvPYTHON3())
                              .put("verilator_root", verilatorRoot)
                              .put("verilator_solver", V3Options::getenvVERILATOR_SOLVER())
                              .end()
                              .begin("options")
                              .putList("cflags", v3Global.opt.cFlags())
                              .putList("ldflags", v3Global.opt.ldLibs())
                              .put("system_c", v3Global.opt.systemC())
                              .put("coverage", v3Global.opt.coverage())
                              .put("use_timing", v3Global.usesTiming())
                              .put("threads", v3Global.opt.threads())
                              .put("trace", trace)
                              .end()
                              .begin("sources")
                              .putList("global", global)
                              .putList("classes_slow", classesSlow)
                              .putList("classes_fast", classesFast)
                              .putList("support_slow", supportSlow)
                              .putList("support_fast", supportFast)
                              .putList("deps", deps)
                              .putList("user_classes", cppFiles)
                              .end();

        if (const V3HierBlockPlan* const planp = v3Global.hierPlanp()) {
            // Sorted hierarchical blocks in order of leaf-first.
            const V3HierBlockPlan::HierVector& hierBlocks = planp->hierBlocksSorted();

            cursor += cursor.begin("submodules", '[');

            for (V3HierBlockPlan::HierVector::const_iterator it = hierBlocks.begin();
                 it != hierBlocks.end(); ++it) {
                const V3HierBlock* hblockp = *it;
                const V3HierBlock::HierBlockSet& children = hblockp->children();

                std::vector<std::string> childDeps;
                std::vector<std::string> sources;

                for (const auto& childr : children) {
                    childDeps.emplace_back((childr)->hierPrefix());
                    sources.emplace_back(makeDir + "/" + childr->hierWrapperFilename(true));
                }

                const string vFile = hblockp->vFileIfNecessary();
                if (!vFile.empty()) sources.emplace_back(vFile);

                const V3StringList& vFiles = v3Global.opt.vFiles();
                for (const string& i : vFiles)
                    sources.emplace_back(V3Os::filenameSlashPath(V3Os::filenameRealPath(i)));

                std::vector<std::string> cflags;
                cflags.emplace_back("-fPIC");

                cursor += cursor.begin()
                              .put("prefix", hblockp->hierPrefix())
                              .put("top", hblockp->modp()->name())
                              .putList("deps", childDeps)
                              .put("directory", makeDir + "/" + hblockp->hierPrefix())
                              .putList("sources", sources)
                              .putList("cflags", cflags)
                              .put("verilator_args",
                                   V3Os::filenameSlashPath(
                                       V3Os::filenameRealPath(hblockp->commandArgsFilename(true))))
                              .end();
            }

            std::vector<std::string> sources;
            for (const auto& itr : *planp)
                sources.emplace_back(makeDir + "/" + itr.second->hierWrapperFilename(true));

            const V3StringList& vFiles = v3Global.opt.vFiles();
            for (const string& i : vFiles)
                sources.emplace_back(V3Os::filenameSlashPath(V3Os::filenameRealPath(i)));

            cursor += cursor.begin()
                          .put("prefix", v3Global.opt.prefix())
                          .put("top", v3Global.rootp()->topModulep()->name())
                          .put("directory", makeDir)
                          .putList("sources", sources)
                          .put("verilator_args", V3Os::filenameSlashPath(V3Os::filenameRealPath(
                                                     planp->topCommandArgsFilename(true))))
                          .end()
                          .end();
        }
    }

public:
    explicit V3EmitMkJsonEmitter() { emitManifest(); }
    virtual ~V3EmitMkJsonEmitter() = default;
};

void V3EmitMkJson::emit() {
    UINFO(2, __FUNCTION__ << ": " << endl);
    const V3EmitMkJsonEmitter emitter;
}
