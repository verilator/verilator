// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit waivers into a config file
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2020-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilatedos.h"

#include "V3Waiver.h"

#include "V3File.h"
#include "V3Global.h"
#include "V3Options.h"

#include <memory>
#include <sstream>

void V3Waiver::addEntry(V3ErrorCode errorCode, const std::string& filename, const std::string& msg)
    VL_MT_SAFE_EXCLUDES(s_mutex) {
    if (filename == V3Options::getStdPackagePath()) return;
    const V3LockGuard lock{s_mutex};

    string trimmsg = msg;
    if (!v3Global.opt.waiverMultiline()) {
        const size_t pos = trimmsg.find('\n');
        trimmsg = trimmsg.substr(0, pos);
        if (pos != std::string::npos) trimmsg += '*';
    }
    {  // Remove line numbers and context "\n [0-9] | ", "\n  ^[~]+"
        string result;
        for (const char* cp = trimmsg.c_str(); *cp; cp = *cp ? cp + 1 : cp) {
            while (*cp == ' ' || isdigit(*cp)) ++cp;
            if (*cp == '|') ++cp;
            // ^~~~~
            while (*cp == ' ' || *cp == '^') ++cp;
            while (*cp == '~') ++cp;
            while (*cp && *cp != '\n') result += *cp++;
            while (*cp == '\n') result += *cp++;
        }
        trimmsg = result;
    }
    trimmsg += '*';
    {  // "\n"->"*", " *"->"*", "* "->"*"
        string result;
        string add;
        result.reserve(trimmsg.size());
        for (const char& c : trimmsg) {
            if (c == '*' || !std::isprint(c)) {
                add = "*";
            } else if (c == ' ') {
                if (add != "*") add += c;
            } else {
                result += add + c;
                add = "";
            }
        }
        result += add;
        trimmsg = result;
    }

    std::stringstream entry;
    entry << "lint_off -rule " << errorCode.ascii() << " -file \"*" << filename << "\" -match \""
          << trimmsg << "\"";
    s_waiverList.push_back(entry.str());
}

void V3Waiver::write(const std::string& filename) VL_MT_SAFE_EXCLUDES(s_mutex) {
    const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
    if (ofp->fail()) v3fatal("Can't write " << filename);

    *ofp << "// DESCR"
            "IPTION: Verilator output: Waivers generated with --waiver-output\n\n";

    *ofp << "`verilator_config\n\n";

    *ofp << "// Below are suggested waivers. You have three options:\n";
    *ofp << "//   1. Fix the reason for the linter warning in the Verilog sources\n";
    *ofp << "//   2. Keep the waiver permanently if you are sure it is okay\n";
    *ofp << "//   3. Keep the waiver temporarily to suppress the output\n\n";

    const V3LockGuard lock{s_mutex};

    if (s_waiverList.empty()) *ofp << "// No waivers needed - great!\n";

    for (const auto& i : s_waiverList) *ofp << "// " << i << "\n\n";
}

V3Mutex V3Waiver::s_mutex;
V3Waiver::WaiverList V3Waiver::s_waiverList;
