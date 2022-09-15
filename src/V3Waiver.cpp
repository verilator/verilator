// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit waivers into a config file
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2020-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilatedos.h"

#include "V3Waiver.h"

#include "V3File.h"

#include <memory>
#include <sstream>

void V3Waiver::addEntry(V3ErrorCode errorCode, const std::string& filename,
                        const std::string& str) {
    std::stringstream entry;
    const size_t pos = str.find('\n');
    entry << "lint_off -rule " << errorCode.ascii() << " -file \"*" << filename << "\" -match \""
          << str.substr(0, pos);
    if (pos != std::string::npos) entry << "*";
    entry << "\"";
    s_waiverList.push_back(entry.str());
}

void V3Waiver::write(const std::string& filename) {
    const std::unique_ptr<std::ofstream> ofp{V3File::new_ofstream(filename)};
    if (ofp->fail()) v3fatal("Can't write " << filename);

    *ofp << "// DESCR"
            "IPTION: Verilator output: Waivers generated with --waiver-output\n\n";

    *ofp << "`verilator_config\n\n";

    *ofp << "// Below you find suggested waivers. You have three options:\n";
    *ofp << "//   1. Fix the reason for the linter warning\n";
    *ofp << "//   2. Keep the waiver permanently if you are sure this is okay\n";
    *ofp << "//   3. Keep the waiver temporarily to suppress the output\n\n";

    if (s_waiverList.empty()) *ofp << "// No waivers needed - great!\n";

    for (const auto& i : s_waiverList) *ofp << "// " << i << "\n\n";
}

V3Waiver::WaiverList V3Waiver::s_waiverList;
