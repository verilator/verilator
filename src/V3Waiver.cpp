// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit waivers into a config file
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU Lesser
// General Public License Version 3 or the Perl Artistic License Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilatedos.h"

#include "V3File.h"
#include "V3Waiver.h"

#include <memory>
#include <sstream>

void V3Waiver::addEntry(V3ErrorCode errorCode, const std::string& filename,
                        const std::string& str) {
    std::stringstream entry;
    entry << "lint_off -rule " << errorCode.ascii() << " -file \"*" << filename << "\" -match \""
          << str << "\"";
    s_waiverList.push_back(entry.str());
}

void V3Waiver::write(const std::string& filename) {
    const std::unique_ptr<std::ofstream> ofp(V3File::new_ofstream(filename));
    if (ofp->fail()) v3fatal("Can't write " << filename);

    *ofp << "// DESCR"
            "IPTION: Verilator output: Waivers generated with --waiver-output"
         << std::endl
         << endl;

    *ofp << "`verilator_config" << endl << endl;

    *ofp << "// Below you find suggested waivers. You have three options:" << endl;
    *ofp << "//   1. Fix the reason for the linter warning" << endl;
    *ofp << "//   2. Keep the waiver permanently if you are sure this is okay" << endl;
    *ofp << "//   3. Keep the waiver temporarily to suppress the output" << endl << endl;

    if (s_waiverList.size() == 0) { *ofp << "// No waivers needed - great!" << endl; }

    for (V3Waiver::WaiverList::const_iterator it = s_waiverList.begin(); it != s_waiverList.end();
         ++it) {
        *ofp << "// " << *it << std::endl << endl;
    }
}

V3Waiver::WaiverList V3Waiver::s_waiverList;
