// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Emit Waivers
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3WAIVER_H_
#define VERILATOR_V3WAIVER_H_

#include "V3Error.h"
#include "V3Mutex.h"

#include <string>
#include <vector>

class V3Waiver final {
    // TYPES
    using WaiverList = std::vector<std::string>;
    static V3Mutex s_mutex;  // Protect members
    static WaiverList s_waiverList VL_GUARDED_BY(s_mutex);

public:
    static void addEntry(V3ErrorCode errorCode, const string& filename, const std::string& str)
        VL_MT_SAFE_EXCLUDES(s_mutex);
    static void write(const std::string& filename) VL_MT_SAFE_EXCLUDES(s_mutex);
};

#endif  // Guard
