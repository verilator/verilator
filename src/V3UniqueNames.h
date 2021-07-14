// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Basic data structure to keep names unique
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
//*************************************************************************

#ifndef VERILATOR_V3UNIQUENAMES_H_
#define VERILATOR_V3UNIQUENAMES_H_
#include "config_build.h"
#include "verilatedos.h"

#include <string>
#include <unordered_map>

class V3UniqueNames final {
    std::unordered_map<std::string, unsigned> m_multiplicity;  // Suffix number for given key

public:
    // Return argument, appended with a unique suffix each time we are called with the same
    // argument.
    std::string get(const std::string& name) {
        const unsigned num = m_multiplicity.emplace(name, 0).first->second++;
        return name + "__" + cvtToStr(num);
    }
};

#endif  // Guard
