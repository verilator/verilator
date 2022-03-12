// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Basic data structure to keep names unique
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2022 by Wilson Snyder. This program is free software; you
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

#include "V3Hasher.h"

#include <string>
#include <unordered_map>

class V3UniqueNames final {
    const std::string m_prefix;  // Prefix to attach to all names

    std::unordered_map<std::string, unsigned> m_multiplicity;  // Suffix number for given key

public:
    V3UniqueNames()
        : m_prefix{""} {}
    explicit V3UniqueNames(const std::string& prefix)
        : m_prefix{prefix} {}

    // Return argument, prepended with the prefix if any, then appended with a unique suffix each
    // time we are called with the same argument.
    std::string get(const std::string& name) {
        const unsigned num = m_multiplicity.emplace(name, 0).first->second++;
        std::string result;
        if (!m_prefix.empty()) {
            result += m_prefix;
            result += "_";
        }
        result += name;
        result += "__";
        result += cvtToStr(num);
        return result;
    }

    // Return hash of node as string, prepended with the prefix if any, appended with a unique
    // suffix each time we are called with a node that hashes to the same value.
    std::string get(const AstNode* nodep) { return get(V3Hasher::uncachedHash(nodep).toString()); }

    // Reset to initial state (as if just constructed)
    void reset() { m_multiplicity.clear(); }
};

#endif  // Guard
