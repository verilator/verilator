// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Basic data structure to keep names unique
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2024 by Wilson Snyder. This program is free software; you
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

#include <map>
#include <string>

class V3UniqueNames final {
    const std::string m_prefix;  // Prefix to attach to all names

    std::map<std::string, unsigned> m_multiplicity;  // Suffix number for given key

    const bool m_addSuffix = true;  // Ad suffix or not

public:
    V3UniqueNames() = default;
    explicit V3UniqueNames(const std::string& prefix, bool addSuffix = true)
        : m_prefix{prefix}
        , m_addSuffix(addSuffix) {
        if (!m_prefix.empty()) {
            UASSERT(VString::startsWith(m_prefix, "__V"), "Prefix must start with '__V'");
            UASSERT(!VString::endsWith(m_prefix, "_"), "Prefix must not end with '_'");
        }
    }

    // Return argument, prepended with the prefix if any, then appended with a unique suffix each
    // time we are called with the same argument.
    std::string get(const std::string& name) {
        if (!m_addSuffix) {
            if (m_multiplicity.count(name) == 0) {
                m_multiplicity[name] = 0;
                return name;
            } else {
                return get(name + "__" + cvtToStr(m_multiplicity[name]++));
            }
        }
        // NORMAL mode
        const unsigned num = m_multiplicity[name]++;
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
