// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Temporary variables shared between instances
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Creates temporary variables in scopes, such that the scopes of the same
// module (instances) use the same AstVar declarations, each with their own
// AstVarScope. Without this, identical instances would reference different
// variables, which prevents V3Combine from sharing their logic.
//
// Variables are named '<prefix>_<name>_<n>', with the prefix given to the
// constructor, which must start with '__V', and must be unique among all
// instances created during the run, so names never clash.
//
// Variables are requested with a name and a data type. The n-th request with
// the same name and type from each scope of a module yields the same AstVar,
// so sharing works if all scopes of a module request their temporaries in the
// same order, which holds as they contain the same code. A scope never gets
// the same AstVar twice. As the AstVar is shared, callers must set identical
// AstVar attributes on all variables created with the same name. Data types
// are compared by identity, so callers must pass shared (e.g. type table) data
// types, not ones created anew for each scope, otherwise no variables are
// shared.
//
//*************************************************************************

#ifndef VERILATOR_V3SHAREDTMPS_H_
#define VERILATOR_V3SHAREDTMPS_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Hash.h"
#include "V3HashTable.h"
#include "V3String.h"

#include <set>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

class V3SharedTmps final {
    // TYPES
    // Temporaries are identified by their module, name and data type
    struct Key final {
        const AstNodeModule* m_modp;  // The module of the scopes
        std::string m_name;  // Name of the temporary
        const AstNodeDType* m_dtypep;  // Data type of the temporary
    };
    // Hash and equality of Keys, which can be looked up by their parts, without making one
    struct KeyHash final {
        size_t operator()(const AstNodeModule* modp, const std::string& name,
                          const AstNodeDType* dtypep) const {
            V3Hash hash{modp};
            hash += name;
            hash += dtypep;
            return hash.value();
        }
        size_t operator()(const Key& key) const {
            return (*this)(key.m_modp, key.m_name, key.m_dtypep);
        }
    };
    struct KeyEqual final {
        bool operator()(const Key& key, const AstNodeModule* modp, const std::string& name,
                        const AstNodeDType* dtypep) const {
            return key.m_modp == modp && key.m_dtypep == dtypep && key.m_name == name;
        }
        bool operator()(const Key& a, const Key& b) const {
            return (*this)(a, b.m_modp, b.m_name, b.m_dtypep);
        }
    };
    struct Tmps final {
        std::vector<AstVar*> m_varps;  // Variables created so far
        // Number of variables used by each scope
        std::unordered_map<const AstScope*, size_t> m_nUsed;
    };

    // STATE
    const std::string m_prefix;  // Prefix of all variable names
    const VVarType m_varType;  // Type of all variables
    V3HashMap<Key, Tmps, KeyHash, KeyEqual> m_tmps;  // The temporaries created so far
    size_t m_nVars = 0;  // Number of variables created, used to make unique names
    size_t m_nReused = 0;  // Number of temporaries using an existing variable

public:
    // CONSTRUCTORS
    V3SharedTmps(const std::string& prefix, VVarType varType)
        : m_prefix{prefix}
        , m_varType{varType} {
        UASSERT(VString::startsWith(prefix, "__V"), "Prefix must start with '__V'");
        UASSERT(!VString::endsWith(prefix, "_"), "Prefix must not end with '_'");
        // Prefixes used so far during the whole of compilation. Must be unique.
        static std::set<std::string> s_prefixes;
        const bool isNew = s_prefixes.insert(m_prefix).second;
        UASSERT(isNew, "V3SharedTmps prefix is not unique: '" << prefix << "'");
    }

    // METHODS
    // Create a new temporary of type 'dtypep' in 'scopep', and return its AstVarScope
    AstVarScope* make(FileLine* flp, AstScope* scopep, AstNodeDType* dtypep,
                      const std::string& name = "") {
        const AstNodeModule* const modp = scopep->modp();
        const auto pair = m_tmps.insertLazy(modp, name, dtypep, [&]() {  //
            return std::make_pair(Key{modp, name, dtypep}, Tmps{});
        });
        Tmps& tmps = pair.first.value();
        const size_t n = tmps.m_nUsed[scopep]++;
        if (n < tmps.m_varps.size()) {
            ++m_nReused;
        } else {
            std::string uniqueName = m_prefix + "_";
            if (!name.empty()) uniqueName += name + "_";
            uniqueName += std::to_string(m_nVars++);
            AstVar* const varp = new AstVar{flp, m_varType, uniqueName, dtypep};
            scopep->modp()->addStmtsp(varp);
            tmps.m_varps.emplace_back(varp);
        }
        AstVarScope* const vscp = new AstVarScope{flp, scopep, tmps.m_varps[n]};
        scopep->addVarsp(vscp);
        return vscp;
    }
    // Same as above, but with a 2-state unsigned packed type of the given 'width'
    AstVarScope* make(FileLine* flp, AstScope* scopep, unsigned width,
                      const std::string& name = "") {
        return make(flp, scopep, scopep->findBitDType(width, width, VSigning::UNSIGNED), name);
    }

    // Number of temporaries using an existing variable
    size_t nReused() const { return m_nReused; }
};

#endif  // Guard
