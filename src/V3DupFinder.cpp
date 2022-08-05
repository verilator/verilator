// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Hashed common code into functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3DupFinder.h"

#include "V3Ast.h"
#include "V3File.h"
#include "V3Global.h"

#include <algorithm>
#include <iomanip>
#include <map>
#include <memory>

//######################################################################
// V3DupFinder class functions

V3DupFinder::size_type V3DupFinder::erase(AstNode* nodep) {
    const auto& er = equal_range(m_hasher(nodep));
    for (iterator it = er.first; it != er.second; ++it) {
        if (nodep == it->second) {
            erase(it);
            return 1;
        }
    }
    return 0;
}

V3DupFinder::iterator V3DupFinder::findDuplicate(AstNode* nodep, V3DupFinderUserSame* checkp) {
    const auto& er = equal_range(m_hasher(nodep));
    for (iterator it = er.first; it != er.second; ++it) {
        AstNode* const node2p = it->second;
        if (nodep == node2p) continue;  // Same node is not a duplicate
        if (checkp && !checkp->isSame(nodep, node2p)) continue;  // User says it is not a duplicate
        if (!nodep->sameTree(node2p)) continue;  // Not the same trees
        // Found duplicate
        return it;
    }
    return end();
}

void V3DupFinder::dumpFile(const string& filename, bool tree) {
    const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
    if (logp->fail()) v3fatal("Can't write " << filename);

    std::unordered_map<int, int> dist;

    V3Hash lasthash;
    int num_in_bucket = 0;
    for (auto it = cbegin(); true; ++it) {
        if (it == cend() || lasthash != it->first) {
            if (it != cend()) lasthash = it->first;
            if (num_in_bucket) {
                if (dist.find(num_in_bucket) == dist.end()) {
                    dist.emplace(num_in_bucket, 1);
                } else {
                    ++dist[num_in_bucket];
                }
            }
            num_in_bucket = 0;
        }
        if (it == cend()) break;
        num_in_bucket++;
    }
    *logp << "\n*** STATS:\n\n";
    *logp << "    #InBucket   Occurrences\n";
    for (const auto& i : dist) {
        *logp << "    " << std::setw(9) << i.first << "  " << std::setw(12) << i.second << '\n';
    }

    *logp << "\n*** Dump:\n\n";
    for (const auto& it : *this) {
        if (lasthash != it.first) {
            lasthash = it.first;
            *logp << "    " << it.first << '\n';
        }
        *logp << "\t" << it.second << '\n';
        // Dumping the entire tree may make nearly N^2 sized dumps,
        // because the nodes under this one may also be in the hash table!
        if (tree) it.second->dumpTree(*logp, "    ");
    }
}

void V3DupFinder::dumpFilePrefixed(const string& nameComment, bool tree) {
    if (v3Global.opt.dumpTree()) {  //
        dumpFile(v3Global.debugFilename(nameComment) + ".hash", tree);
    }
}
