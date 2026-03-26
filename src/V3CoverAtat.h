// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: covergroup @@ event lowering
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3COVERATAT_H_
#define VERILATOR_V3COVERATAT_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;
class AstNode;
class AstNodeModule;

class V3CoverAtat final {
public:
    static constexpr const char* kTagBegin = "__V3CoverAtatBegin";
    static constexpr const char* kTagEnd = "__V3CoverAtatEnd";

    static void registerHook(AstNodeModule* modp, const string& target, bool begin,
                             AstNode* stmtp) VL_MT_DISABLED;
    static void coverAtat(AstNetlist* rootp) VL_MT_DISABLED;
};

#endif  // Guard
