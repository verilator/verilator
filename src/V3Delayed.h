// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Pre C-Emit stage changes
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

#ifndef VERILATOR_V3DELAYED_H_
#define VERILATOR_V3DELAYED_H_

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;
class AstNodeExpr;
class AstVarScope;
class FileLine;

//============================================================================

class V3Delayed final {
public:
    static void delayedAll(AstNetlist* nodep) VL_MT_DISABLED;
    // New expression taking the ticket of an NBA executed now (VlNBATicket), ordering its update
    static AstNodeExpr* newTicketp(FileLine* flp) VL_MT_DISABLED;
    // The named event that the NBA region triggers if the trigger flag
    // (AstNetlist::nbaEventTriggerp) is set, both created if needed
    static AstVarScope* nbaEventp(AstNetlist* netlistp) VL_MT_DISABLED;
};

#endif  // Guard
