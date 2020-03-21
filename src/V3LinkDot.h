// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link XREF signals/functions together
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3LINKDOT_H_
#define _V3LINKDOT_H_ 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

enum VLinkDotStep { LDS_PRIMARY, LDS_PARAMED, LDS_ARRAYED, LDS_SCOPED };

class V3LinkDot {
private:
    static int debug();
    static void linkDotGuts(AstNetlist* rootp, VLinkDotStep step);
public:
    static void linkDotPrimary(AstNetlist* nodep) {
        UINFO(2,__FUNCTION__<<": "<<endl);
        linkDotGuts(nodep,LDS_PRIMARY);
        V3Global::dumpCheckGlobalTree("linkdot", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    }
    static void linkDotParamed(AstNetlist* nodep) {
        UINFO(2,__FUNCTION__<<": "<<endl);
        linkDotGuts(nodep,LDS_PARAMED);
        V3Global::dumpCheckGlobalTree("paramlink", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
    static void linkDotArrayed(AstNetlist* nodep) {
        UINFO(2,__FUNCTION__<<": "<<endl);
        linkDotGuts(nodep,LDS_ARRAYED);
        V3Global::dumpCheckGlobalTree("linkdot", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    }
    static void linkDotScope(AstNetlist* nodep) {
        UINFO(2,__FUNCTION__<<": "<<endl);
        linkDotGuts(nodep,LDS_SCOPED);
        V3Global::dumpCheckGlobalTree("linkdot", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
};

#endif  // Guard
