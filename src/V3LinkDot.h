// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link XREF signals/functions together
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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
    static void linkDotGuts(AstNetlist* nodep, VLinkDotStep step);
public:
    static void linkDotPrimary(AstNetlist* nodep) {
	UINFO(2,__FUNCTION__<<": "<<endl);	linkDotGuts(nodep,LDS_PRIMARY);
	V3Global::dumpCheckGlobalTree("linkdot.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    }
    static void linkDotParamed(AstNetlist* nodep) {
	UINFO(2,__FUNCTION__<<": "<<endl);	linkDotGuts(nodep,LDS_PARAMED);
	V3Global::dumpCheckGlobalTree("paramlink.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
    static void linkDotArrayed(AstNetlist* nodep) {
	UINFO(2,__FUNCTION__<<": "<<endl);	linkDotGuts(nodep,LDS_ARRAYED);
	V3Global::dumpCheckGlobalTree("linkdot.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
    }
    static void linkDotScope(AstNetlist* nodep) {
	UINFO(2,__FUNCTION__<<": "<<endl);	linkDotGuts(nodep,LDS_SCOPED);
	V3Global::dumpCheckGlobalTree("linkdot.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
    }
};

#endif // Guard
