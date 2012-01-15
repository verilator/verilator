// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Link XREF signals/functions together
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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

class V3LinkDot {
private:
    static void linkDotGuts(AstNetlist* nodep, bool preparam, bool scoped);
public:
    static void linkDotPrearrayed(AstNetlist* nodep)	{ linkDotGuts(nodep,true,false); }
    static void linkDotArrayed(AstNetlist* nodep)	{ linkDotGuts(nodep,false,false); }
    static void linkDotScope(AstNetlist* nodep)		{ linkDotGuts(nodep,false,true); }
};

#endif // Guard
