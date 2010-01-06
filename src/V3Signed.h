// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Signed/unsigned resolution
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2010 by Wilson Snyder.  This program is free software; you can
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

#ifndef _V3SIGNED_H_
#define _V3SIGNED_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

class V3Signed {
public:
    static void signedAll(AstNetlist* nodep);
protected:
    friend class V3Width;  // Use widthParamsEdit instead of signedParamsEdit
    static AstNode* signedParamsEdit(AstNode* nodep); // May replace nodep
};

#endif // Guard
