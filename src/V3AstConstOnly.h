// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
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

#ifndef _V3ASTCONSTONLY_H_
#define _V3ASTCONSTONLY_H_ 1

// Include only in visitors that do not not edit nodes, so should use constant iterators
#define iterateAndNext   error_use_iterateAndNextConst
#define iterateChildren  error_use_iterateChildrenConst

#define addNext          error_no_addNext_in_ConstOnlyVisitor
#define replaceWith      error_no_replaceWith_in_ConstOnlyVisitor
#define deleteTree       error_no_deleteTree_in_ConstOnlyVisitor
#define unlinkFrBack     error_no_unlinkFrBack_in_ConstOnlyVisitor

#endif // Guard
