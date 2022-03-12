// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Ast node structure
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

#ifndef VERILATOR_V3ASTCONSTONLY_H_
#define VERILATOR_V3ASTCONSTONLY_H_

// Include only in visitors that do not not edit nodes, so should use constant iterators
#define iterateAndNext error_use_iterateAndNextConst
#define iterateChildren error_use_iterateChildrenConst

#define addNext error_no_addNext_in_ConstOnlyVisitor
#define replaceWith error_no_replaceWith_in_ConstOnlyVisitor
#define deleteTree error_no_deleteTree_in_ConstOnlyVisitor
#define unlinkFrBack error_no_unlinkFrBack_in_ConstOnlyVisitor

#endif  // Guard
