// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cleanup stage in V3Width
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3WIDTHREMOVE_H_
#define VERILATOR_V3WIDTHREMOVE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Error.h"

// clang-format off
#ifndef VERILATOR_V3WIDTH_CPP_
# error "V3WidthRemove for V3Width internal use only"
#endif
// clang-format on

//######################################################################

class WidthRemoveVisitor final : public VNVisitor {
    // METHODS
    VL_DEFINE_DEBUG_FUNCTIONS;

    void replaceWithSignedVersion(AstNode* nodep, AstNode* newp) {
        UINFO(6, " Replace " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        newp->dtypeFrom(nodep);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    void visit(AstSigned* nodep) override {
        VL_DO_DANGLING(replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()), nodep);
    }
    void visit(AstUnsigned* nodep) override {
        VL_DO_DANGLING(replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    WidthRemoveVisitor() = default;
    ~WidthRemoveVisitor() override = default;
    AstNode* mainAcceptEdit(AstNode* nodep) { return iterateSubtreeReturnEdits(nodep); }
};

//######################################################################

#endif  // Guard
