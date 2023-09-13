// -*- mode: C++; c-file-style: "cc-mode" -*-
//
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2022-2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#define VL_MT_DISABLED_CODE_UNIT 1

#include "mt_disabled.h"
#include "mt_enabled.h"

void unannotatedMtDisabledFunctionBad() {
}

void UnannotatedMtDisabledClass::unannotatedMtDisabledMethodBad() {
}

void UnannotatedMtDisabledClass::unannotatedMtDisabledStaticMethodBad() {
}

// Declarations in .cpp don't have to be annotated with VL_MT_DISABLED.
void annotatedMtDisabledFunctionOK();

void annotatedMtDisabledFunctionOK() {
    VerilatedMutex m;
    // REQUIRES should be ignored and mutex locking not needed.
    nsf_aa_VL_REQUIRES(m);
}

void AnnotatedMtDisabledClass::annotatedMtDisabledMethodOK() {
    annotatedMtDisabledFunctionOK();
}

void AnnotatedMtDisabledClass::annotatedMtDisabledStaticMethodOK() {
    annotatedMtDisabledFunctionOK();
}
