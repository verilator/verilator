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

#ifndef T_DIST_ATTRIBUTES_MT_DISABLED_H_
#define T_DIST_ATTRIBUTES_MT_DISABLED_H_

#include "verilatedos.h"

#include "V3ThreadSafety.h"

void unannotatedMtDisabledFunctionBad();

// Duplicate to check that every declaration is reported
void unannotatedMtDisabledFunctionBad();

class UnannotatedMtDisabledClass final {
public:
    void unannotatedMtDisabledMethodBad();
    static void unannotatedMtDisabledStaticMethodBad();

    int unannotatedInlineMethodOK() const { return 42; }
    static int unannotatedInlineStaticMethodOK() { return -42; }
};

void annotatedMtDisabledFunctionOK() VL_MT_DISABLED;

// Duplicate
void annotatedMtDisabledFunctionOK() VL_MT_DISABLED;

class AnnotatedMtDisabledClass final {
public:
    void annotatedMtDisabledMethodOK() VL_MT_DISABLED;
    static void annotatedMtDisabledStaticMethodOK() VL_MT_DISABLED;

    int annotatedInlineMethodOK() const VL_MT_DISABLED { return 42; }
    static int annotatedInlineStaticMethodOK() VL_MT_DISABLED { return -42; }
};

#endif  // T_DIST_ATTRIBUTES_MT_DISABLED_H_
