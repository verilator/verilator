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

#include "verilatedos.h"

#include "mt_enabled.h"

// Non-Static Functions, Annotated declaration, Unannotated definition.
// (definitions)
EMIT_ALL(SIG_UNANNOTATED, nsf_au, /**/, {})

// Non-Static Functions, Unannotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, nsf_ua, /**/, {})

// Non-Static Functions, Annotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, nsf_aa, /**/, {})

// Non-Static Functions, Annotated declaration, Annotated definition.
// Definitions have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, nsf_ae, /**/, VL_PURE VL_MT_SAFE{})

// Non-Static Functions, Annotated declaration, Annotated definition.
// Declarations have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, nsf_ea, /**/, {})

// Non-Static Functions (call test).
EMIT_ALL(VL_ATTR_UNUSED static SIG_ANNOTATED, nsf_test_caller_func, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, nsf_au, m, ;)
    EMIT_ALL(CALL, nsf_ua, m, ;)
    EMIT_ALL(CALL, nsf_aa, m, ;)
    EMIT_ALL(CALL, nsf_ae, m, ;)
    EMIT_ALL(CALL, nsf_ea, m, ;)
})

// Inline Functions in Header (call test).
EMIT_ALL(VL_ATTR_UNUSED static SIG_ANNOTATED, ifh_test_caller_func, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, ifh, m, ;)
})

// Static Functions in Cpp file.
EMIT_ALL(inline SIG_ANNOTATED, sfc, /**/, {})

// Static Functions in Cpp file (call test).
EMIT_ALL(VL_ATTR_UNUSED static SIG_ANNOTATED, sfc_test_caller_func, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, sfc, m, ;)
})

// Static Class Methods, Annotated declaration, Unannotated definition.
// (definitions)
EMIT_ALL(SIG_UNANNOTATED, TestClass::scm_au, /**/, {})

// Static Class Methods, Unannotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::scm_ua, /**/, {})

// Static Class Methods, Annotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::scm_aa, /**/, {})

// Static Class Methods, Annotated declaration, Annotated definition.
// Definitions have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::scm_ae, /**/, VL_PURE VL_MT_SAFE{})

// Static Class Methods, Annotated declaration, Annotated definition.
// Declarations have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::scm_ea, /**/, {})

// Static Class Methods (call test).
// (definition)
EMIT_ALL(SIG_ANNOTATED, TestClass::scm_test_caller_smethod, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, TestClass::scm_au, m, ;)
    EMIT_ALL(CALL, TestClass::scm_ua, m, ;)
    EMIT_ALL(CALL, TestClass::scm_aa, m, ;)
    EMIT_ALL(CALL, TestClass::scm_ae, m, ;)
    EMIT_ALL(CALL, TestClass::scm_ea, m, ;)

    TestClass tc;
    EMIT_ALL(CALL, tc.scm_au, m, ;)
    EMIT_ALL(CALL, tc.scm_ua, m, ;)
    EMIT_ALL(CALL, tc.scm_aa, m, ;)
    EMIT_ALL(CALL, tc.scm_ae, m, ;)
    EMIT_ALL(CALL, tc.scm_ea, m, ;)

    TestClass* tcp = &tc;
    EMIT_ALL(CALL, tcp->scm_au, m, ;)
    EMIT_ALL(CALL, tcp->scm_ua, m, ;)
    EMIT_ALL(CALL, tcp->scm_aa, m, ;)
    EMIT_ALL(CALL, tcp->scm_ae, m, ;)
    EMIT_ALL(CALL, tcp->scm_ea, m, ;)
})

// Inline Static Class Methods (call test).
// (definition)
EMIT_ALL(SIG_ANNOTATED, TestClass::iscm_test_caller_smethod, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, TestClass::iscm, m, ;)

    TestClass tc;
    EMIT_ALL(CALL, tc.iscm, m, ;)

    TestClass* tcp = &tc;
    EMIT_ALL(CALL, tcp->iscm, m, ;)
})

// Class Methods, Annotated declaration, Unannotated definition.
// (definitions)
EMIT_ALL(SIG_UNANNOTATED, TestClass::cm_au, /**/, {})

// Class Methods, Unannotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::cm_ua, /**/, {})

// Class Methods, Annotated declaration, Annotated definition.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::cm_aa, /**/, {})

// Class Methods, Annotated declaration, Annotated definition.
// Definitions have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::cm_ae, /**/, VL_PURE VL_MT_SAFE{})

// Class Methods, Annotated declaration, Annotated definition.
// Declarations have extra annotations.
// (definitions)
EMIT_ALL(SIG_ANNOTATED, TestClass::cm_ea, /**/, {})

// Class Methods (call test).
// (definition)
EMIT_ALL(SIG_ANNOTATED, TestClass::cm_test_caller_smethod, /**/, {
    VerilatedMutex m;

    TestClass tc;
    EMIT_ALL(CALL, tc.cm_au, m, ;)
    EMIT_ALL(CALL, tc.cm_ua, m, ;)
    EMIT_ALL(CALL, tc.cm_aa, m, ;)
    EMIT_ALL(CALL, tc.cm_ae, m, ;)
    EMIT_ALL(CALL, tc.cm_ea, m, ;)

    TestClass* tcp = &tc;
    EMIT_ALL(CALL, tcp->cm_au, m, ;)
    EMIT_ALL(CALL, tcp->cm_ua, m, ;)
    EMIT_ALL(CALL, tcp->cm_aa, m, ;)
    EMIT_ALL(CALL, tcp->cm_ae, m, ;)
    EMIT_ALL(CALL, tcp->cm_ea, m, ;)
})

// Inline Class Methods (call test).
// (definition)
EMIT_ALL(SIG_ANNOTATED, TestClass::icm_test_caller_smethod, /**/, {
    VerilatedMutex m;

    TestClass tc;
    EMIT_ALL(CALL, tc.icm, m, ;)

    TestClass* tcp = &tc;
    EMIT_ALL(CALL, tcp->icm, m, ;)
})
