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

#ifndef T_DIST_ATTRIBUTES_MT_ENABLED_H_
#define T_DIST_ATTRIBUTES_MT_ENABLED_H_

#include "verilatedos.h"

#include "verilated.h"

#include <mutex>

#define NO_ANNOTATION

#define CALL_0(prefix, annotation, aarg_type, aarg, val) prefix##_##annotation(val)

#define CALL_1(prefix, annotation, aarg_type, aarg, val) prefix##_##annotation(val)

#define SIG_ANNOTATED_0(prefix, annotation, aarg_type, aarg, val) \
    void prefix##_##annotation(aarg_type aarg) annotation

#define SIG_ANNOTATED_1(prefix, annotation, aarg_type, aarg, val) \
    void prefix##_##annotation(aarg_type aarg) annotation(aarg)

#define SIG_UNANNOTATED_0(prefix, annotation, aarg_type, aarg, val) \
    void prefix##_##annotation(aarg_type aarg)

#define SIG_UNANNOTATED_1(prefix, annotation, aarg_type, aarg, val) \
    void prefix##_##annotation(aarg_type aarg)

// clang-format off
#define EMIT_ALL(before, sig_prefix, val, after) \
    before##_0(sig_prefix, NO_ANNOTATION,       VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_PURE,             VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_MT_SAFE,          VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_MT_SAFE_POSTINIT, VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_MT_UNSAFE,        VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_MT_UNSAFE_ONE,    VerilatedMutex&, mtx, val) after \
    before##_0(sig_prefix, VL_MT_START,         VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_ACQUIRE,          VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_REQUIRES,         VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_RELEASE,          VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_ACQUIRE_SHARED,   VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_RELEASE_SHARED,   VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_EXCLUDES,         VerilatedMutex&, mtx, val) after \
    before##_1(sig_prefix, VL_MT_SAFE_EXCLUDES, VerilatedMutex&, mtx, val) after
// clang-format on

// Non-Static Functions, Annotated declaration, Unannotated definition.
// (declarations)
EMIT_ALL(SIG_ANNOTATED, nsf_au, /**/, ;)

// Non-Static Functions, Unannotated declaration, Annotated definition.
// (declarations)
EMIT_ALL(SIG_UNANNOTATED, nsf_ua, /**/, ;)

// Non-Static Functions, Annotated declaration, Annotated definition.
// (declarations)
EMIT_ALL(SIG_ANNOTATED, nsf_aa, /**/, ;)

// Non-Static Functions, Annotated declaration, Annotated definition.
// Definitions have extra annotations.
// (declarations)
EMIT_ALL(SIG_ANNOTATED, nsf_ae, /**/, ;)

// Non-Static Functions, Annotated declaration, Annotated definition.
// Declarations have extra annotations.
// (declarations)
EMIT_ALL(SIG_ANNOTATED, nsf_ea, /**/, VL_PURE VL_MT_SAFE;)

// Non-Static Functions (call test in header).
EMIT_ALL(inline SIG_ANNOTATED, nsf_test_caller_func_hdr, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, nsf_au, m, ;)
    EMIT_ALL(CALL, nsf_ua, m, ;)
    EMIT_ALL(CALL, nsf_aa, m, ;)
    EMIT_ALL(CALL, nsf_ae, m, ;)
    EMIT_ALL(CALL, nsf_ea, m, ;)
})

// Inline Functions in Header.
EMIT_ALL(inline SIG_ANNOTATED, ifh, /**/, {})

// Inline Functions in Header (call test in header).
EMIT_ALL(inline SIG_ANNOTATED, ifh_test_caller_func_hdr, /**/, {
    VerilatedMutex m;

    EMIT_ALL(CALL, ifh, m, ;)
})

struct GuardMe {
    void safe_if_guarded_or_local() {}

    operator int() const { return 4; }

    GuardMe& operator+=(int) { return *this; }
};

class TestClass {
    VerilatedMutex m_mtx;
    GuardMe m_guardme VL_GUARDED_BY(m_mtx);

    GuardMe m_guardme_unguarded;

public:
    // Static Class Methods, Annotated declaration, Unannotated definition.
    // (declarations)
    EMIT_ALL(static SIG_ANNOTATED, scm_au, /**/, ;)

    // Static Class Methods, Unannotated declaration, Annotated definition.
    // (declarations)
    EMIT_ALL(static SIG_UNANNOTATED, scm_ua, /**/, ;)

    // Static Class Methods, Annotated declaration, Annotated definition.
    // (declarations)
    EMIT_ALL(static SIG_ANNOTATED, scm_aa, /**/, ;)

    // Static Class Methods, Annotated declaration, Annotated definition.
    // Definitions have extra annotations.
    // (declarations)
    EMIT_ALL(static SIG_ANNOTATED, scm_ae, /**/, ;)

    // Static Class Methods, Annotated declaration, Annotated definition.
    // Declarations have extra annotations.
    // (declarations)
    EMIT_ALL(static SIG_ANNOTATED, scm_ea, /**/, VL_PURE VL_MT_SAFE;)

    // Static Class Methods (call test in header).
    EMIT_ALL(static SIG_ANNOTATED, scm_test_caller_smethod_hdr, /**/, {
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

    // Static Class Methods (call test).
    // (declaration)
    EMIT_ALL(static SIG_ANNOTATED, scm_test_caller_smethod, /**/, ;)

    // Inline Static Class Methods.
    EMIT_ALL(static SIG_ANNOTATED, iscm, /**/, {})

    // Inline Static Class Methods (call test in header).
    EMIT_ALL(static SIG_ANNOTATED, iscm_test_caller_smethod_hdr, /**/, {
        VerilatedMutex m;

        EMIT_ALL(CALL, TestClass::iscm, m, ;)

        TestClass tc;
        EMIT_ALL(CALL, tc.iscm, m, ;)

        TestClass* tcp = &tc;
        EMIT_ALL(CALL, tcp->iscm, m, ;)
    })

    // Inline Static Class Methods (call test).
    // (declaration)
    EMIT_ALL(static SIG_ANNOTATED, iscm_test_caller_smethod, /**/, ;)

    // Class Methods, Annotated declaration, Unannotated definition.
    // (declarations)
    EMIT_ALL(SIG_ANNOTATED, cm_au, /**/, ;)

    // Class Methods, Unannotated declaration, Annotated definition.
    // (declarations)
    EMIT_ALL(SIG_UNANNOTATED, cm_ua, /**/, ;)

    // Class Methods, Annotated declaration, Annotated definition.
    // (declarations)
    EMIT_ALL(SIG_ANNOTATED, cm_aa, /**/, ;)

    // Class Methods, Annotated declaration, Annotated definition.
    // Definitions have extra annotations.
    // (declarations)
    EMIT_ALL(SIG_ANNOTATED, cm_ae, /**/, ;)

    // Class Methods, Annotated declaration, Annotated definition.
    // Declarations have extra annotations.
    // (declarations)
    EMIT_ALL(SIG_ANNOTATED, cm_ea, /**/, VL_PURE VL_MT_SAFE;)

    // Class Methods (call test in header).
    EMIT_ALL(SIG_ANNOTATED, cm_test_caller_smethod_hdr, /**/, {
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

    // Class Methods (call test).
    // (declaration)
    EMIT_ALL(SIG_ANNOTATED, cm_test_caller_smethod, /**/, ;)

    // Inline Class Methods.
    EMIT_ALL(SIG_ANNOTATED, icm, /**/, {})

    // Inline Class Methods (call test in header).
    EMIT_ALL(SIG_ANNOTATED, icm_test_caller_smethod_hdr, /**/, {
        VerilatedMutex m;

        TestClass tc;
        EMIT_ALL(CALL, tc.icm, m, ;)

        TestClass* tcp = &tc;
        EMIT_ALL(CALL, tcp->icm, m, ;)
    })

    // Inline Class Methods (call test).
    // (declaration)
    EMIT_ALL(SIG_ANNOTATED, icm_test_caller_smethod, /**/, ;)

    void guarded_by_test_pass(GuardMe& guardme_arg) VL_MT_SAFE {
        guardme_arg.safe_if_guarded_or_local();
        int a = guardme_arg;
        guardme_arg += 4;

        m_mtx.lock();
        m_guardme.safe_if_guarded_or_local();
        int b = m_guardme;
        m_guardme += 4;
        m_mtx.unlock();

        GuardMe guardme_local;
        guardme_local.safe_if_guarded_or_local();
        int c = guardme_local;
        guardme_local += 4;
    }

    void guarded_by_test_fail() VL_MT_SAFE {
        m_guardme_unguarded.safe_if_guarded_or_local();
        int a = m_guardme_unguarded;
        m_guardme_unguarded += 4;
    }
};

static void static_function() {}

class StaticClass {
public:
    static void static_class_function() {}
};

class ConstructorCallsUnsafeLocalFunction {
public:
    void unsafe_function() VL_MT_UNSAFE{};
    ConstructorCallsUnsafeLocalFunction() { unsafe_function(); }
};
class ConstructorCallsStaticFunctionNoAnnotation {
public:
    ConstructorCallsStaticFunctionNoAnnotation() { static_function(); }
};

class ConstructorCallsLocalFunction {
public:
    void local_function() {}
    ConstructorCallsLocalFunction() { local_function(); }
};

class ConstructorCallsLocalFunctionCallsGlobal {
public:
    void local_function() { static_function(); }
    ConstructorCallsLocalFunctionCallsGlobal() { local_function(); }
};

class SafeFunction {
public:
    void safe_function() VL_MT_SAFE {}
};
class UnsafeFunction {
public:
    void unsafe_function() VL_MT_UNSAFE {}
};

class ConstructorWithPointer {
public:
    ConstructorWithPointer(SafeFunction* p) { p->safe_function(); }
};

class ConstructorWithReference {
public:
    ConstructorWithReference(SafeFunction& p) { p.safe_function(); }
};
class ConstructorWithUnsafePointer {
public:
    ConstructorWithUnsafePointer(UnsafeFunction* p) { p->unsafe_function(); }
};

class ConstructorWithUnsafeReference {
public:
    ConstructorWithUnsafeReference(UnsafeFunction& p) { p.unsafe_function(); }
};

class ConstructorCallsLocalCallsGlobal {
    void local_function2() { static_function(); }
    void local_function() { local_function2(); }

public:
    ConstructorCallsLocalCallsGlobal() { local_function(); }
};

class ConstructorCallsLocalCallsClassGlobal {
    void local_function2() { StaticClass::static_class_function(); }
    void local_function() { local_function2(); }

public:
    ConstructorCallsLocalCallsClassGlobal() { local_function(); }
};
class DummyClass2 {
public:
    void dummy_function2() {}
};
class DummyClass {
public:
    DummyClass2 d;
    void dummy_function() {}
};
DummyClass dummyGlobalVar;
class ConstructorCallsGlobalObject {

public:
    ConstructorCallsGlobalObject() { dummyGlobalVar.dummy_function(); }
};

class ConstructorCallsGlobalObjectMember {

public:
    ConstructorCallsGlobalObjectMember() { dummyGlobalVar.d.dummy_function2(); }
};

class TestClassConstructor {
    void safe_function_unsafe_constructor_bad() VL_MT_SAFE {
        ConstructorCallsUnsafeLocalFunction f{};
    };
    void safe_function_static_constructor_bad() VL_MT_SAFE {
        ConstructorCallsStaticFunctionNoAnnotation f{};
    };
    void safe_function_local_function_global_bad() VL_MT_SAFE {
        ConstructorCallsLocalFunctionCallsGlobal f{};
    }
    void safe_function_local_function_constructor_good() VL_MT_SAFE {
        ConstructorCallsLocalFunction f{};
    }
    void safe_function_calls_constructor_with_pointer_good() VL_MT_SAFE {
        SafeFunction* i = new SafeFunction{};
        ConstructorWithPointer f{i};
    }
    void safe_function_calls_constructor_with_reference_good() VL_MT_SAFE {
        SafeFunction i;
        ConstructorWithReference f{i};
    }
    void safe_function_calls_constructor_with_unsafepointer_bad() VL_MT_SAFE {
        UnsafeFunction* i = new UnsafeFunction{};
        ConstructorWithUnsafePointer f{i};
    }
    void safe_function_calls_constructor_with_unsafereference_bad() VL_MT_SAFE {
        UnsafeFunction i;
        ConstructorWithUnsafeReference f{i};
    }
    void safe_function_calls_constructor_local_calls_global_bad() VL_MT_SAFE {
        ConstructorCallsLocalCallsGlobal f{};
    }
    void safe_function_calls_constructor_local_calls_class_global_bad() VL_MT_SAFE {
        ConstructorCallsLocalCallsClassGlobal f{};
    }
    void safe_function_calls_constructor_global_object_bad() VL_MT_STABLE {
        ConstructorCallsGlobalObject f{};
    }
    void safe_function_calls_constructor_global_object_member_bad() VL_MT_STABLE {
        ConstructorCallsGlobalObjectMember f{};
    }
};

#endif  // T_DIST_ATTRIBUTES_MT_ENABLED_H_
