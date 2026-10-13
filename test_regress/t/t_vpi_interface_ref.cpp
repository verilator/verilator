// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "sv_vpi_user.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <string>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;

#define TEST_STRINGIFY_(x) #x
#define TEST_STRINGIFY(x) TEST_STRINGIFY_(x)

// Path of the test top. With TEST_MODEL_NAME the model is constructed under
// that instance name, so every path is prefixed with it.
static std::string test_top() {
    std::string top;
#ifdef TEST_MODEL_NAME
    top = std::string{TEST_STRINGIFY(TEST_MODEL_NAME)} + ".";
#endif
    top += TestSimulator::top();
    return top;
}

// Report with the object path rather than a line number, so the failure
// messages are stable against edits to this file
static void check_failed(const std::string& msg) {
    std::cout << "%Error: " << msg << std::endl;
    ++errors;
}

static void check_type(vpiHandle handle, const std::string& what, PLI_INT32 expected) {
    const PLI_INT32 got = vpi_get(vpiType, handle);
    if (got != expected) {
        check_failed("vpi_get(vpiType, " + what + ") = " + strFromVpiObjType(got) + ", expected "
                     + strFromVpiObjType(expected));
    }
}

static void check_fullname(vpiHandle handle, const std::string& what,
                           const std::string& expected) {
    const char* const got = vpi_get_str(vpiFullName, handle);
    if (!got) {
        check_failed("vpi_get_str(vpiFullName, " + what + ") = NULL, expected '" + expected + "'");
    } else if (expected != got) {
        check_failed("vpi_get_str(vpiFullName, " + what + ") = '" + got + "', expected '"
                     + expected + "'");
    }
}

// Read a 32-bit variable relative to scope, checking it reads back as expected
static void check_read(vpiHandle scope, const std::string& scopeName, const std::string& varName,
                       uint32_t expected) {
    const std::string what = scopeName + "." + varName;
    const TestVpiHandle vh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(varName.c_str()), scope);
    if (!vh) {
        check_failed("vpi_handle_by_name('" + varName + "', <" + scopeName + ">) = NULL");
        return;
    }

    s_vpi_value value;
    value.format = vpiIntVal;
    vpi_get_value(vh, &value);
    const uint32_t got = static_cast<uint32_t>(value.value.integer);
    if (got != expected) {
        char buf[256];
        std::snprintf(buf, sizeof(buf), "read '%s' = 0x%08x, expected 0x%08x", what.c_str(), got,
                      expected);
        check_failed(buf);
    }
}

// Write a 32-bit variable relative to scope
static void put_var(vpiHandle scope, const std::string& scopeName, const std::string& varName,
                    uint32_t newval) {
    const TestVpiHandle vh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(varName.c_str()), scope);
    if (!vh) {
        check_failed("vpi_handle_by_name('" + varName + "', <" + scopeName + ">) = NULL");
        return;
    }

    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = newval;
    vpi_put_value(vh, &value, NULL, vpiNoDelay);
}

static void check_name(vpiHandle handle, const std::string& what, const std::string& expected) {
    const char* const got = vpi_get_str(vpiName, handle);
    if (!got) {
        check_failed("vpi_get_str(vpiName, " + what + ") = NULL, expected '" + expected + "'");
    } else if (expected != got) {
        check_failed("vpi_get_str(vpiName, " + what + ") = '" + got + "', expected '" + expected
                     + "'");
    }
}

static void check_defname(vpiHandle handle, const std::string& what, const std::string& expected) {
    const char* const got = vpi_get_str(vpiDefName, handle);
    if (!got) {
        check_failed("vpi_get_str(vpiDefName, " + what + ") = NULL, expected '" + expected + "'");
    } else if (expected != got) {
        check_failed("vpi_get_str(vpiDefName, " + what + ") = '" + got + "', expected '" + expected
                     + "'");
    }
}

// An interface reference and a modport are not scopes, so a name must not
// resolve relative to them.  In particular this must not silently fall back
// to resolving from the top level, which would return an unrelated object.
static void check_not_a_scope(vpiHandle handle, const std::string& what) {
    // "some_intf_var" exists in the interface, "top_collide" only at the top
    // level.  Neither may be found relative to this handle.
    for (const char* const varName : {"some_intf_var", "top_collide"}) {
        const TestVpiHandle vh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(varName), handle);
        if (vh) {
            const char* const got = vpi_get_str(vpiFullName, vh);
            check_failed("vpi_handle_by_name('" + std::string{varName} + "', <" + what + ">) = '"
                         + (got ? got : "<null>") + "', expected NULL");
        }
    }
}

// vpiActual of an interface reference yields the concrete interface, or, for
// a modport-typed reference, the modport within it.  Follow vpiInterface in
// that case so we always end up at the interface instance.
// Caller must release the result.
static vpiHandle concrete_of(vpiHandle refh, const std::string& what) {
    check_type(refh, what, vpiRefObj);
    check_not_a_scope(refh, what);
    // IEEE 1800-2023 37.15: modport name for a modport-typed reference
    check_defname(refh, what, "SomeModport");

    vpiHandle actualh = vpi_handle(vpiActual, refh);
    if (!actualh) {
        check_failed("vpi_handle(vpiActual, " + what + ") = NULL");
        return NULL;
    }

    // The port is modport-typed, so vpiActual is the modport
    const std::string actWhat = "vpiActual of " + what;
    check_type(actualh, actWhat, vpiModport);
    check_fullname(actualh, actWhat, test_top() + ".concrete_intf.SomeModport");
    check_name(actualh, actWhat, "SomeModport");
    if (vpi_get_str(vpiDefName, actualh)) check_defname(actualh, actWhat, "SomeModport");
    check_not_a_scope(actualh, actWhat);

    vpiHandle intfh = vpi_handle(vpiInterface, actualh);
    vpi_release_handle(actualh);
    if (!intfh) {
        check_failed("vpi_handle(vpiInterface, " + actWhat + ") = NULL");
        return NULL;
    }

    const std::string intfWhat = "vpiInterface of " + actWhat;
    check_type(intfh, intfWhat, vpiInterface);
    check_fullname(intfh, intfWhat, test_top() + ".concrete_intf");
    return intfh;
}

// A plain interface port has no modport, so vpiActual is the concrete
// interface directly rather than a modport.  Caller must release the result.
static vpiHandle concrete_of_plain(const std::string& refName) {
    const TestVpiHandle refh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(refName.c_str()), NULL);
    if (!refh) {
        check_failed("vpi_handle_by_name('" + refName + "') = NULL");
        return NULL;
    }
    const std::string what = "'" + refName + "'";
    check_type(refh, what, vpiRefObj);
    check_not_a_scope(refh, what);
    // IEEE 1800-2023 37.15: interface definition name when there is no modport
    check_defname(refh, what, "SomeIntf");

    vpiHandle actualh = vpi_handle(vpiActual, refh);
    if (!actualh) {
        check_failed("vpi_handle(vpiActual, " + what + ") = NULL");
        return NULL;
    }
    const std::string actWhat = "vpiActual of " + what;
    check_type(actualh, actWhat, vpiInterface);
    check_fullname(actualh, actWhat, test_top() + ".concrete_intf");
    return actualh;
}

// vpi_handle_by_name() of the full path to an interface reference, then on to
// the concrete interface.  Caller must release the result.
static vpiHandle concrete_by_full_name(const std::string& refName) {
    const TestVpiHandle refh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(refName.c_str()), NULL);
    if (!refh) {
        check_failed("vpi_handle_by_name('" + refName + "') = NULL");
        return NULL;
    }
    const std::string what = "'" + refName + "'";
    check_name(refh, what, "intf_ref");
    check_fullname(refh, what, refName);
    return concrete_of(refh, what);
}

// vpi_handle_by_name() of just "intf_ref" relative to a handle for the
// instance containing it, which yields the interface reference directly.
// Caller must release the result.
static vpiHandle concrete_by_relative_name(const std::string& scopeName) {
    const TestVpiHandle scopeh
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(scopeName.c_str()), NULL);
    if (!scopeh) {
        check_failed("vpi_handle_by_name('" + scopeName + "') = NULL");
        return NULL;
    }

    const TestVpiHandle refh = vpi_handle_by_name(const_cast<PLI_BYTE8*>("intf_ref"), scopeh);
    if (!refh) {
        check_failed("vpi_handle_by_name('intf_ref', <" + scopeName + ">) = NULL");
        return NULL;
    }
    const std::string what = "'intf_ref' in '" + scopeName + "'";
    check_fullname(refh, what, scopeName + ".intf_ref");
    return concrete_of(refh, what);
}

static int mon_check() {
    const std::string top = test_top();
    const std::string concrete = top + ".concrete_intf";
    const std::string barScope = top + ".bar";
    const std::string fooScope = top + ".bar.foo";
    const std::string barRef = barScope + ".intf_ref";
    const std::string fooRef = fooScope + ".intf_ref";

    // Baseline: the concrete interface instance resolves and reads back the
    // values set by the initial block
    const TestVpiHandle concreteh
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(concrete.c_str()), NULL);
    if (!concreteh) {
        check_failed("vpi_handle_by_name('" + concrete + "') = NULL");
    } else {
        check_type(concreteh, "'" + concrete + "'", vpiInterface);
        check_read(concreteh, concrete, "some_intf_var", 0x11112222);
        check_read(concreteh, concrete, "other_intf_var", 0x33334444);
    }

    // vpi_handle(vpiActual, <interface reference>) reaches the concrete
    // interface, from which the interface variables are accessible
    {
        const TestVpiHandle intfh = concrete_by_full_name(barRef);
        if (intfh) {
            const std::string what = "concrete via '" + barRef + "'";
            check_read(intfh, what, "some_intf_var", 0x11112222);
            check_read(intfh, what, "other_intf_var", 0x33334444);
            put_var(intfh, what, "some_intf_var", 0x55556666);
        }
    }

    // Same one level deeper, and the write above must be visible here
    {
        const TestVpiHandle intfh = concrete_by_full_name(fooRef);
        if (intfh) {
            const std::string what = "concrete via '" + fooRef + "'";
            check_read(intfh, what, "some_intf_var", 0x55556666);
            check_read(intfh, what, "other_intf_var", 0x33334444);
        }
    }

    // Relative lookup of just "intf_ref" from a handle to the instance
    {
        const TestVpiHandle intfh = concrete_by_relative_name(fooScope);
        if (intfh) {
            const std::string what = "concrete via 'intf_ref' in '" + fooScope + "'";
            check_read(intfh, what, "some_intf_var", 0x55556666);
            put_var(intfh, what, "other_intf_var", 0x77778888);
            check_read(intfh, what, "other_intf_var", 0x77778888);
        }
    }

    // Relative lookup one level up, and the writes above must be visible
    {
        const TestVpiHandle intfh = concrete_by_relative_name(barScope);
        if (intfh) {
            const std::string what = "concrete via 'intf_ref' in '" + barScope + "'";
            check_read(intfh, what, "some_intf_var", 0x55556666);
            check_read(intfh, what, "other_intf_var", 0x77778888);
            // Final values, checked by the Verilog side
            put_var(intfh, what, "some_intf_var", 0xfeedface);
            put_var(intfh, what, "other_intf_var", 0xdeadbeef);
        }
    }

    {
        const TestVpiHandle scopeh
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(fooScope.c_str()), NULL);
        if (scopeh) {
            const TestVpiHandle actualh = vpi_handle(vpiActual, scopeh);
            if (actualh) { check_failed("vpi_handle(vpiActual, <" + fooScope + ">) = non-NULL"); }
            const TestVpiHandle intfh = vpi_handle(vpiInterface, scopeh);
            if (intfh) { check_failed("vpi_handle(vpiInterface, <" + fooScope + ">) = non-NULL"); }
        }
    }

    // The interface must be enumerable by type from the scope containing it
    {
        const TestVpiHandle toph = vpi_handle_by_name(const_cast<PLI_BYTE8*>(top.c_str()), NULL);
        TestVpiHandle it = toph ? vpi_iterate(vpiInterface, toph) : NULL;
        if (!it) {
            check_failed("vpi_iterate(vpiInterface, <" + top + ">) = NULL");
        } else {
            check_type(it, "vpi_iterate(vpiInterface, <" + top + ">)", vpiIterator);
            bool found = false;
            while (vpiHandle ih = vpi_scan(it)) {
                const char* const fn = vpi_get_str(vpiFullName, ih);
                if (fn && concrete == fn) found = true;
                check_type(ih, "vpiInterface iteration item", vpiInterface);
                vpi_release_handle(ih);
            }
            it.freed();
            if (!found) {
                check_failed("vpi_iterate(vpiInterface, <" + top + ">) did not yield '" + concrete
                             + "'");
            }
        }
    }

    {
        TestVpiHandle it = vpi_iterate(vpiInterface, NULL);
        if (it) {
            if (vpiHandle ih = vpi_scan(it)) {
                check_failed("vpi_iterate(vpiInterface, NULL) yielded a handle");
                vpi_release_handle(ih);
            } else {
                it.freed();  // vpi_scan at end released it
            }
        }
    }

    {
        const TestVpiHandle leafh
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(concrete.c_str()), NULL);
        if (!leafh) {
            check_failed("vpi_handle_by_name('" + concrete + "') = NULL");
        } else {
            const TestVpiHandle it = vpi_iterate(vpiInterface, leafh);
            if (it) check_failed("vpi_iterate(vpiInterface, <childless scope>) = non-NULL");
        }
    }

    // A plain interface port: vpiActual is the interface, not a modport
    {
        const TestVpiHandle intfh = concrete_of_plain(fooScope + ".plain_ref");
        if (intfh) {
            const std::string what = "concrete via '" + fooScope + ".plain_ref'";
            check_read(intfh, what, "some_intf_var", 0xfeedface);
            check_read(intfh, what, "other_intf_var", 0xdeadbeef);
        }
    }

    // All of the above wrote through the concrete interface, so the writes
    // must also be visible on the concrete instance path
    if (concreteh) {
        check_read(concreteh, concrete, "some_intf_var", 0xfeedface);
        check_read(concreteh, concrete, "other_intf_var", 0xdeadbeef);
    }

    return errors;
}

//======================================================================

static PLI_INT32 value_change(t_cb_data* datap) {
    // Some simulators also report the declaration initializer as a change;
    // only the write in the initial block, which sets it, means run now
    if (!datap->value || !datap->value->value.integer) return 0;
    if (mon_check()) {
        std::cout << "%Error: t_vpi_interface_ref.cpp: C Test failed with " << errors
                  << " error(s)" << std::endl;
        vpi_control(vpiStop);
    }
    return 0;
}

static PLI_INT32 start_of_sim(t_cb_data* /*datap*/) {
    const std::string watched = test_top() + ".run_mon_check";
    TestVpiHandle varh = vpi_handle_by_name(const_cast<PLI_BYTE8*>(watched.c_str()), NULL);
    if (!varh) {
        check_failed("vpi_handle_by_name('" + watched + "') = NULL");
        vpi_control(vpiStop);
        return 0;
    }

    static s_vpi_time vpi_time;
    vpi_time.type = vpiSuppressTime;
    static s_vpi_value vpi_value;
    vpi_value.format = vpiIntVal;

    static s_cb_data cb_data{};
    cb_data.reason = cbValueChange;
    cb_data.cb_rtn = &value_change;
    cb_data.obj = varh;
    cb_data.time = &vpi_time;
    cb_data.value = &vpi_value;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
    varh.freed();  // Callback holds it
    return 0;
}

void vpi_compat_bootstrap(void) {
    static s_vpi_time vpi_time;
    vpi_time.high = 0;
    vpi_time.low = 0;
    vpi_time.type = vpiSimTime;

    s_cb_data cb_data{};
    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    cb_data.obj = NULL;
    cb_data.time = &vpi_time;
    cb_data.value = NULL;
    cb_data.index = 0;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
