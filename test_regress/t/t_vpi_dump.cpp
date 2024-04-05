// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "svdpi.h"
#include "vpi_user.h"

#include <cstdio>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

#include <map>
#include <vector>

int errors = 0;

// vpiType -> list of vpiTypes to iterate over
std::map<int32_t, std::vector<int32_t>> iterate_over = [] {
    // static decltype(iterate_over) iterate_over = [] {
    /* for reused lists */

    // vpiInstance is the base class for module, program, interface, etc.
    std::vector<int32_t> instance_options = {
        vpiNet,
        vpiNetArray,
        vpiReg,
        vpiRegArray,
    };

    std::vector<int32_t> module_options = {
        // vpiModule,  // Aldec SEGV on mixed language
        // vpiModuleArray,       // Aldec SEGV on mixed language
        // vpiIODecl,            // Don't care about these
        vpiMemory, vpiIntegerVar, vpiRealVar,
        // vpiRealNet, Vpi extension
        vpiStructVar, vpiStructNet, vpiNamedEvent, vpiNamedEventArray, vpiParameter,
        // vpiVariables, // parent of vpiReg, vpiRegArray, vpiIntegerVar, etc vars
        // vpiSpecParam,         // Don't care
        // vpiParamAssign,       // Aldec SEGV on mixed language
        // vpiDefParam,          // Don't care
        vpiPrimitive, vpiPrimitiveArray,
        // vpiContAssign,        // Don't care
        // vpiProcess,  // Don't care
        vpiModPath, vpiTchk, vpiAttribute, vpiPort, vpiInternalScope,
        // vpiInterface,         // Aldec SEGV on mixed language
        // vpiInterfaceArray,    // Aldec SEGV on mixed language
    };

    // append base class vpiInstance members
    module_options.insert(module_options.begin(), instance_options.begin(),
                          instance_options.end());

    std::vector<int32_t> struct_options = {
        vpiNet,       vpiReg,       vpiRegArray,       vpiMemory,
        vpiParameter, vpiPrimitive, vpiPrimitiveArray, vpiAttribute,
        vpiMember,
    };

    return decltype(iterate_over){
        {vpiModule, module_options},
        {vpiInterface, instance_options},
        {vpiGenScope, module_options},

        {vpiStructVar, struct_options},
        {vpiStructNet, struct_options},

        {vpiNet,
         {
             // vpiContAssign,        // Driver and load handled separately
             // vpiPrimTerm,
             // vpiPathTerm,
             // vpiTchkTerm,
             // vpiDriver,
             // vpiLocalDriver,
             // vpiLoad,
             // vpiLocalLoad,
             vpiNetBit,
         }},
        {vpiNetArray,
         {
             vpiNet,
         }},
        {vpiRegArray,
         {
             vpiReg,
         }},
        {vpiMemory,
         {
             vpiMemoryWord,
         }},
        {vpiPort,
         {
             vpiPortBit,
         }},
        {vpiGate,
         {
             vpiPrimTerm,
             vpiTableEntry,
             vpiUdpDefn,
         }},
        {vpiPackage,
         {
             vpiParameter,
         }},
    };
}();

void modDump(TestVpiHandle& it, int n) {

    if (n > 8) {
        printf("going too deep\n");
        return;
    }

    while (const TestVpiHandle& hndl = vpi_scan(it)) {
        for (int i = 0; i < n; i++) printf("    ");
        const int type = vpi_get(vpiType, hndl);
        const char* name = vpi_get_str(vpiName, hndl);
        const char* fullname = vpi_get_str(vpiFullName, hndl);
        printf("%s (%s) %s\n", name, strFromVpiObjType(type), fullname);
        if (type == vpiParameter || type == vpiConstType) {
            for (int i = 0; i < n + 1; i++) printf("    ");
            printf("vpiConstType=%s\n", strFromVpiConstType(vpi_get(vpiConstType, hndl)));
        }

        if (iterate_over.find(type) == iterate_over.end()) { continue; }
        for (int type : iterate_over.at(type)) {
            TestVpiHandle subIt = vpi_iterate(type, hndl);
            if (subIt) {
                for (int i = 0; i < n + 1; i++) printf("    ");
                printf("%s:\n", strFromVpiObjType(type));
                modDump(subIt, n + 1);
            }
        }
    }
    it.freed();
}

PLI_INT32 start_of_sim(t_cb_data* data) {
    TestVpiHandle it = vpi_iterate(vpiModule, NULL);
    TEST_CHECK_NZ(it);
    modDump(it, 0);
    return 0;
}

//cver, xcelium entry
void vpi_compat_bootstrap(void) {

    // We're able to call vpi_main() here on Verilator/Xcelium,
    // but Icarus complains (rightfully so)
    s_cb_data cb_data;
    s_vpi_time vpi_time;

    vpi_time.high = 0;
    vpi_time.low = 0;
    vpi_time.type = vpiSimTime;

    cb_data.reason = cbStartOfSimulation;
    cb_data.cb_rtn = &start_of_sim;
    cb_data.obj = NULL;
    cb_data.time = &vpi_time;
    cb_data.value = NULL;
    cb_data.index = 0;
    cb_data.user_data = NULL;
    TestVpiHandle callback_h = vpi_register_cb(&cb_data);
}

// Verilator (via t_vpi_main.cpp), and standard LRM entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
