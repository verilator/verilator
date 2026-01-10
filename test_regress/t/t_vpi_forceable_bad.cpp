// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

// DESCRIPTION: Test failure of trying to force a non-forceable signal
//
// This test checks that attempting to force a signal that is not marked as
// forceable causes an error under Verilator, and does not cause an error in
// other simulators that do not need this metacomment to be able to force
// signals.

#include "verilated.h"

#include "TestSimulator.h"  // For is_verilator()
#include "TestVpi.h"  // For CHECK_RESULT_NZ
#include "vpi_user.h"

extern "C" int forceValue(void) {
    if (!TestSimulator::is_verilator()) {
#ifdef VERILATOR
        printf("TestSimulator indicating not verilator, but VERILATOR macro is defined\n");
        return 1;
#endif
    }

    PLI_BYTE8 testSignalName[] = "t.nonForceableSignal";
    vpiHandle signal = vpi_handle_by_name(testSignalName, nullptr);
    CHECK_RESULT_NZ(signal);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s;
    value_s.format = vpiIntVal;
    value_s.value.integer = 0;
    vpi_put_value(signal, &value_s, nullptr, vpiForceFlag);
    // NOLINTNEXTLINE(concurrency-mt-unsafe);
    CHECK_RESULT_Z(vpi_chk_error(nullptr))

    return 0;
}

#ifdef IS_VPI
static int force_value_vpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = forceValue();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

std::array<s_vpi_systf_data, 1> vpi_systf_data
    = {s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$forceValue",
                        (PLI_INT32(*)(PLI_BYTE8*))force_value_vpi, 0, 0, 0}};

// cver entry
extern "C" void vpi_compat_bootstrap(void) {
    for (s_vpi_systf_data& systf : vpi_systf_data) vpi_register_systf(&systf);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
