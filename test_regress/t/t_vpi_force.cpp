// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================
#include "verilated.h"  // For VL_PRINTF

#include "TestSimulator.h"  // For is_verilator()
#include "TestVpi.h"  // For CHECK_RESULT_NZ
#include "vpi_user.h"

constexpr PLI_INT32 forceValue = 0;
constexpr PLI_INT32 releaseValue = 1;
constexpr int maxAllowedErrorLevel = vpiWarning;
const std::string testSignalName = "t.test.clockedReg";

namespace {

bool vpiCheckErrorLevel(const int maxAllowedErrorLevel) {

    t_vpi_error_info errorInfo{};
    const bool errorOccured = vpi_chk_error(&errorInfo);
    if (VL_UNLIKELY(errorOccured)) {
        VL_PRINTF("%s", errorInfo.message);
        return errorInfo.level > maxAllowedErrorLevel;
    }
    return false;
}

// vpi_handle_by_name expects a non-const PLI_BYTE8* array, so this function creates a copy of the
// const string name.
vpiHandle vpiHandleFromString(const std::string& name) {
    std::vector<char> nameCopy(name.begin(), name.end());
    nameCopy.push_back('\0');
    return vpi_handle_by_name(reinterpret_cast<PLI_BYTE8*>(nameCopy.data()), nullptr);
}

int checkValues(int expectedValue) {
    vpiHandle signalp = vpiHandleFromString(testSignalName);
    CHECK_RESULT_NZ(signalp);  // NOLINT(concurrency-mt-unsafe)
    s_vpi_value value_s;
    value_s.format = vpiIntVal;
    value_s.value.integer = 0;
    int signalValue = 0;

    vpi_get_value(signalp, &value_s);
    signalValue = value_s.value.integer;

    // NOLINTNEXTLINE(concurrency-mt-unsafe);
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))
    // NOLINTNEXTLINE(concurrency-mt-unsafe, performance-avoid-endl);
    CHECK_RESULT(signalValue, expectedValue)

    return 0;
}

}  // namespace

extern "C" int baselineValue(void) { return releaseValue; }

extern "C" int checkValuesForced(void) { return checkValues(forceValue); }

extern "C" int checkValuesReleased(void) { return checkValues(releaseValue); }

extern "C" int forceValues(void) {
    if (!TestSimulator::is_verilator()) {
#ifdef VERILATOR
        printf("TestSimulator indicating not verilator, but VERILATOR macro is defined\n");
        return 1;
#endif
    }

    vpiHandle signalp = vpiHandleFromString(testSignalName);
    CHECK_RESULT_NZ(signalp);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s;
    value_s.format = vpiIntVal;
    value_s.value.integer = forceValue;
    vpi_put_value(signalp, &value_s, nullptr, vpiForceFlag);
    // NOLINTNEXTLINE(concurrency-mt-unsafe);
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

extern "C" int releaseValues(void) {
    vpiHandle signalp = vpiHandleFromString(testSignalName);
    CHECK_RESULT_NZ(signalp);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s;
    value_s.format = vpiIntVal;
    value_s.value.integer = releaseValue;
    vpi_put_value(signalp, &value_s, nullptr, vpiReleaseFlag);
    // NOLINTNEXTLINE(concurrency-mt-unsafe);
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))
    // TODO: Correct value for value_s is not implemented yet in vpi_put_value with vpiReleaseFlag,
    // so for now it will always return the force value.

    // NOLINTNEXTLINE(concurrency-mt-unsafe, performance-avoid-endl);
    CHECK_RESULT(value_s.value.integer, forceValue)

    return 0;
}

#ifdef IS_VPI

static int baselineValueVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = baselineValue();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkValuesForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkValuesForced();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkValuesReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkValuesReleased();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int forceValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = forceValues();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int releaseValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpiValue;

    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = releaseValues();
    vpi_put_value(href, &vpiValue, NULL, vpiNoDelay);

    return 0;
}

std::array<s_vpi_systf_data, 5> vpi_systf_data
    = {s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$forceValues",
                        (PLI_INT32(*)(PLI_BYTE8*))forceValuesVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releaseValues",
                        (PLI_INT32(*)(PLI_BYTE8*))releaseValuesVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesForced",
                        (PLI_INT32(*)(PLI_BYTE8*))checkValuesForcedVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesReleased",
                        (PLI_INT32(*)(PLI_BYTE8*))checkValuesReleasedVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$baselineValue",
                        (PLI_INT32(*)(PLI_BYTE8*))baselineValueVpi, 0, 0, 0}};

// cver entry
extern "C" void vpi_compat_bootstrap(void) {
    for (s_vpi_systf_data& systf : vpi_systf_data) vpi_register_systf(&systf);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
