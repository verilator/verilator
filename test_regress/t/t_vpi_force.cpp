// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty.
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

// DESCRIPTION: vpi force and release test
//
// This test checks that forcing a signal using vpi_put_value with vpiForceFlag
// sets it to the correct value, and then releasing it with vpiReleaseFlag
// returns it to the initial state.

#include "verilated.h"  // For VL_PRINTF
#include "verilated_sym_props.h"  // For VerilatedVar
#include "verilated_syms.h"  // For VerilatedVarNameMap
#include "verilated_vpi.h"  // For VerilatedVpi::doInertialPuts();

#include "TestSimulator.h"  // For is_verilator()
#include "TestVpi.h"  // For CHECK_RESULT_NZ
#include "vpi_user.h"

#include <algorithm>
#include <memory>  // For std::unique_ptr

namespace {

constexpr int maxAllowedErrorLevel = vpiWarning;
const std::string scopeName = "t.test";

using signalValueTypes = union {
    const char* str;
    PLI_INT32 integer;
    double real;
    const struct t_vpi_vecval* vector;
};

using TestSignal = const struct {
    const char* signalName;
    PLI_INT32 valueType;
    signalValueTypes releaseValue;
    signalValueTypes forceValue;
    std::pair<signalValueTypes, bool>
        partialForceValue;  // No std::optional on C++14, so the bool inside the pair is used to
                            // specify if a partial force should be tested for this signal. For a
                            // partial force, the first part of the signal is left at the release
                            // value, while the second part is forced to the force value.
};

constexpr std::array<TestSignal, 16> TestSignals = {
    TestSignal{"onebit",
               vpiIntVal,
               {.integer = 1},
               {.integer = 0},
               {{}, false}},  // Can't partially force just one bit
    TestSignal{"intval",
               vpiIntVal,
               {.integer = -1431655766},  // 1010...1010
               {.integer = 0x55555555},  // 0101...0101
               {{.integer = -1431677611}, true}},  // 1010...010_010...0101

    TestSignal{"vectorC",
               vpiVectorVal,
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0b10101010, 0}}},
               {.vector = (t_vpi_vecval[]){{0b01010101, 0}}},
               {{.vector = (t_vpi_vecval[]){{0b10100101, 0}}}, true}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{
        "vectorQ",
        vpiVectorVal,
        // NOTE: This is a 62 bit signal, so the first two bits of the MSBs (*second* vecval,
        // since the LSBs come first) are set to 0, hence the 0x2 and 0x1, respectively.

        // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
        {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0}, {0x2AAAAAAAUL, 0}}},  // (00)1010...1010
        {.vector = (t_vpi_vecval[]){{0x55555555UL, 0}, {0x15555555UL, 0}}},  // (00)0101...0101
        {{.vector = (t_vpi_vecval[]){{0xD5555555UL, 0}, {0x2AAAAAAAUL, 0}}},
         true}},  // 1010...010_010...0101
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{"vectorW",
               vpiVectorVal,
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0},  // 1010...1010
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0}}},
               {.vector = (t_vpi_vecval[]){{0x55555555UL, 0},  // 0101...0101
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0}}},
               {{.vector = (t_vpi_vecval[]){{0x55555555UL, 0},  // 1010...010_010...0101
                                            {0x55555555UL, 0},
                                            {0xAAAAAAAAUL, 0},
                                            {0xAAAAAAAAUL, 0}}},
                true}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{"real1",
               vpiRealVal,
               {.real = 1.0},
               {.real = 123456.789},
               {{}, false}},  // reals cannot be packed and individual bits cannot be accessed, so
                              // there is no way to partially force a real signal.

    TestSignal{"textHalf", vpiStringVal, {.str = "Hf"}, {.str = "T2"}, {{.str = "H2"}, true}},
    TestSignal{"textLong",
               vpiStringVal,
               {.str = "Long64b"},
               {.str = "44Four44"},
               {{.str = "Lonur44"}, true}},
    TestSignal{"text",
               vpiStringVal,
               {.str = "Verilog Test module"},
               {.str = "lorem ipsum"},
               {{.str = "Verilog Tesem ipsum"}, true}},

    TestSignal{"binString",
               vpiBinStrVal,
               {.str = "10101010"},
               {.str = "01010101"},
               {{.str = "10100101"}, true}},
    TestSignal{"octString",
               vpiOctStrVal,
               {.str = "25252"},  // 010101010101010
               {.str = "52525"},  // 101010101010101
               {{.str = "25325"}, true}},  // 010101011010101
    TestSignal{"hexString",
               vpiHexStrVal,
               {.str = "aaaaaaaaaaaaaaaa"},  // 1010...1010
               {.str = "5555555555555555"},  // 0101...0101
               {{.str = "aaaaaaaa55555555"}, true}},  // 1010...010_010...0101

    TestSignal{"decStringC",
               vpiDecStrVal,
               {.str = "170"},  // 10101010
               {.str = "85"},  // 01010101
               {{.str = "165"}, true}},  // 10100101
    TestSignal{"decStringS",
               vpiDecStrVal,
               {.str = "43690"},  // 1010...1010
               {.str = "21845"},  // 0101...0101
               {{.str = "43605"}, true}},  // 1010...010_010...0101
    TestSignal{"decStringI",
               vpiDecStrVal,
               {.str = "2863311530"},  // 1010...1010
               {.str = "1431655765"},  // 0101...0101
               {{.str = "2863289685"}, true}},  // 1010...010_010...0101
    TestSignal{"decStringQ",
               vpiDecStrVal,
               {.str = "12297829382473034410"},  // 1010...1010
               {.str = "6148914691236517205"},  // 0101...0101
               {{.str = "12297829381041378645"}, true}},  // 1010...010_010...0101
};

bool vpiCheckErrorLevel(const int maxAllowedErrorLevel) {
    t_vpi_error_info errorInfo{};
    const bool errorOccured = vpi_chk_error(&errorInfo);
    if (VL_UNLIKELY(errorOccured)) {
        VL_PRINTF("%s", errorInfo.message);
        return errorInfo.level > maxAllowedErrorLevel;
    }
    return false;
}

std::pair<const std::string, const bool> vpiGetErrorMessage() {
    t_vpi_error_info errorInfo{};
    const bool errorOccured = vpi_chk_error(&errorInfo);
    return {errorOccured ? errorInfo.message : std::string{}, errorOccured};
}

#ifdef VERILATOR  // m_varsp is Verilator-specific and does not make sense for other simulators
std::unique_ptr<const VerilatedVar> removeSignalFromScope(const std::string& scopeName,
                                                          const std::string& signalName) {
    const VerilatedScope* const scopep = Verilated::threadContextp()->scopeFind(scopeName.c_str());
    if (!scopep) return nullptr;
    VerilatedVarNameMap* const varsp = scopep->varsp();
    const VerilatedVarNameMap::const_iterator foundSignalIt = varsp->find(signalName.c_str());
    if (foundSignalIt == varsp->end()) return nullptr;
    VerilatedVar foundSignal = foundSignalIt->second;
    varsp->erase(foundSignalIt);
    return std::make_unique<const VerilatedVar>(foundSignal);
}

bool insertSignalIntoScope(const std::pair<std::string, std::string>& scopeAndSignalNames,
                           const std::unique_ptr<const VerilatedVar> signal) {
    const std::string& scopeName = scopeAndSignalNames.first;
    const std::string& signalName = scopeAndSignalNames.second;

    const VerilatedScope* const scopep = Verilated::threadContextp()->scopeFind(scopeName.c_str());
    if (!scopep) return false;
    VerilatedVarNameMap* const varsp = scopep->varsp();

    // NOTE: The lifetime of the name inserted into varsp must be the same as the scopep, i.e. the
    // same as threadContextp. Otherwise, the key in the m_varsp map will be a stale pointer.
    // Hence, names of signals being inserted are stored in the static set, and it is assumed that
    // the set's lifetime is the same as the threadContextp.
    static std::set<std::string> insertedSignalNames;
    const auto insertedSignalName = insertedSignalNames.insert(signalName);

    varsp->insert(
        std::pair<const char*, VerilatedVar>{insertedSignalName.first->c_str(), *signal});
    return true;
}

int tryVpiGetWithMissingSignal(const TestVpiHandle& signalToGet,  // NOLINT(misc-misplaced-const)
                               const PLI_INT32 signalFormat,
                               const std::pair<std::string, std::string>& scopeAndSignalNames,
                               const std::string& expectedErrorMessage) {
    const std::string& scopeName = scopeAndSignalNames.first;
    const std::string& signalNameToRemove = scopeAndSignalNames.second;
    std::unique_ptr<const VerilatedVar> removedSignal
        = removeSignalFromScope(scopeName, signalNameToRemove);
    CHECK_RESULT_NZ(removedSignal);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s{.format = signalFormat, .value = {}};

    // Prevent program from terminating, so error message can be collected
    Verilated::fatalOnVpiError(false);
    vpi_get_value(signalToGet, &value_s);
    // Re-enable so tests that should pass properly terminate the simulation on failure
    Verilated::fatalOnVpiError(true);

    std::pair<const std::string, const bool> receivedError = vpiGetErrorMessage();
    const bool errorOccurred = receivedError.second;
    const std::string receivedErrorMessage = receivedError.first;
    CHECK_RESULT_NZ(errorOccurred);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe,performance-avoid-endl)
    CHECK_RESULT(receivedErrorMessage, expectedErrorMessage);
    bool insertSuccess
        = insertSignalIntoScope({scopeName, signalNameToRemove}, std::move(removedSignal));
    CHECK_RESULT_NZ(insertSuccess);  // NOLINT(concurrency-mt-unsafe)
    return 0;
}

int tryVpiPutWithMissingSignal(const s_vpi_value value_s,
                               const TestVpiHandle& signalToPut,  // NOLINT(misc-misplaced-const)
                               const int flag, const std::string& scopeName,
                               const std::string& signalNameToRemove,
                               const std::vector<std::string>& expectedErrorMessageSubstrings) {
    std::unique_ptr<const VerilatedVar> removedSignal
        = removeSignalFromScope(scopeName, signalNameToRemove);
    CHECK_RESULT_NZ(removedSignal);  // NOLINT(concurrency-mt-unsafe)

    // Prevent program from terminating, so error message can be collected
    Verilated::fatalOnVpiError(false);
    vpi_put_value(signalToPut, const_cast<p_vpi_value>(&value_s), nullptr, flag);
    // Re-enable so tests that should pass properly terminate the simulation on failure
    Verilated::fatalOnVpiError(true);

    std::pair<const std::string, const bool> receivedError = vpiGetErrorMessage();
    const bool errorOccurred = receivedError.second;
    const std::string receivedErrorMessage = receivedError.first;
    CHECK_RESULT_NZ(errorOccurred);  // NOLINT(concurrency-mt-unsafe)

    const bool allExpectedErrorSubstringsFound
        = std::all_of(expectedErrorMessageSubstrings.begin(), expectedErrorMessageSubstrings.end(),
                      [receivedErrorMessage](const std::string& expectedSubstring) {
                          return receivedErrorMessage.find(expectedSubstring) != std::string::npos;
                      });
    CHECK_RESULT_NZ(allExpectedErrorSubstringsFound);  // NOLINT(concurrency-mt-unsafe)
    bool insertSuccess
        = insertSignalIntoScope({scopeName, signalNameToRemove}, std::move(removedSignal));
    CHECK_RESULT_NZ(insertSuccess);  // NOLINT(concurrency-mt-unsafe)
    return 0;
}

// Simpler function that expects an exact string instead of a number of substrings, and just a
// signalName instead of a handle.
int expectVpiPutError(const std::string& signalName, s_vpi_value value_s, const int flag,
                      const std::string& expectedErrorMessage) {
    const std::string fullSignalName = std::string{scopeName} + "." + signalName;
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(fullSignalName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // Prevent program from terminating, so error message can be collected
    Verilated::fatalOnVpiError(false);
    vpi_put_value(signalHandle, &value_s, nullptr, flag);
    // Re-enable so tests that should pass properly terminate the simulation on failure
    Verilated::fatalOnVpiError(true);

    std::pair<const std::string, const bool> receivedError = vpiGetErrorMessage();
    const bool errorOccurred = receivedError.second;
    const std::string receivedErrorMessage = receivedError.first;
    CHECK_RESULT_NZ(errorOccurred);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe,performance-avoid-endl)
    CHECK_RESULT(receivedErrorMessage, expectedErrorMessage);
    return 0;
}

#endif

bool vpiValuesEqual(const std::size_t bitCount, const s_vpi_value& first,
                    const s_vpi_value& second) {
    if (first.format != second.format) return false;
    switch (first.format) {
    case vpiIntVal: return first.value.integer == second.value.integer; break;
    case vpiVectorVal: {
        const t_vpi_vecval* const firstVecval = first.value.vector;
        const t_vpi_vecval* const secondVecval = second.value.vector;
        const std::size_t vectorElements = (bitCount + 31) / 32;  // Ceil
        for (std::size_t i{0}; i < vectorElements; ++i) {
            if (firstVecval[i].aval != secondVecval[i].aval) return false;
        }
        return true;
    }
    case vpiRealVal:
        return std::abs(first.value.real - second.value.real)
               < std::numeric_limits<double>::epsilon();
        break;
    case vpiStringVal:
    case vpiBinStrVal:
    case vpiOctStrVal:
    case vpiDecStrVal:
    case vpiHexStrVal: {
        // Same as CHECK_RESULT_CSTR_STRIP, but should return true when equal, false otherwise
        const std::string firstUnpadded = first.value.str + std::strspn(first.value.str, " ");
        return std::string{firstUnpadded} == std::string{second.value.str};
        break;
    }
    default:
        VL_PRINTF("Unsupported value format %i passed to vpiValuesEqual\n", first.format);
        return false;
    }
}

std::unique_ptr<s_vpi_value> vpiValueWithFormat(const PLI_INT32 signalFormat,
                                                const signalValueTypes value) {
    std::unique_ptr<s_vpi_value> value_sp = std::make_unique<s_vpi_value>();
    value_sp->format = signalFormat;

    switch (signalFormat) {
    case vpiIntVal: value_sp->value = {.integer = value.integer}; break;
    case vpiVectorVal: value_sp->value = {.vector = const_cast<p_vpi_vecval>(value.vector)}; break;
    case vpiRealVal: value_sp->value = {.real = value.real}; break;
    case vpiStringVal:
    case vpiBinStrVal:
    case vpiOctStrVal:
    case vpiDecStrVal:
    case vpiHexStrVal: value_sp->value = {.str = const_cast<PLI_BYTE8*>(value.str)}; break;
    default:
        VL_PRINTF("Unsupported value format %i passed to vpiValueWithFormat\n", signalFormat);
        return nullptr;
    }

    return value_sp;
}

int checkValue(const std::string& scopeName, const std::string& testSignalName,
               const PLI_INT32 signalFormat, const signalValueTypes expectedValue) {
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

#ifdef VERILATOR
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiGetWithMissingSignal(
        signalHandle, signalFormat, {scopeName, testSignalName + "__VforceEn"},
        "vl_vpi_get_value: Signal '" + testSignalFullName
            + "' is marked forceable, but force control signals could not be retrieved. Error "
              "message: getForceControlSignals: vpi force or release requested for '"
            + testSignalFullName + "', but vpiHandle '(nil)' of enable signal '"
            + testSignalFullName
            + "__VforceEn' could not be cast to VerilatedVpioVar*. Ensure signal is marked as "
              "forceable"));

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiGetWithMissingSignal(
        signalHandle, signalFormat, {scopeName, testSignalName + "__VforceVal"},
        "vl_vpi_get_value: Signal '" + testSignalFullName
            + "' is marked forceable, but force control signals could not be retrieved. Error "
              "message: getForceControlSignals: vpi force or release requested for '"
            + testSignalFullName + "', but vpiHandle '(nil)' of value signal '"
            + testSignalFullName
            + "__VforceVal' could not be cast to VerilatedVpioVar*. Ensure signal is marked "
              "as "
              "forceable"));
#endif

    std::unique_ptr<s_vpi_value> receivedValueSp = vpiValueWithFormat(signalFormat, {});
    CHECK_RESULT_NZ(receivedValueSp);  // NOLINT(concurrency-mt-unsafe)
    vpi_get_value(signalHandle, receivedValueSp.get());

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedValue);
    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(
        vpiValuesEqual(vpi_get(vpiSize, signalHandle), *receivedValueSp, *expectedValueSp));

    return 0;
}

int forceSignal(const std::string& scopeName, const std::string& testSignalName,
                const PLI_INT32 signalFormat, const signalValueTypes forceValue) {
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    std::unique_ptr<s_vpi_value> value_sp = vpiValueWithFormat(signalFormat, forceValue);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

#ifdef VERILATOR
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiPutWithMissingSignal(
        *value_sp, signalHandle, vpiForceFlag, scopeName, testSignalName + "__VforceEn",
        {"vpi_put_value: Signal '" + testSignalFullName + "' with vpiHandle ",
         // Exact handle address does not matter
         " is marked forceable, but force control signals could not be retrieved. Error "
         "message: getForceControlSignals: vpi force or release requested for '"
             + testSignalFullName + "', but vpiHandle '(nil)' of enable signal '"
             + testSignalFullName
             + "__VforceEn' could not be cast to VerilatedVpioVar*. Ensure signal is marked "
               "as "
               "forceable"}));

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiPutWithMissingSignal(
        *value_sp, signalHandle, vpiForceFlag, scopeName, testSignalName + "__VforceVal",
        {"vpi_put_value: Signal '" + testSignalFullName + "' with vpiHandle ",
         // Exact handle address does not matter
         " is marked forceable, but force control signals could not be retrieved. Error "
         "message: getForceControlSignals: vpi force or release requested for '"
             + testSignalFullName + "', but vpiHandle '(nil)' of value signal '"
             + testSignalFullName
             + "__VforceVal' could not be cast to VerilatedVpioVar*. Ensure signal is marked "
               "as "
               "forceable"}));
#endif

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int releaseSignal(const std::string& scopeName, const std::string& testSignalName,
                  const PLI_INT32 signalFormat,
                  const std::pair<signalValueTypes, signalValueTypes> releaseValue) {
    const signalValueTypes expectedReleaseValueInit = releaseValue.first;
    const signalValueTypes expectedReleaseValue = releaseValue.second;
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // initialize value_sp to the value that is *not* expected (i.e. forceValue for continuously
    // assigned signals, and releaseValue for clocked signals) to ensure the test fails if value_sp
    // is not updated
    std::unique_ptr<s_vpi_value> value_sp
        = vpiValueWithFormat(signalFormat, expectedReleaseValueInit);
    CHECK_RESULT_NZ(value_sp);  //NOLINT(concurrency-mt-unsafe)

#ifdef VERILATOR
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiPutWithMissingSignal(
        *value_sp, signalHandle, vpiReleaseFlag, scopeName, testSignalName + "__VforceEn",
        {"vpi_put_value: Signal '" + testSignalFullName + "' with vpiHandle ",
         // Exact handle address does not matter
         " is marked forceable, but force control signals could not be retrieved. Error "
         "message: getForceControlSignals: vpi force or release requested for '"
             + testSignalFullName + "', but vpiHandle '(nil)' of enable signal '"
             + testSignalFullName
             + "__VforceEn' could not be cast to VerilatedVpioVar*. Ensure signal is marked "
               "as "
               "forceable"}));

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(tryVpiPutWithMissingSignal(
        *value_sp, signalHandle, vpiReleaseFlag, scopeName, testSignalName + "__VforceVal",
        {"vpi_put_value: Signal '" + testSignalFullName + "' with vpiHandle ",
         // Exact handle address does not matter
         " is marked forceable, but force control signals could not be retrieved. Error "
         "message: getForceControlSignals: vpi force or release requested for '"
             + testSignalFullName + "', but vpiHandle '(nil)' of value signal '"
             + testSignalFullName
             + "__VforceVal' could not be cast to VerilatedVpioVar*. Ensure signal is marked "
               "as "
               "forceable"}));
#endif

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiReleaseFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

#ifdef XRUN
    // Special case: real1Continuously is continuously assigned, but in xrun the value for the
    // s_vpi_value output parameter upon releasing using vpi_put_value is *not* the releaseValue as
    // expected, but the forceValue. This ifdef ensures the test still passes on xrun.
    const std::unique_ptr<s_vpi_value> expectedValueSp = vpiValueWithFormat(
        signalFormat, testSignalName == "real1Continuously" ? signalValueTypes{.real = 123456.789}
                                                            : expectedReleaseValue);
#else
    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedReleaseValue);
#endif
    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), *value_sp, *expectedValueSp));

    return 0;
}

}  // namespace

extern "C" int checkValuesForced(void) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                checkValue(scopeName, signal.signalName, signal.valueType, signal.forceValue));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            const std::string continouslyAssignedSignal
                = std::string{signal.signalName} + "Continuously";
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                checkValue(scopeName, continouslyAssignedSignal, signal.valueType,
                           signal.forceValue));
            return 0;
        }));
    return 0;
}

extern "C" int checkValuesPartiallyForced(void) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.partialForceValue.second)
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, signal.signalName, signal.valueType,
                               signal.partialForceValue.first));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.partialForceValue.second)
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                               signal.valueType, signal.partialForceValue.first));
            return 0;
        }));
    return 0;
}

extern "C" int checkValuesReleased(void) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                checkValue(scopeName, signal.signalName, signal.valueType, signal.releaseValue));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                           signal.valueType, signal.releaseValue));
            return 0;
        }));
    return 0;
}

#ifdef VERILATOR
// This function only makes sense with Verilator, because its purpose is testing error messages
// emitted from verilated_vpi.
extern "C" int tryInvalidPutOperations() {
    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "str1", {.format = vpiStringVal, .value = {.str = const_cast<PLI_BYTE8*>("foo")}},
        vpiForceFlag,
        "vpi_put_value used with vpiForceFlag on non-forceable signal 't.test.str1'"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "octString", {.format = vpiOctStrVal, .value = {.str = const_cast<PLI_BYTE8*>("123A")}},
        vpiForceFlag,
        "vpi_put_value: Non octal character 'A' in '123A' as value "
        "vpiOctStrVal for t.test.octString__VforceVal"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "decStringC", {.format = vpiDecStrVal, .value = {.str = const_cast<PLI_BYTE8*>("A123")}},
        vpiForceFlag,
        "vpi_put_value: Parsing failed for 'A123' as value vpiDecStrVal for "
        "t.test.decStringC__VforceVal"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "decStringC", {.format = vpiDecStrVal, .value = {.str = const_cast<PLI_BYTE8*>("123A")}},
        vpiForceFlag,
        "vpi_put_value: Trailing garbage 'A' in '123A' as value vpiDecStrVal for "
        "t.test.decStringC__VforceVal"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "hexString", {.format = vpiHexStrVal, .value = {.str = const_cast<PLI_BYTE8*>("12AG")}},
        vpiForceFlag,
        "vpi_put_value: Non hex character 'G' in '12AG' as value vpiHexStrVal for "
        "t.test.hexString__VforceVal"));

    // vop was replaced with baseSignalVop in vpi_put_value, so these tests are required to hit the
    // test coverage target and ensure the error messages still work.
    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "onebit", {.format = vpiRawFourStateVal, .value = {}}, vpiForceFlag,
        "vl_check_format: Unsupported format (vpiRawFourStateVal) for t.test.onebit"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "onebit", {.format = vpiSuppressVal, .value = {}}, vpiForceFlag,
        "vpi_put_value: Unsupported format (vpiSuppressVal) as "
        "requested for t.test.onebit__VforceVal"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "onebit", {.format = vpiStringVal, .value = {}}, vpiInertialDelay,
        "vpi_put_value: Unsupported p_vpi_value as requested for 't.test.onebit' with "
        "vpiInertialDelay"));

    return 0;
}

// This function is just needed for hitting the test coverage target for verilated_vpi.cpp and
// ensuring that vpi_put_value to a string without vpiForceFlag still works.
extern "C" int putString() {
    const std::string stringName = std::string{scopeName} + ".str1";
    TestVpiHandle const stringSignalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(stringName.c_str()), nullptr);
    CHECK_RESULT_NZ(stringSignalHandle);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s{.format = vpiStringVal, .value = {.str = const_cast<PLI_BYTE8*>("foo")}};

    vpi_put_value(stringSignalHandle, &value_s, nullptr, vpiNoDelay);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    value_s.value.str
        = const_cast<PLI_BYTE8*>("bar");  // Ensure that test fails if value_s is not updated

    vpi_get_value(stringSignalHandle, &value_s);
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    s_vpi_value expectedValueS{.format = vpiStringVal,
                               .value = {.str = const_cast<PLI_BYTE8*>("foo")}};
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, stringSignalHandle), value_s, expectedValueS));

    return 0;
}

// This function is just needed for hitting the test coverage target for verilated_vpi.cpp and
// ensuring that vpiInertialDelay still works after renaming vop to baseSignalVop.
extern "C" int putInertialDelay() {
    const std::string fullSignalName = std::string{scopeName} + ".delayed";
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(fullSignalName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    constexpr int delayedValue = 123;
    s_vpi_value value_s{.format = vpiIntVal, .value = {.integer = delayedValue}};
    s_vpi_time time{.type = vpiSimTime, .high = 0, .low = 0, .real = {}};
    vpi_put_value(signalHandle, &value_s, &time, vpiInertialDelay);
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    // Check that the put had no immediate effect

    vpi_get_value(signalHandle, &value_s);
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    s_vpi_value expectedValueS{.format = vpiIntVal, .value = {.integer = 0}};
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), value_s, expectedValueS));

    // Check that the put is executed upon doInertialPuts
    VerilatedVpi::doInertialPuts();

    value_s.value.integer = 0;  // Ensure that test fails if value_s is not updated
    vpi_get_value(signalHandle, &value_s);
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    expectedValueS.value.integer = delayedValue;
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), value_s, expectedValueS));

    return 0;
}
#endif

extern "C" int forceValues(void) {
    if (!TestSimulator::is_verilator()) {
#ifdef VERILATOR
        printf("TestSimulator indicating not verilator, but VERILATOR macro is defined\n");
        return 1;
#endif
    }

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                forceSignal(scopeName, signal.signalName, signal.valueType, signal.forceValue));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                forceSignal(scopeName, std::string{signal.signalName} + "Continuously",
                            signal.valueType, signal.forceValue));
            return 0;
        }));
    return 0;
}

extern "C" int releaseValues(void) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                releaseSignal(scopeName, signal.signalName, signal.valueType,
                              {signal.releaseValue, signal.forceValue}));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                releaseSignal(scopeName, std::string{signal.signalName} + "Continuously",
                              signal.valueType, {signal.forceValue, signal.releaseValue}));
            return 0;
        }));
    return 0;
}

extern "C" int releasePartiallyForcedValues(void) {
    // Skip any values that cannot be partially forced. Can't just reuse releaseValues, because the
    // output argument s_vpi_value of vpi_put_value with vpiReleaseFlag differs depending on
    // whether or not a signal was forced before, and not all signals are forced in the partial
    // forcing test.

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.partialForceValue.second)
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    releaseSignal(scopeName, signal.signalName, signal.valueType,
                                  {signal.releaseValue, signal.partialForceValue.first}));
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.partialForceValue.second)
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    releaseSignal(scopeName, std::string{signal.signalName} + "Continuously",
                                  signal.valueType,
                                  {signal.partialForceValue.first, signal.releaseValue}));
            return 0;
        }));
    return 0;
}

#ifdef IS_VPI

static int checkValuesForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkValuesForced();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkValuesPartiallyForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkValuesPartiallyForced();
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

static int releasePartiallyForcedValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpiValue;

    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = releasePartiallyForcedValues();
    vpi_put_value(href, &vpiValue, NULL, vpiNoDelay);

    return 0;
}

std::array<s_vpi_systf_data, 6> vpi_systf_data
    = {s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$forceValues",
                        (PLI_INT32(*)(PLI_BYTE8*))forceValuesVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releaseValues",
                        (PLI_INT32(*)(PLI_BYTE8*))releaseValuesVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releasePartiallyForcedValues",
                        (PLI_INT32(*)(PLI_BYTE8*))releasePartiallyForcedValuesVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesForced",
                        (PLI_INT32(*)(PLI_BYTE8*))checkValuesForcedVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesPartiallyForced",
                        (PLI_INT32(*)(PLI_BYTE8*))checkValuesPartiallyForcedVpi, 0, 0, 0},
       s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesReleased",
                        (PLI_INT32(*)(PLI_BYTE8*))checkValuesReleasedVpi, 0, 0, 0}};

// cver entry
extern "C" void vpi_compat_bootstrap(void) {
    for (s_vpi_systf_data& systf : vpi_systf_data) vpi_register_systf(&systf);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
