// ======================================================================
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Christian Hecken
// SPDX-License-Identifier: CC0-1.0
// ======================================================================

// DESCRIPTION: vpi force and release test
//
// This test checks that forcing a signal using vpi_put_value with vpiForceFlag
// sets it to the correct value, and then releasing it with vpiReleaseFlag
// returns it to the initial state.

#include "verilated.h"  // For VL_PRINTF
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

using BitRange = const struct {
    int lo;
    int hi;
};

using PartialValue = const struct {
    signalValueTypes fullSignalForceValue;  // The value the signal has after partial forcing
    signalValueTypes fullSignalReleaseValue;  // The value the signal has after partial releasing
    signalValueTypes partialForceValue;  // *Only* the value of the bits being forced
    signalValueTypes
        partialReleaseValue;  // *Only* the value of the bits being released (after release)
    BitRange bitRange;  // NOLINT(cppcoreguidelines-avoid-const-or-ref-data-members)
};

using BitValue = const struct {
    signalValueTypes fullSignalForceValue;  // The value the signal has after forcing one bit
    signalValueTypes fullSignalReleaseValue;  // The value the signal has after all bits were
                                              // forced and just one bit is released
    PLI_INT32
    valueType;  // Xcelium refuses to return non-printable characters for vpiStringVal, so for
                // strings, a different format must be used to set individual bits to 0 or 1
    // Assumption is that fullSignalForceValue and fullSignalReleaseValue use the same type as the
    // parent TestSignal, and bitForceValue and bitReleaseValue use the valueType specified here.
    signalValueTypes bitForceValue;  // *Only* the value of the single bit being forced
    signalValueTypes bitReleaseValue;  // *Only* the value of the single bit after being released
    int bitIndex;
};

using TestSignal = const struct {
    const char* signalName;
    PLI_INT32 valueType;
    std::vector<int> packedIndices;  // Allows access into multidimensional packed vectors
    signalValueTypes releaseValue;
    signalValueTypes forceValue;
    bool shouldTestPartialForce;
    // No std::optional on C++14, so shouldTestPartialForce is used to
    // specify if a partial force should be tested for this signal. For a
    // partial force, the first part of the signal is left at the release
    // value, while the second part is forced to the force value.
    PartialValue partialValue;  // NOLINT(cppcoreguidelines-avoid-const-or-ref-data-members)
    BitValue bitValue;  // NOLINT(cppcoreguidelines-avoid-const-or-ref-data-members)
};

using ReleaseValue = const struct {
    signalValueTypes
        expectedReleaseValueInit;  // Something that's *not* the expected release value, to ensure
                                   // the test fails if the value is not updated
    signalValueTypes expectedReleaseValue;
};

enum class BitIndexingMethod : uint8_t {
    ByIndex = 0,  // vpi_handle_by_index
    ByName = 1,  // vpi_handle_by_name
};

enum class DimIndexingMethod : uint8_t {
    ByRepeatedIndex = 0,  // Repeatedly use vpi_handle_by_index
    ByMultiIndex = 1,  // vpi_handle_by_multi_index
    ByName = 2,  // vpi_handle_by_name
};

enum class Direction : uint8_t {
    Descending = 0,  // [hi:lo]
    Ascending = 1,  // [lo:hi]
};

#ifndef IVERILOG
const std::array<TestSignal, 36> TestSignals = {
#else  // Multidimensional packed arrays aren't tested in Icarus
const std::array<TestSignal, 17> TestSignals = {
#endif
    TestSignal{"onebit",
               vpiIntVal,
               {},
               {.integer = 1},
               {.integer = 0},
               false,
               {},  // Can't partially force just one bit
               {}},  // Can't index into a single bit
    TestSignal{"intval",
               vpiIntVal,
               {},
               {.integer = -1431655766},  // 1010...1010
               {.integer = 0x55555555},  // 0101...0101
               true,
               {{.integer = -1431677611},  // 1010...010_010...0101
                {.integer = 0x5555AAAA},
                {.integer = 0x5555},
                {.integer = 0xAAAA},
                {.lo = 0, .hi = 15}},
               {{.integer = -1431655765},  // 1010...1011
                {.integer = 0x55555554},  // 0101...0100
                vpiIntVal,
                {.integer = 1},
                {.integer = 0},
                0}},

    TestSignal{"vectorC",
               vpiVectorVal,
               {},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0b10101010, 0}}},
               {.vector = (t_vpi_vecval[]){{0b01010101, 0}}},
               true,
               {{.vector = (t_vpi_vecval[]){{0b10100101, 0}}},
                {.vector = (t_vpi_vecval[]){{0b01011010, 0}}},
                {.vector = (t_vpi_vecval[]){{0x5, 0}}},
                {.vector = (t_vpi_vecval[]){{0xA, 0}}},
                {.lo = 0, .hi = 3}},
               {{.vector = (t_vpi_vecval[]){{0b10101011, 0}}},
                {.vector = (t_vpi_vecval[]){{0b01010100, 0}}},
                vpiVectorVal,
                {.vector = (t_vpi_vecval[]){{0b1, 0}}},
                {.vector = (t_vpi_vecval[]){{0b0, 0}}},
                0}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{"forcedNonForceable",
               vpiVectorVal,
               {},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0b10101010, 0}}},
               {.vector = (t_vpi_vecval[]){{0b01010101, 0}}},
               true,
               {{.vector = (t_vpi_vecval[]){{0b10100101, 0}}},
                {.vector = (t_vpi_vecval[]){{0b01011010, 0}}},
                {.vector = (t_vpi_vecval[]){{0x5, 0}}},
                {.vector = (t_vpi_vecval[]){{0xA, 0}}},
                {.lo = 0, .hi = 3}},
               {{.vector = (t_vpi_vecval[]){{0b10101011, 0}}},
                {.vector = (t_vpi_vecval[]){{0b01010100, 0}}},
                vpiVectorVal,
                {.vector = (t_vpi_vecval[]){{0b1, 0}}},
                {.vector = (t_vpi_vecval[]){{0b0, 0}}},
                0}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{
        "vectorQ",
        vpiVectorVal,
        {},
        // NOTE: This is a 62 bit signal, so the first two bits of the MSBs (*second* vecval,
        // since the LSBs come first) are set to 0, hence the 0x2 and 0x1, respectively.

        // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
        {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0}, {0x2AAAAAAAUL, 0}}},  // (00)1010...1010
        {.vector = (t_vpi_vecval[]){{0x55555555UL, 0}, {0x15555555UL, 0}}},  // (00)0101...0101
        true,
        {{.vector
          = (t_vpi_vecval[]){{0xD5555555UL, 0}, {0x2AAAAAAAUL, 0}}},  // 1010...010_010...0101
         {.vector = (t_vpi_vecval[]){{0x2AAAAAAAUL, 0}, {0x15555555UL, 0}}},
         {.vector = (t_vpi_vecval[]){{0x55555555, 0}}},
         {.vector = (t_vpi_vecval[]){{0x2AAAAAAAUL, 0}}},
         {.lo = 0, .hi = 30}},
        {{.vector = (t_vpi_vecval[]){{0xAAAAAAABUL, 0}, {0x2AAAAAAAUL, 0}}},  // (00)1010...1011
         {.vector = (t_vpi_vecval[]){{0x55555554UL, 0}, {0x15555555UL, 0}}},  // (00)0101...0100
         vpiVectorVal,
         {.vector = (t_vpi_vecval[]){{0b1, 0}}},
         {.vector = (t_vpi_vecval[]){{0b0, 0}}},
         0}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{"vectorW",
               vpiVectorVal,
               {},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0},  // 1010...1010
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0}}},
               {.vector = (t_vpi_vecval[]){{0x55555555UL, 0},  // 0101...0101
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0}}},
               true,
               {{.vector = (t_vpi_vecval[]){{0x55555555UL, 0},  // 1010...010_010...0101
                                            {0x55555555UL, 0},
                                            {0xAAAAAAAAUL, 0},
                                            {0xAAAAAAAAUL, 0}}},
                {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0},
                                            {0xAAAAAAAAUL, 0},
                                            {0x55555555UL, 0},
                                            {0x55555555UL, 0}}},
                {.vector = (t_vpi_vecval[]){{0x55555555UL, 0}, {0x55555555UL, 0}}},
                {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0}, {0xAAAAAAAAUL, 0}}},
                {.lo = 0, .hi = 63}},
               {{.vector = (t_vpi_vecval[]){{0xAAAAAAABUL, 0},  // 1010...1011
                                            {0xAAAAAAAAUL, 0},
                                            {0xAAAAAAAAUL, 0},
                                            {0xAAAAAAAAUL, 0}}},
                {.vector = (t_vpi_vecval[]){{0x55555554UL, 0},  // 0101...0100
                                            {0x55555555UL, 0},
                                            {0x55555555UL, 0},
                                            {0x55555555UL, 0}}},
                vpiVectorVal,
                {.vector = (t_vpi_vecval[]){{0b1, 0}}},
                {.vector = (t_vpi_vecval[]){{0b0, 0}}},
                0}},
    // NOLINTEND (cppcoreguidelines-avoid-c-arrays)

    TestSignal{"real1",
               vpiRealVal,
               {},
               {.real = 1.0},
               {.real = 123456.789},
               false,
               {},  // reals cannot be packed and individual bits cannot be accessed,so there is no
                    // way to partially force a real signal.
               {}},

    TestSignal{"textHalf",
               vpiStringVal,
               {},
               {.str = "Hf"},
               {.str = "T3"},
               true,
               {{.str = "H3"}, {.str = "Tf"}, {.str = "3"}, {.str = "f"}, {.lo = 0, .hi = 7}},
               {{.str = "Hg"},
                {.str = "T2"},
#ifndef XRUN
                vpiStringVal,
                {.str = "\1"},  // "f" = 0b0110_0110, so force LSB to 1
                {.str = ""},  // Only null terminator
#else
                vpiIntVal,
                {.integer = 1},
                {.integer = 0},
#endif
                0}},
    TestSignal{"textLong",
               vpiStringVal,
               {},
               {.str = "Long64b"},
               {.str = "44Four44"},
               true,
               {{.str = "Lonur44"},
                {.str = "44Fog64b"},
                {.str = "ur44"},
                {.str = "g64b"},
                {.lo = 0, .hi = 31}},
               {{.str = "Long64`"},
                {.str = "44Four46"},  // "4" = 00110100, so release second-to-last bit to 1 -> "6"
#ifndef XRUN
                vpiStringVal,
                {.str = ""},  // "b" = 0b01100010, so force second-to-last bit to 0 -> "`"
                {.str = "\1"},
#else
                vpiIntVal,
                {.integer = 0},
                {.integer = 1},
#endif
                1}},  // "b" and "4" both have 0 LSB, so force bit 1 instead to see a difference
    TestSignal{"text",
               vpiStringVal,
               {},
               {.str = "Verilog Test module"},
               {.str = "lorem ipsum"},
               true,
               {{.str = "Verilog Torem ipsum"},
                {.str = "lest module"},
                {.str = "orem ipsum"},
                {.str = "est module"},
                {.lo = 0, .hi = 79}},
               {{.str = "Verilog Test modulm"},  // "e" = 0b01100101, force bit 3 to 1 -> "m"
                {.str = "lorem ipsue"},  // "m" = 0b01101101, release bit 3 to 0 -> "e"
#ifndef XRUN
                vpiStringVal,
                {.str = "\1"},
                {.str = ""},
#else
                vpiIntVal,
                {.integer = 1},
                {.integer = 0},
#endif
                3}},  // Bits 0 through 2 for "m" and "e" are identical, so force bit 3 to see a
                      // difference

    TestSignal{
        "binString",
        vpiBinStrVal,
        {},
        {.str = "10101010"},
        {.str = "01010101"},
        true,
        {{.str = "10100101"},
         {.str = "01011010"},
         {.str = "0101"},
         {.str = "1010"},
         {.lo = 0, .hi = 3}},
        {{.str = "10101011"}, {.str = "01010100"}, vpiBinStrVal, {.str = "1"}, {.str = "0"}, 0}},
    TestSignal{
        "octString",
        vpiOctStrVal,
        {},
        {.str = "25252"},  // 010101010101010
        {.str = "52525"},  // 101010101010101
        true,
        {{.str = "25325"},  // 010101011010101
         {.str = "52452"},  // 101010100101010
         {.str = "125"},
         {.str = "052"},  // [xx]0101010 - note: the first character is 0 even though the actual
                          // triplet at that point in the signal would be `100`, because the bit
                          // select extracts only bits 0 through 6, and the 1 would be at bit 8.
         {.lo = 0, .hi = 6}},
        {{.str = "25253"},  // 010101010101011
         {.str = "52524"},  // 101010101010100
         vpiOctStrVal,
         {.str = "1"},
         {.str = "0"},
         0}},
    TestSignal{"hexString",
               vpiHexStrVal,
               {},
               {.str = "aaaaaaaaaaaaaaaa"},  // 1010...1010
               {.str = "5555555555555555"},  // 0101...0101
               true,
               {{.str = "aaaaaaaa55555555"},  // 1010...010_010...0101
                {.str = "55555555aaaaaaaa"},
                {.str = "55555555"},
                {.str = "aaaaaaaa"},
                {.lo = 0, .hi = 31}},
               {{.str = "aaaaaaaaaaaaaaab"},  // 1010...1011
                {.str = "5555555555555554"},  // 0101...0100
                vpiHexStrVal,
                {.str = "1"},
                {.str = "0"},
                0}},

    TestSignal{"decStringC",
               vpiDecStrVal,
               {},
               {.str = "170"},  // 10101010
               {.str = "85"},  // 01010101
               true,
               {{.str = "165"},  // 10100101
                {.str = "90"},  // 01011010
                {.str = "5"},  // 0101
                {.str = "10"},  // 1010
                {.lo = 0, .hi = 3}},
               {{.str = "171"},  // 10101011
                {.str = "84"},  // 01010100
                vpiDecStrVal,
                {.str = "1"},
                {.str = "0"},
                0}},
    TestSignal{"decStringS",
               vpiDecStrVal,
               {},
               {.str = "43690"},  // 1010...1010
               {.str = "21845"},  // 0101...0101
               true,
               {{.str = "43605"},  // 1010...010_010...0101
                {.str = "21930"},  // 0101...101_101...1010
                {.str = "85"},  // 0b01010101
                {.str = "170"},  // 0b10101010
                {.lo = 0, .hi = 7}},
               {{.str = "43691"},  // 1010...1011
                {.str = "21844"},  // 0101...0100
                vpiDecStrVal,
                {.str = "1"},
                {.str = "0"},
                0}},
    TestSignal{"decStringI",
               vpiDecStrVal,
               {},
               {.str = "2863311530"},  // 1010...1010
               {.str = "1431655765"},  // 0101...0101
               true,
               {{.str = "2863289685"},  // 1010...010_010...0101
                {.str = "1431677610"},  // 0101...101_101...1010
                {.str = "21845"},  // 0101...0101
                {.str = "43690"},  // 1010...1010
                {.lo = 0, .hi = 15}},
               {{.str = "2863311531"},  // 1010...1011
                {.str = "1431655764"},  // 0101...0100
                vpiDecStrVal,
                {.str = "1"},
                {.str = "0"},
                0}},
    TestSignal{"decStringQ",
               vpiDecStrVal,
               {},
               {.str = "12297829382473034410"},  // 1010...1010
               {.str = "6148914691236517205"},  // 0101...0101
               true,
               {{.str = "12297829381041378645"},  // 1010...010_010...0101
                {.str = "6148914692668172970"},  // 0101...101_101...1010
                {.str = "1431655765"},  // 0x55555555
                {.str = "2863311530"},  // 0xAAAAAAAA
                {.lo = 0, .hi = 31}},
               {{.str = "12297829382473034411"},  // 1010...1010
                {.str = "6148914691236517204"},  // 0101...0100
                vpiDecStrVal,
                {.str = "1"},
                {.str = "0"},
                0}},

#ifndef IVERILOG
    // Force the entire 2d packed array (no partial forcing possible since part selection of
    // individual bits is only possible in the last dimension)
    TestSignal{"packed2dC",
               vpiIntVal,
               {},  // No indexing, force entire array
               {.integer = 0xAA},
               {.integer = 0x55},
               false,
               {},
               {}},
    TestSignal{
        "packed2dS", vpiIntVal, {}, {.integer = 0xAAAA}, {.integer = 0x5555}, false, {}, {}},
    TestSignal{"packed2dI",
               vpiIntVal,
               {},
               {.integer = 0xAAAAAA},  // 24 bit
               {.integer = 0x555555},
               false,
               {},
               {}},
    TestSignal{"packed2dQ",
               vpiVectorVal,
               {},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0}, {0xAAAAAAAAUL, 0}}},
               {.vector = (t_vpi_vecval[]){{0x55555555UL, 0}, {0x55555555UL, 0}}},
               // NOLINTEND (cppcoreguidelines-avoid-c-arrays)
               false,
               {},
               {}},
    TestSignal{"packed2dW",
               vpiVectorVal,
               {},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0}}},
               {.vector = (t_vpi_vecval[]){{0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0}}},
               // NOLINTEND (cppcoreguidelines-avoid-c-arrays)
               false,
               {},
               {}},

    // Index into the first dimension and attempt to force all elements in it.
    // Should have the same effect as forcing the entire packed2d array.
    TestSignal{"packed3dS",
               vpiIntVal,
               {-2},  // Index into second element of the first dimension (defined as [-1:-2]),
                      // leaving a 2D packed array of [1:0][1:0] with 4 elements of width 2 each
               {.integer = 0xAA},
               {.integer = 0x55},
               false,
               {},
               {}},
    TestSignal{
        "packed3dI", vpiIntVal, {-2}, {.integer = 0xAAAA}, {.integer = 0x5555}, false, {}, {}},
    TestSignal{
        "packed3dQ", vpiIntVal, {-2}, {.integer = 0xAAAAAA}, {.integer = 0x555555}, false, {}, {}},
    TestSignal{"packed3dW",
               vpiVectorVal,
               {-2},
               // NOLINTBEGIN (cppcoreguidelines-avoid-c-arrays)
               {.vector = (t_vpi_vecval[]){{0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0},
                                           {0xAAAAAAAAUL, 0}}},
               {.vector = (t_vpi_vecval[]){{0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0},
                                           {0x55555555UL, 0}}},
               // NOLINTEND (cppcoreguidelines-avoid-c-arrays)
               false,
               {},
               {}},

    // Attempt to force only one element in the 4D vectors, and also attempt partial and bit
    // forcing
    TestSignal{
        "packed4dC",  // 2-bit elements
        vpiIntVal,
        {-3, 2, -1, 2},
        {.integer = 0b10},
        {.integer = 0b01},
        true,
        {{.integer = 0b11},
         {.integer = 0b00},
         {.integer = 0b1},
         {.integer = 0b0},
         {.lo = -1, .hi = -1}},
        {{.integer = 0b11}, {.integer = 0b00}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, -1}},
    TestSignal{
        "packed4dS",  // 4-bit elements
        vpiIntVal,
        {-3, 2, -1, 2},
        {.integer = 0xA},
        {.integer = 0x5},
        true,
        {{.integer = 0b1001},
         {.integer = 0b0110},
         {.integer = 0b01},
         {.integer = 0b10},
         {.lo = -3, .hi = -2}},
        {{.integer = 0xB}, {.integer = 0x4}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, -3}},
    TestSignal{
        "packed4dI",  // 8-bit elements
        vpiIntVal,
        {-3, 2, -1, 2},
        {.integer = 0xAA},
        {.integer = 0x55},
        true,
        {{.integer = 0xA5},
         {.integer = 0x5A},
         {.integer = 0x5},
         {.integer = 0xA},
         {.lo = -7, .hi = -4}},
        {{.integer = 0xAB}, {.integer = 0x54}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, -7}},
    TestSignal{"packed4dQ",  // 16-bit elements
               vpiIntVal,
               {-3, 2, -1, 2},
               {.integer = 0xAAAA},
               {.integer = 0x5555},
               true,
               {{.integer = 0xAA55},
                {.integer = 0x55AA},
                {.integer = 0x55},
                {.integer = 0xAA},
                {.lo = -15, .hi = -8}},
               {{.integer = 0xAAAB},
                {.integer = 0x5554},
                vpiIntVal,
                {.integer = 0b1},
                {.integer = 0b0},
                -15}},
    TestSignal{"packed4dW",  // 32-bit elements
               vpiIntVal,
               {-3, 2, -1, 2},
               {.integer = static_cast<PLI_INT32>(0xAAAAAAAA)},
               {.integer = 0x55555555},
               true,
               {{.integer = static_cast<PLI_INT32>(0xAAAA5555)},
                {.integer = 0x5555AAAA},
                {.integer = 0x5555},
                {.integer = 0xAAAA},
                {.lo = -31, .hi = -16}},
               {{.integer = static_cast<PLI_INT32>(0xAAAAAAAB)},
                {.integer = 0x55555554},
                vpiIntVal,
                {.integer = 0b1},
                {.integer = 0b0},
                -31}},

    // Same elements as with packed4d* assuming identical data layout, but with ascending indices
    TestSignal{
        "ascPacked4dC",  // 2-bit elements
        vpiIntVal,
        {-3, 2, -1, 5},
        {.integer = 0b10},
        {.integer = 0b01},
        true,
        {{.integer = 0b11},
         {.integer = 0b00},
         {.integer = 0b1},
         {.integer = 0b0},
         {.lo = 9, .hi = 9}},
        {{.integer = 0b11}, {.integer = 0b00}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, 9}},
    TestSignal{
        "ascPacked4dS",  // 4-bit elements
        vpiIntVal,
        {-3, 2, -1, 5},
        {.integer = 0xA},
        {.integer = 0x5},
        true,
        {{.integer = 0b1001},
         {.integer = 0b0110},
         {.integer = 0b01},
         {.integer = 0b10},
         {.lo = 10, .hi = 11}},
        {{.integer = 0xB}, {.integer = 0x4}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, 11}},
    TestSignal{
        "ascPacked4dI",  // 8-bit elements
        vpiIntVal,
        {-3, 2, -1, 5},
        {.integer = 0xAA},
        {.integer = 0x55},
        true,
        {{.integer = 0xA5},
         {.integer = 0x5A},
         {.integer = 0x5},
         {.integer = 0xA},
         {.lo = 12, .hi = 15}},
        {{.integer = 0xAB}, {.integer = 0x54}, vpiIntVal, {.integer = 0b1}, {.integer = 0b0}, 15}},
    TestSignal{"ascPacked4dQ",  // 16-bit elements
               vpiIntVal,
               {-3, 2, -1, 5},
               {.integer = 0xAAAA},
               {.integer = 0x5555},
               true,
               {{.integer = 0xAA55},
                {.integer = 0x55AA},
                {.integer = 0x55},
                {.integer = 0xAA},
                {.lo = 16, .hi = 23}},
               {{.integer = 0xAAAB},
                {.integer = 0x5554},
                vpiIntVal,
                {.integer = 0b1},
                {.integer = 0b0},
                23}},
    TestSignal{"ascPacked4dW",  // 32-bit elements
               vpiIntVal,
               {-3, 2, -1, 5},
               {.integer = static_cast<PLI_INT32>(0xAAAAAAAA)},
               {.integer = 0x55555555},
               true,
               {{.integer = static_cast<PLI_INT32>(0xAAAA5555)},
                {.integer = 0x5555AAAA},
                {.integer = 0x5555},
                {.integer = 0xAAAA},
                {.lo = 24, .hi = 39}},
               {{.integer = static_cast<PLI_INT32>(0xAAAAAAAB)},
                {.integer = 0x55555554},
                vpiIntVal,
                {.integer = 0b1},
                {.integer = 0b0},
                39}},
#endif
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

#ifdef VERILATOR
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

int checkHandleValue(const vpiHandle handle,  //NOLINT(misc-misplaced-const)
                                              // Raw handle because this function should not
                                              // release the handle when it ends
                     const PLI_INT32 signalFormat, const signalValueTypes expectedValue) {
    std::unique_ptr<s_vpi_value> receivedValueSp = vpiValueWithFormat(signalFormat, {});
    CHECK_RESULT_NZ(receivedValueSp);  // NOLINT(concurrency-mt-unsafe)
    vpi_get_value(handle, receivedValueSp.get());

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedValue);
    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, handle), *receivedValueSp, *expectedValueSp));

    return 0;
}

int checkValue(const std::string& scopeName, const std::string& testSignalName,
               const PLI_INT32 signalFormat, const signalValueTypes expectedValue) {
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};

    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    CHECK_RESULT_Z(checkHandleValue(signalHandle, signalFormat, expectedValue));

    return 0;
}

auto getDimIndexString(const std::vector<int>& indices) {
    std::string indexString;
    for (const int index : indices) { indexString += "[" + std::to_string(index) + "]"; }
    return indexString;
};

auto getBitIndexString(const int index) { return "[" + std::to_string(index) + "]"; };

auto getPartSelectString(const int hi,  // NOLINT(readability-identifier-length)
                         const int lo,  // NOLINT(readability-identifier-length)
                         const Direction direction) {
    return direction == Direction::Descending
               ? "[" + std::to_string(hi) + ":" + std::to_string(lo) + "]"
               : "[" + std::to_string(lo) + ":" + std::to_string(hi) + "]";
};

TestVpiHandle getDimIndexedSignalHandle(const std::string& scopeName,
                                        const std::string& testSignalName,
                                        const std::vector<int>& indices,
                                        const DimIndexingMethod dimIndexingMethod) {
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};

    vpiHandle signalHandle
        = nullptr;  // Use a raw vpiHandle here so that it isn't freed when this function ends
    switch (dimIndexingMethod) {
    case DimIndexingMethod::ByName:
        signalHandle = vpi_handle_by_name(
            const_cast<PLI_BYTE8*>((testSignalFullName + getDimIndexString(indices)).c_str()),
            nullptr);
        break;
    case DimIndexingMethod::ByRepeatedIndex: {
        signalHandle
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
        for (const int index : indices) {
            vpiHandle nextIndexHandle
                = vpi_handle_by_index(signalHandle, static_cast<PLI_INT32>(index));
            vpi_release_handle(signalHandle);
            signalHandle = nextIndexHandle;
        }
        break;
    }
    case DimIndexingMethod::ByMultiIndex: {
        TestVpiHandle baseSignalHandle
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
        signalHandle
            = vpi_handle_by_multi_index(baseSignalHandle, static_cast<PLI_INT32>(indices.size()),
                                        const_cast<PLI_INT32*>(indices.data()));
        break;
    }
    default:
        VL_PRINTF("Unsupported DimIndexingMethod %i passed to getDimIndexedSignalHandle\n",
                  static_cast<int>(dimIndexingMethod));
        return nullptr;
    }

    return signalHandle;
}

TestVpiHandle getBitIndexedSignalHandle(const std::string& scopeName,
                                        const std::string& testSignalName, const int index,
                                        const BitIndexingMethod bitIndexingMethod) {
    const std::string testSignalFullName
        = std::string{scopeName} + "." + std::string{testSignalName};

    vpiHandle signalHandle
        = nullptr;  // Use a raw vpiHandle here so that it isn't freed when this function ends
    switch (bitIndexingMethod) {
    case BitIndexingMethod::ByName:
        signalHandle = vpi_handle_by_name(
            const_cast<PLI_BYTE8*>((testSignalFullName + getBitIndexString(index)).c_str()),
            nullptr);
        break;
    case BitIndexingMethod::ByIndex: {
        TestVpiHandle baseSignalHandle
            = vpi_handle_by_name(const_cast<PLI_BYTE8*>(testSignalFullName.c_str()), nullptr);
        signalHandle = vpi_handle_by_index(baseSignalHandle, static_cast<PLI_INT32>(index));
        break;
    }
    default:
        VL_PRINTF("Unsupported BitIndexingMethod %i passed to getBitIndexedSignalHandle\n",
                  static_cast<int>(bitIndexingMethod));
        return nullptr;
    }

    return signalHandle;
}

TestVpiHandle getDimAndBitIndexedSignalHandle(const std::string& scopeName,
                                              const std::string& testSignalName,
                                              const std::vector<int>& dimIndices,
                                              const int bitIndex,
                                              const DimIndexingMethod dimIndexingMethod,
                                              const BitIndexingMethod bitIndexingMethod) {
    TestVpiHandle signalHandle
        = getDimIndexedSignalHandle(scopeName, testSignalName, dimIndices, dimIndexingMethod);
    if (!signalHandle) return nullptr;

    vpiHandle bitHandle
        = nullptr;  // Use a raw vpiHandle here so that it isn't freed when this function ends
    switch (bitIndexingMethod) {
    case BitIndexingMethod::ByName:
        bitHandle = vpi_handle_by_name(
            const_cast<PLI_BYTE8*>((std::string{scopeName} + "." + std::string{testSignalName}
                                    + getDimIndexString(dimIndices) + getBitIndexString(bitIndex))
                                       .c_str()),
            nullptr);
        break;
    case BitIndexingMethod::ByIndex:
        bitHandle = vpi_handle_by_index(signalHandle, static_cast<PLI_INT32>(bitIndex));
        break;
    default:
        VL_PRINTF("Unsupported BitIndexingMethod %i passed to getDimAndBitIndexedSignalHandle\n",
                  static_cast<int>(bitIndexingMethod));
        return nullptr;
    }

    return bitHandle;
}

int checkSingleBit(const std::string& scopeName, const std::string& testSignalName,
                   const PLI_INT32 signalFormat, const signalValueTypes expectedValue,
                   const int index, const BitIndexingMethod bitIndexingMethod) {
    TestVpiHandle const signalHandle
        = getBitIndexedSignalHandle(scopeName, testSignalName, index, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    CHECK_RESULT_Z(checkHandleValue(signalHandle, signalFormat, expectedValue));

    return 0;
}

int checkSingleDimIndexedBit(const std::string& scopeName, const std::string& testSignalName,
                             const PLI_INT32 signalFormat, const signalValueTypes expectedValue,
                             const std::vector<int>& indices,
                             const DimIndexingMethod dimIndexingMethod, const int index,
                             const BitIndexingMethod bitIndexingMethod) {
    // Check the specific bit - can't just call checkSingleBit since that one takes a name rather
    // than a handle and would redo the dimension indexing
    TestVpiHandle const signalHandle = getDimAndBitIndexedSignalHandle(
        scopeName, testSignalName, indices, index, dimIndexingMethod, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    CHECK_RESULT_Z(checkHandleValue(signalHandle, signalFormat, expectedValue));

    return 0;
}

int checkDimIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                          const PLI_INT32 signalFormat, const signalValueTypes expectedValue,
                          const std::vector<int>& indices,
                          const DimIndexingMethod dimIndexingMethod) {
    TestVpiHandle signalHandle
        = getDimIndexedSignalHandle(scopeName, testSignalName, indices, dimIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    CHECK_RESULT_Z(checkHandleValue(signalHandle, signalFormat, expectedValue));

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

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int forceBitIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                          const PLI_INT32 signalFormat, const signalValueTypes forceValue,
                          const int index, const BitIndexingMethod bitIndexingMethod) {
    TestVpiHandle const signalHandle
        = getBitIndexedSignalHandle(scopeName, testSignalName, index, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    std::unique_ptr<s_vpi_value> value_sp = vpiValueWithFormat(signalFormat, forceValue);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int forceDimIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                          const PLI_INT32 signalFormat, const signalValueTypes forceValue,
                          const std::vector<int>& indices,
                          const DimIndexingMethod dimIndexingMethod) {
    TestVpiHandle signalHandle
        = getDimIndexedSignalHandle(scopeName, testSignalName, indices, dimIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    std::unique_ptr<s_vpi_value> value_sp = vpiValueWithFormat(signalFormat, forceValue);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int forceDimAndBitIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                                const PLI_INT32 signalFormat, const signalValueTypes forceValue,
                                const std::vector<int>& dimIndices,
                                const DimIndexingMethod dimIndexingMethod, const int bitIndex,
                                const BitIndexingMethod bitIndexingMethod) {
    TestVpiHandle const signalHandle = getDimAndBitIndexedSignalHandle(
        scopeName, testSignalName, dimIndices, bitIndex, dimIndexingMethod, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    std::unique_ptr<s_vpi_value> value_sp = vpiValueWithFormat(signalFormat, forceValue);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int partiallyForceSignal(const std::string& scopeName, const std::string& testSignalName,
                         const PLI_INT32 signalFormat, const signalValueTypes forceValue,
                         const int hi,  // NOLINT(readability-identifier-length)
                         const int lo,  // NOLINT(readability-identifier-length)
                         const Direction direction) {
    return forceSignal(scopeName,
                       std::string{testSignalName} + getPartSelectString(hi, lo, direction),
                       signalFormat, forceValue);
}

int partiallyForceDimIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                                   const PLI_INT32 signalFormat, const signalValueTypes forceValue,
                                   const int hi,  // NOLINT(readability-identifier-length)
                                   const int lo,  // NOLINT(readability-identifier-length)
                                   const Direction direction, const std::vector<int>& indices) {
    // Can't just wrap forceDimIndexedSignal by appending the part selection to the signal name,
    // because dimension indexing has to be applied before part selection
    // NOTE: Can't use DimIndexingMethod, because the part select can only be applied through
    // vpi_handle_by_name

    const std::string partSelectedSignalName
        = std::string{scopeName} + "." + std::string{testSignalName} + getDimIndexString(indices)
          + getPartSelectString(hi, lo, direction);

    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(partSelectedSignalName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    std::unique_ptr<s_vpi_value> value_sp = vpiValueWithFormat(signalFormat, forceValue);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiForceFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    return 0;
}

int releaseSignal(const std::string& scopeName, const std::string& testSignalName,
                  const PLI_INT32 signalFormat, const ReleaseValue releaseValue) {
#ifdef XRUN
    // For the packed*Continuously signals, Xrun returns the *force* value instead of the
    // expected release value when vpi_put_value is called with vpiReleaseFlag. The signal is still
    // released properly, as proven by value checks in the SystemVerilog testbench.
    signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
    if (testSignalName.find("Continuously") != std::string::npos
        && testSignalName.find("acked") != std::string::npos) {  // Match packed/Packed in name
        VL_PRINTF("Note: Running on Xrun, so expecting force value instead of release value for "
                  "signal %s\n",
                  testSignalName.c_str());
        expectedReleaseValueInit = releaseValue.expectedReleaseValue;
        expectedReleaseValue = releaseValue.expectedReleaseValueInit;
    }
#else
    const signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    const signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
#endif

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

int releaseBitIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                            const PLI_INT32 signalFormat, const ReleaseValue releaseValue,
                            const int index, const BitIndexingMethod bitIndexingMethod) {
    const signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    const signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
    TestVpiHandle const signalHandle
        = getBitIndexedSignalHandle(scopeName, testSignalName, index, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // initialize value_sp to the value that is *not* expected (i.e. forceValue for continuously
    // assigned signals, and releaseValue for clocked signals) to ensure the test fails if value_sp
    // is not updated
    std::unique_ptr<s_vpi_value> value_sp
        = vpiValueWithFormat(signalFormat, expectedReleaseValueInit);
    CHECK_RESULT_NZ(value_sp);  //NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiReleaseFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedReleaseValue);

    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), *value_sp, *expectedValueSp));

    return 0;
}

int releaseDimIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                            const PLI_INT32 signalFormat, const ReleaseValue releaseValue,
                            const std::vector<int>& indices,
                            const DimIndexingMethod dimIndexingMethod) {
#ifdef XRUN
    signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
    if (testSignalName.find("Continuously") != std::string::npos
        && testSignalName.find("acked") != std::string::npos) {
        VL_PRINTF("Note: Running on Xrun, so expecting force value instead of release value for "
                  "signal %s\n",
                  testSignalName.c_str());
        expectedReleaseValueInit = releaseValue.expectedReleaseValue;
        expectedReleaseValue = releaseValue.expectedReleaseValueInit;
    }
#else
    const signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    const signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
#endif
    TestVpiHandle signalHandle
        = getDimIndexedSignalHandle(scopeName, testSignalName, indices, dimIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // initialize value_sp to the value that is *not* expected (i.e. forceValue for continuously
    // assigned signals, and releaseValue for clocked signals) to ensure the test fails if value_sp
    // is not updated
    std::unique_ptr<s_vpi_value> value_sp
        = vpiValueWithFormat(signalFormat, expectedReleaseValueInit);
    CHECK_RESULT_NZ(value_sp);  //NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiReleaseFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedReleaseValue);

    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), *value_sp, *expectedValueSp));

    return 0;
}

int releaseDimAndBitIndexedSignal(const std::string& scopeName, const std::string& testSignalName,
                                  const PLI_INT32 signalFormat, const ReleaseValue releaseValue,
                                  const std::vector<int>& dimIndices,
                                  const DimIndexingMethod dimIndexingMethod, const int bitIndex,
                                  const BitIndexingMethod bitIndexingMethod) {
#ifdef XRUN
    signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
    if (testSignalName.find("Continuously") != std::string::npos
        && testSignalName.find("acked") != std::string::npos) {
        VL_PRINTF("Note: Running on Xrun, so expecting force value instead of release value for "
                  "signal %s\n",
                  testSignalName.c_str());
        expectedReleaseValueInit = releaseValue.expectedReleaseValue;
        expectedReleaseValue = releaseValue.expectedReleaseValueInit;
    }
#else
    const signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    const signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;
#endif
    TestVpiHandle const signalHandle = getDimAndBitIndexedSignalHandle(
        scopeName, testSignalName, dimIndices, bitIndex, dimIndexingMethod, bitIndexingMethod);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // initialize value_sp to the value that is *not* expected (i.e. forceValue for continuously
    // assigned signals, and releaseValue for clocked signals) to ensure the test fails if value_sp
    // is not updated
    std::unique_ptr<s_vpi_value> value_sp
        = vpiValueWithFormat(signalFormat, expectedReleaseValueInit);
    CHECK_RESULT_NZ(value_sp);  //NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiReleaseFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    const std::unique_ptr<s_vpi_value> expectedValueSp
        = vpiValueWithFormat(signalFormat, expectedReleaseValue);

    CHECK_RESULT_NZ(expectedValueSp);  // NOLINT(concurrency-mt-unsafe)

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), *value_sp, *expectedValueSp));

    return 0;
}

int partiallyReleaseSignal(const std::string& scopeName, const std::string& testSignalName,
                           const PLI_INT32 signalFormat, const ReleaseValue releaseValue,
                           const int hi,  // NOLINT(readability-identifier-length)
                           const int lo,  // NOLINT(readability-identifier-length)
                           const Direction direction) {
    return releaseSignal(scopeName,
                         std::string{testSignalName} + getPartSelectString(hi, lo, direction),
                         signalFormat, releaseValue);
}

int partiallyReleaseDimIndexedSignal(const std::string& scopeName,
                                     const std::string& testSignalName,
                                     const PLI_INT32 signalFormat, const ReleaseValue releaseValue,
                                     int hi,  // NOLINT(readability-identifier-length)
                                     const int lo,  // NOLINT(readability-identifier-length)
                                     const Direction direction, const std::vector<int>& indices) {
    // Can't just wrap releaseDimIndexedSignal by appending the part selection to the signal name,
    // because dimension indexing has to be applied before part selection
    const signalValueTypes expectedReleaseValueInit = releaseValue.expectedReleaseValueInit;
    const signalValueTypes expectedReleaseValue = releaseValue.expectedReleaseValue;

    const std::string partSelectedSignalName
        = std::string{scopeName} + "." + std::string{testSignalName} + getDimIndexString(indices)
          + getPartSelectString(hi, lo, direction);  // Apply indexing before bit-select

    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(partSelectedSignalName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    // initialize value_sp to the value that is *not* expected (i.e. forceValue for continuously
    // assigned signals, and releaseValue for clocked signals) to ensure the test fails if value_sp
    // is not updated
    std::unique_ptr<s_vpi_value> value_sp
        = vpiValueWithFormat(signalFormat, expectedReleaseValueInit);
    CHECK_RESULT_NZ(value_sp);  // NOLINT(concurrency-mt-unsafe)

    vpi_put_value(signalHandle, value_sp.get(), nullptr, vpiReleaseFlag);

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), *value_sp,
                                   *vpiValueWithFormat(signalFormat, expectedReleaseValue)));

    return 0;
}

}  // namespace

extern "C" int checkNonContinuousValuesForced() {
    // Non-continuously assigned (e.g. clocked) signals retain the forced value after releasing
    // until the they are updated again, so check that they are still at the forced value
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.packedIndices.empty()) {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, signal.signalName, signal.valueType, signal.forceValue));
            } else {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.forceValue, signal.packedIndices,
                                          DimIndexingMethod::ByRepeatedIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.forceValue, signal.packedIndices,
                                          DimIndexingMethod::ByMultiIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.forceValue, signal.packedIndices,
                                          DimIndexingMethod::ByName));
            }
            return 0;
        }));
    return 0;
}

extern "C" int checkValuesForced() {
    // Clocked signals
    CHECK_RESULT_Z(checkNonContinuousValuesForced());

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.packedIndices.empty()) {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                               signal.valueType, signal.forceValue));
            } else {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(
                        scopeName, std::string{signal.signalName} + "Continuously",
                        signal.valueType, signal.forceValue, signal.packedIndices,
                        DimIndexingMethod::ByRepeatedIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName,
                                          std::string{signal.signalName} + "Continuously",
                                          signal.valueType, signal.forceValue,
                                          signal.packedIndices, DimIndexingMethod::ByMultiIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName,
                                          std::string{signal.signalName} + "Continuously",
                                          signal.valueType, signal.forceValue,
                                          signal.packedIndices, DimIndexingMethod::ByName));
            }
            return 0;
        }));
    return 0;
}

extern "C" int checkContinuousValuesReleased() {
    // Continuously assigned signals return to their original value immediately after releasing
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.packedIndices.empty()) {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                               signal.valueType, signal.releaseValue));
            } else {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(
                        scopeName, std::string{signal.signalName} + "Continuously",
                        signal.valueType, signal.releaseValue, signal.packedIndices,
                        DimIndexingMethod::ByRepeatedIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName,
                                          std::string{signal.signalName} + "Continuously",
                                          signal.valueType, signal.releaseValue,
                                          signal.packedIndices, DimIndexingMethod::ByMultiIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName,
                                          std::string{signal.signalName} + "Continuously",
                                          signal.valueType, signal.releaseValue,
                                          signal.packedIndices, DimIndexingMethod::ByName));
            }
            return 0;
        }));
    return 0;
}

extern "C" int
checkContinuousValuesPartiallyReleased(  // NOLINT(readability-function-cognitive-complexity)
    void) {
    // The released bits should return to the release value immediately, while the still forced
    // bits should still be at the force value
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
#ifdef XRUN
                if (!signal.packedIndices.empty()) return 0;
#endif
                if (signal.shouldTestPartialForce) {
                    if (!TestSimulator::is_icarus()) {  // Icarus does not support bit selects in
                                                        // vpi_handle_by_name
                        const std::string dimIndex = signal.packedIndices.empty()
                                                         ? ""
                                                         : getDimIndexString(signal.packedIndices);
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + "Continuously" + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Descending),
                                       signal.valueType, signal.partialValue.partialReleaseValue));
#ifndef XRUN  // Xcelium does not support ascending part selects in vpi_handle_by_name
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + "Continuously" + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Ascending),
                                       signal.valueType, signal.partialValue.partialReleaseValue));
#endif
                    }
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                                       signal.valueType,
                                       signal.partialValue.fullSignalReleaseValue));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalReleaseValue,
                                signal.packedIndices, DimIndexingMethod::ByRepeatedIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalReleaseValue,
                                signal.packedIndices, DimIndexingMethod::ByMultiIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalReleaseValue,
                                signal.packedIndices, DimIndexingMethod::ByName));
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int
checkValuesPartiallyReleased(void) {  // NOLINT(readability-function-cognitive-complexity)
    // Check both the partial ranges and the full signal values

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
#ifdef XRUN
                if (!signal.packedIndices.empty()) return 0;
#endif
                if (signal.shouldTestPartialForce) {
                    if (!TestSimulator::is_icarus()) {  // Icarus does not support bit selects in
                                                        // vpi_handle_by_name
                        const std::string dimIndex = signal.packedIndices.empty()
                                                         ? ""
                                                         : getDimIndexString(signal.packedIndices);
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Descending),
                                       signal.valueType, signal.partialValue.partialReleaseValue));
#ifndef XRUN  // Xcelium does not support ascending part selects in vpi_handle_by_name
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Ascending),
                                       signal.valueType, signal.partialValue.partialReleaseValue));
#endif
                    }
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, signal.signalName, signal.valueType,
                                       signal.partialValue.fullSignalReleaseValue));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalReleaseValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByRepeatedIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalReleaseValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByMultiIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalReleaseValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByName));
                    }
                }
                return 0;
            }));

    // Continuously assigned signals
    checkContinuousValuesPartiallyReleased();
    return 0;
}

extern "C" int
checkNonContinuousValuesPartiallyForced(  // NOLINT(readability-function-cognitive-complexity)
    void) {
    // Non-continuously assigned (e.g. clocked) signals retain the partially forced value after
    // releasing until the they are updated again, so check that they are still at the partially
    // forced value
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
#ifdef XRUN
                if (!signal.packedIndices.empty()) return 0;
#endif
                if (signal.shouldTestPartialForce) {
                    if (!TestSimulator::is_icarus()) {  // Icarus does not support bit selects in
                                                        // vpi_handle_by_name
                        const std::string dimIndex = signal.packedIndices.empty()
                                                         ? ""
                                                         : getDimIndexString(signal.packedIndices);
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Descending),
                                       signal.valueType, signal.partialValue.partialForceValue));
#ifndef XRUN  // Xcelium does not support ascending part selects in vpi_handle_by_name
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Ascending),
                                       signal.valueType, signal.partialValue.partialForceValue));
#endif
                    }
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, signal.signalName, signal.valueType,
                                       signal.partialValue.fullSignalForceValue));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalForceValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByRepeatedIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalForceValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByMultiIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.partialValue.fullSignalForceValue,
                                                  signal.packedIndices,
                                                  DimIndexingMethod::ByName));
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int
checkValuesPartiallyForced(void) {  // NOLINT(readability-function-cognitive-complexity)
    // Check both the partial ranges and the full signal values

    // Clocked signals
    CHECK_RESULT_Z(checkNonContinuousValuesPartiallyForced());

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
#ifdef XRUN  // Xcelium does not support a syntax like "signal[1][0][1:0]" in vpi_handle_by_name,
             // so since it cannot partially force multi-dimensional signals through VPI, checking
             // is skipped entirely, even if the signal was forced through SystemVerilog
                if (!signal.packedIndices.empty()) return 0;
#endif

                if (signal.shouldTestPartialForce) {
                    if (!TestSimulator::is_icarus()) {  // Icarus does not support bit selects in
                                                        // vpi_handle_by_name
                        const std::string dimIndex = signal.packedIndices.empty()
                                                         ? ""
                                                         : getDimIndexString(signal.packedIndices);
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + "Continuously" + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Descending),
                                       signal.valueType, signal.partialValue.partialForceValue));
#ifndef XRUN  // Xcelium does not support ascending part selects in vpi_handle_by_name
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName,
                                       std::string{signal.signalName} + "Continuously" + dimIndex
                                           + getPartSelectString(signal.partialValue.bitRange.hi,
                                                                 signal.partialValue.bitRange.lo,
                                                                 Direction::Ascending),
                                       signal.valueType, signal.partialValue.partialForceValue));
#endif
                    }
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                                       signal.valueType,
                                       signal.partialValue.fullSignalForceValue));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalForceValue,
                                signal.packedIndices, DimIndexingMethod::ByRepeatedIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalForceValue,
                                signal.packedIndices, DimIndexingMethod::ByMultiIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType, signal.partialValue.fullSignalForceValue,
                                signal.packedIndices, DimIndexingMethod::ByName));
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int
checkNonContinuousSingleBitForced(void) {  // NOLINT(readability-function-cognitive-complexity)
    // Non-continuously assigned (e.g. clocked) signals retain the forced value where one bit
    // was forced after releasing until the they are updated again, so check that the bit is
    // still at the forced value.
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName, signal.signalName, signal.valueType,
                                           signal.bitValue.bitForceValue, signal.bitValue.bitIndex,
                                           BitIndexingMethod::ByName));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName, signal.signalName, signal.valueType,
                                           signal.bitValue.bitForceValue, signal.bitValue.bitIndex,
                                           BitIndexingMethod::ByIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, signal.signalName, signal.valueType,
                                       signal.bitValue.fullSignalForceValue));
                    } else {
                        for (DimIndexingMethod dimIndexingMethod :
                             {DimIndexingMethod::ByRepeatedIndex, DimIndexingMethod::ByMultiIndex,
                              DimIndexingMethod::ByName}) {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, signal.signalName, signal.valueType,
                                    signal.bitValue.bitForceValue, signal.packedIndices,
                                    dimIndexingMethod, signal.bitValue.bitIndex,
                                    BitIndexingMethod::ByName));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, signal.signalName, signal.valueType,
                                    signal.bitValue.bitForceValue, signal.packedIndices,
                                    dimIndexingMethod, signal.bitValue.bitIndex,
                                    BitIndexingMethod::ByIndex));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkDimIndexedSignal(scopeName, signal.signalName,
                                                      signal.valueType,
                                                      signal.bitValue.fullSignalForceValue,
                                                      signal.packedIndices, dimIndexingMethod));
                        }
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int checkSingleBitForced(void) {  // NOLINT(readability-function-cognitive-complexity)
    // Check both single bit values and full signal values

    // Clocked signals
    CHECK_RESULT_Z(checkNonContinuousSingleBitForced());

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName,
                                           std::string{signal.signalName} + "Continuously",
                                           signal.valueType, signal.bitValue.bitForceValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByName));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName,
                                           std::string{signal.signalName} + "Continuously",
                                           signal.valueType, signal.bitValue.bitForceValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                                       signal.valueType, signal.bitValue.fullSignalForceValue));
                    } else {
                        for (DimIndexingMethod dimIndexingMethod :
                             {DimIndexingMethod::ByRepeatedIndex, DimIndexingMethod::ByMultiIndex,
                              DimIndexingMethod::ByName}) {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.bitForceValue,
                                    signal.packedIndices, dimIndexingMethod,
                                    signal.bitValue.bitIndex, BitIndexingMethod::ByName));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.bitForceValue,
                                    signal.packedIndices, dimIndexingMethod,
                                    signal.bitValue.bitIndex, BitIndexingMethod::ByIndex));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkDimIndexedSignal(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.fullSignalForceValue,
                                    signal.packedIndices, dimIndexingMethod));
                        }
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int
checkContinuousValuesSingleBitReleased(  // NOLINT(readability-function-cognitive-complexity)
    void) {
    // For continuously assigned signals, the released bit should return to the release value
    // immediately, while the still forced bits should still be at the force value
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName,
                                           std::string{signal.signalName} + "Continuously",
                                           signal.valueType, signal.bitValue.bitReleaseValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByName));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName,
                                           std::string{signal.signalName} + "Continuously",
                                           signal.valueType, signal.bitValue.bitReleaseValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, std::string{signal.signalName} + "Continuously",
                                       signal.valueType, signal.bitValue.fullSignalReleaseValue));
                    } else {
                        for (DimIndexingMethod dimIndexingMethod :
                             {DimIndexingMethod::ByRepeatedIndex, DimIndexingMethod::ByMultiIndex,
                              DimIndexingMethod::ByName}) {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.bitReleaseValue,
                                    signal.packedIndices, dimIndexingMethod,
                                    signal.bitValue.bitIndex, BitIndexingMethod::ByName));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.bitReleaseValue,
                                    signal.packedIndices, dimIndexingMethod,
                                    signal.bitValue.bitIndex, BitIndexingMethod::ByIndex));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkDimIndexedSignal(
                                    scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.bitValue.fullSignalReleaseValue,
                                    signal.packedIndices, dimIndexingMethod));
                        }
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int checkSingleBitReleased(void) {  // NOLINT(readability-function-cognitive-complexity)
    // The released bit should return to the release value, while the other bits are still
    // forced

    // Check both single bit values and full signal values

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [](const TestSignal& signal) {  // NOLINT(readability-function-cognitive-complexity)
                if (signal.shouldTestPartialForce) {

                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName, std::string{signal.signalName},
                                           signal.valueType, signal.bitValue.bitReleaseValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByName));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkSingleBit(scopeName, std::string{signal.signalName},
                                           signal.valueType, signal.bitValue.bitReleaseValue,
                                           signal.bitValue.bitIndex, BitIndexingMethod::ByIndex));
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            checkValue(scopeName, std::string{signal.signalName}, signal.valueType,
                                       signal.bitValue.fullSignalReleaseValue));
                    } else {
                        for (DimIndexingMethod dimIndexingMethod :
                             {DimIndexingMethod::ByRepeatedIndex, DimIndexingMethod::ByMultiIndex,
                              DimIndexingMethod::ByName}) {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName}, signal.valueType,
                                    signal.bitValue.bitReleaseValue, signal.packedIndices,
                                    dimIndexingMethod, signal.bitValue.bitIndex,
                                    BitIndexingMethod::ByName));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkSingleDimIndexedBit(
                                    scopeName, std::string{signal.signalName}, signal.valueType,
                                    signal.bitValue.bitReleaseValue, signal.packedIndices,
                                    dimIndexingMethod, signal.bitValue.bitIndex,
                                    BitIndexingMethod::ByIndex));
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                checkDimIndexedSignal(scopeName, std::string{signal.signalName},
                                                      signal.valueType,
                                                      signal.bitValue.fullSignalReleaseValue,
                                                      signal.packedIndices, dimIndexingMethod));
                        }
                    }
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(checkContinuousValuesSingleBitReleased());
    return 0;
}

extern "C" int checkValuesReleased() {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [](const TestSignal& signal) {
            if (signal.packedIndices.empty()) {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkValue(scopeName, signal.signalName, signal.valueType,
                               signal.releaseValue));
            } else {
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.releaseValue, signal.packedIndices,
                                          DimIndexingMethod::ByRepeatedIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.releaseValue, signal.packedIndices,
                                          DimIndexingMethod::ByMultiIndex));
                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                    checkDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                          signal.releaseValue, signal.packedIndices,
                                          DimIndexingMethod::ByName));
            }
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(checkContinuousValuesReleased());
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
        "vpiOctStrVal for 't.test.octString__VforceVal'"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "decStringC", {.format = vpiDecStrVal, .value = {.str = const_cast<PLI_BYTE8*>("A123")}},
        vpiForceFlag,
        "vpi_put_value: Parsing failed for 'A123' as value vpiDecStrVal for "
        "'t.test.decStringC__VforceVal'"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "decStringC", {.format = vpiDecStrVal, .value = {.str = const_cast<PLI_BYTE8*>("123A")}},
        vpiForceFlag,
        "vpi_put_value: Trailing garbage 'A' in '123A' as value vpiDecStrVal for "
        "'t.test.decStringC__VforceVal'"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "hexString", {.format = vpiHexStrVal, .value = {.str = const_cast<PLI_BYTE8*>("12AG")}},
        vpiForceFlag,
        "vpi_put_value: Non hex character 'G' in '12AG' as value vpiHexStrVal for "
        "'t.test.hexString__VforceVal'"));

    // vop was replaced with baseSignalVop in vpi_put_value, so these tests are required to hit
    // the test coverage target and ensure the error messages still work.
    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "onebit", {.format = vpiRawFourStateVal, .value = {}}, vpiForceFlag,
        "vl_check_format: Unsupported format (vpiRawFourStateVal) for "
        "'t.test.onebit'"));

    CHECK_RESULT_Z(expectVpiPutError(  // NOLINT(concurrency-mt-unsafe)
        "onebit", {.format = vpiSuppressVal, .value = {}}, vpiForceFlag,
        "vpi_put_value: Unsupported format (vpiSuppressVal) as requested for "
        "'t.test.onebit__VforceVal'"));

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

// This function is needed to ensure that vpiInertialDelay also works with forceable signals.
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

    // NOTE: Because __VforceRd will only be updated in `eval_act`, `doInertialPuts` does not
    // update the value read by `vpi_get_value` - that is only visible after another `eval`.
    // Hence, `checkInertialDelay` must be called later to check success.
    VerilatedVpi::doInertialPuts();

    return 0;
}

extern "C" int checkInertialDelay() {
    const std::string fullSignalName = std::string{scopeName} + ".delayed";
    TestVpiHandle const signalHandle  //NOLINT(misc-misplaced-const)
        = vpi_handle_by_name(const_cast<PLI_BYTE8*>(fullSignalName.c_str()), nullptr);
    CHECK_RESULT_NZ(signalHandle);  // NOLINT(concurrency-mt-unsafe)

    s_vpi_value value_s{.format = vpiIntVal,
                        .value
                        = {.integer = 0}};  // Ensure that test fails if value_s is not updated

    vpi_get_value(signalHandle, &value_s);
    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_Z(vpiCheckErrorLevel(maxAllowedErrorLevel))

    constexpr int delayedValue = 123;
    s_vpi_value expectedValueS{.format = vpiIntVal, .value = {.integer = delayedValue}};

    // NOLINTNEXTLINE(concurrency-mt-unsafe)
    CHECK_RESULT_NZ(vpiValuesEqual(vpi_get(vpiSize, signalHandle), value_s, expectedValueS));

    return 0;
}
#endif

extern "C" int forceValues(const DimIndexingMethod dimIndexingMethod) {
    if (!TestSimulator::is_verilator()) {
#ifdef VERILATOR
        printf("TestSimulator indicating not verilator, but VERILATOR macro is defined\n");
        return 1;
#endif
    }

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(),
                    [dimIndexingMethod](const TestSignal& signal) {
                        if (signal.packedIndices.empty()) {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                forceSignal(scopeName, signal.signalName, signal.valueType,
                                            signal.forceValue));
                        } else {
                            CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                forceDimIndexedSignal(scopeName, signal.signalName,
                                                      signal.valueType, signal.forceValue,
                                                      signal.packedIndices, dimIndexingMethod));
                        }
                        return 0;
                    }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        forceSignal(scopeName, std::string{signal.signalName} + "Continuously",
                                    signal.valueType, signal.forceValue));
                } else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        forceDimIndexedSignal(scopeName,
                                              std::string{signal.signalName} + "Continuously",
                                              signal.valueType, signal.forceValue,
                                              signal.packedIndices, dimIndexingMethod));
                }
                return 0;
            }));
    return 0;
}

extern "C" int partiallyForceValues(  // NOLINT(readability-function-cognitive-complexity)
    const Direction direction) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [direction](const TestSignal& signal) {
            if (signal.shouldTestPartialForce) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyForceSignal(scopeName, signal.signalName, signal.valueType,
                                             signal.partialValue.partialForceValue,
                                             signal.partialValue.bitRange.hi,
                                             signal.partialValue.bitRange.lo, direction));
                }
#ifndef XRUN  // Xcelium does not support a syntax like "signal[1][0][1:0]" in vpi_handle_by_name
                else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyForceDimIndexedSignal(
                            scopeName, signal.signalName, signal.valueType,
                            signal.partialValue.partialForceValue, signal.partialValue.bitRange.hi,
                            signal.partialValue.bitRange.lo, direction, signal.packedIndices));
                }
#endif
            }
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [direction](const TestSignal& signal) {
            if (signal.shouldTestPartialForce) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyForceSignal(
                            scopeName, std::string{signal.signalName} + "Continuously",
                            signal.valueType, signal.partialValue.partialForceValue,
                            signal.partialValue.bitRange.hi, signal.partialValue.bitRange.lo,
                            direction));
                }
#ifndef XRUN
                else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyForceDimIndexedSignal(
                            scopeName, std::string{signal.signalName} + "Continuously",
                            signal.valueType, signal.partialValue.partialForceValue,
                            signal.partialValue.bitRange.hi, signal.partialValue.bitRange.lo,
                            direction, signal.packedIndices));
                }
#endif
            }
            return 0;
        }));
    return 0;
}

extern "C" int forceSingleBit(  // NOLINT(readability-function-cognitive-complexity)
    const BitIndexingMethod bitIndexingMethod, const DimIndexingMethod dimIndexingMethod) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [bitIndexingMethod, dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {  // Also applies to single bit forcing
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            forceBitIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                  signal.bitValue.bitForceValue,
                                                  signal.bitValue.bitIndex, bitIndexingMethod));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            forceDimAndBitIndexedSignal(
                                scopeName, signal.signalName, signal.valueType,
                                signal.bitValue.bitForceValue, signal.packedIndices,
                                dimIndexingMethod, signal.bitValue.bitIndex, bitIndexingMethod));
                    }
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(),
                    [bitIndexingMethod, dimIndexingMethod](const TestSignal& signal) {
                        if (signal.shouldTestPartialForce) {
                            if (signal.packedIndices.empty()) {
                                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                    forceBitIndexedSignal(
                                        scopeName, std::string{signal.signalName} + "Continuously",
                                        signal.valueType, signal.bitValue.bitForceValue,
                                        signal.bitValue.bitIndex, bitIndexingMethod));
                            } else {
                                CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                                    forceDimAndBitIndexedSignal(
                                        scopeName, std::string{signal.signalName} + "Continuously",
                                        signal.valueType, signal.bitValue.bitForceValue,
                                        signal.packedIndices, dimIndexingMethod,
                                        signal.bitValue.bitIndex, bitIndexingMethod));
                            }
                        }
                        return 0;
                    }));
    return 0;
}

extern "C" int releaseValues(const DimIndexingMethod dimIndexingMethod) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        releaseSignal(scopeName, signal.signalName, signal.valueType,
                                      {signal.releaseValue, signal.forceValue}));
                } else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        releaseDimIndexedSignal(scopeName, signal.signalName, signal.valueType,
                                                {signal.releaseValue, signal.forceValue},
                                                signal.packedIndices, dimIndexingMethod));
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        releaseSignal(scopeName, std::string{signal.signalName} + "Continuously",
                                      signal.valueType, {signal.forceValue, signal.releaseValue}));
                } else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        releaseDimIndexedSignal(
                            scopeName, std::string{signal.signalName} + "Continuously",
                            signal.valueType, {signal.forceValue, signal.releaseValue},
                            signal.packedIndices, dimIndexingMethod));
                }
                return 0;
            }));
    return 0;
}

extern "C" int releasePartiallyForcedValues(  // NOLINT(readability-function-cognitive-complexity)
    const DimIndexingMethod dimIndexingMethod) {
    // Skip any values that cannot be partially forced. Can't just reuse releaseValues, because
    // the output argument s_vpi_value of vpi_put_value with vpiReleaseFlag differs depending
    // on whether or not a signal was forced before, and not all signals are forced in the
    // partial forcing test.

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.releaseValue, signal.partialValue.fullSignalForceValue}));
                    }
#ifndef XRUN
                    else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimIndexedSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.releaseValue, signal.partialValue.fullSignalForceValue},
                                signal.packedIndices, dimIndexingMethod));
                    }
#endif
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.partialValue.fullSignalForceValue, signal.releaseValue}));
                    }
#ifndef XRUN
                    else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.partialValue.fullSignalForceValue, signal.releaseValue},
                                signal.packedIndices, dimIndexingMethod));
                    }
#endif
                }
                return 0;
            }));
    return 0;
}

extern "C" int releaseSingleBitForcedValues(  // NOLINT(readability-function-cognitive-complexity)
    const DimIndexingMethod dimIndexingMethod) {
    // Release the entire signal that previously had a single bit forced in it

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.releaseValue, signal.bitValue.fullSignalForceValue}));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimIndexedSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.releaseValue, signal.bitValue.fullSignalForceValue},
                                signal.packedIndices, dimIndexingMethod));
                    }
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(), [dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.bitValue.fullSignalForceValue, signal.releaseValue}));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.bitValue.fullSignalForceValue, signal.releaseValue},
                                signal.packedIndices, dimIndexingMethod));
                    }
                }
                return 0;
            }));
    return 0;
}

extern "C" int partiallyReleaseValues(  // NOLINT(readability-function-cognitive-complexity)
    const Direction direction) {
    // Partially release a fully forced signal

    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [direction](const TestSignal& signal) {
            if (signal.shouldTestPartialForce) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyReleaseSignal(scopeName, signal.signalName, signal.valueType,
                                               {signal.partialValue.partialReleaseValue,
                                                signal.partialValue.partialForceValue},
                                               signal.partialValue.bitRange.hi,
                                               signal.partialValue.bitRange.lo, direction));
                }
#ifndef XRUN
                else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyReleaseDimIndexedSignal(
                            scopeName, signal.signalName, signal.valueType,
                            {signal.partialValue.partialReleaseValue,
                             signal.partialValue.partialForceValue},
                            signal.partialValue.bitRange.hi, signal.partialValue.bitRange.lo,
                            direction, signal.packedIndices));
                }
#endif
            }
            return 0;
        }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(TestSignals.begin(), TestSignals.end(), [direction](const TestSignal& signal) {
            if (signal.shouldTestPartialForce) {
                if (signal.packedIndices.empty()) {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyReleaseSignal(scopeName,
                                               std::string{signal.signalName} + "Continuously",
                                               signal.valueType,
                                               {signal.partialValue.partialForceValue,
                                                signal.partialValue.partialReleaseValue},
                                               signal.partialValue.bitRange.hi,
                                               signal.partialValue.bitRange.lo, direction));
                }
#ifndef XRUN
                else {
                    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                        partiallyReleaseDimIndexedSignal(
                            scopeName, std::string{signal.signalName} + "Continuously",
                            signal.valueType,
                            {signal.partialValue.partialForceValue,
                             signal.partialValue.partialReleaseValue},
                            signal.partialValue.bitRange.hi, signal.partialValue.bitRange.lo,
                            direction, signal.packedIndices));
                }
#endif
            }
            return 0;
        }));
    return 0;
}

extern "C" int releaseSingleBit(  // NOLINT(readability-function-cognitive-complexity)
    const BitIndexingMethod bitIndexingMethod, const DimIndexingMethod dimIndexingMethod) {
    // Clocked signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [bitIndexingMethod, dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {  // Also applies to single bit releasing
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseBitIndexedSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.bitValue.bitReleaseValue, signal.bitValue.bitForceValue},
                                signal.bitValue.bitIndex, bitIndexingMethod));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimAndBitIndexedSignal(
                                scopeName, signal.signalName, signal.valueType,
                                {signal.bitValue.bitReleaseValue, signal.bitValue.bitForceValue},
                                signal.packedIndices, dimIndexingMethod, signal.bitValue.bitIndex,
                                bitIndexingMethod));
                    }
                }
                return 0;
            }));

    // Continuously assigned signals
    CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
        std::any_of(
            TestSignals.begin(), TestSignals.end(),
            [bitIndexingMethod, dimIndexingMethod](const TestSignal& signal) {
                if (signal.shouldTestPartialForce) {
                    if (signal.packedIndices.empty()) {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseBitIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.bitValue.bitForceValue, signal.bitValue.bitReleaseValue},
                                signal.bitValue.bitIndex, bitIndexingMethod));
                    } else {
                        CHECK_RESULT_Z(  // NOLINT(concurrency-mt-unsafe)
                            releaseDimAndBitIndexedSignal(
                                scopeName, std::string{signal.signalName} + "Continuously",
                                signal.valueType,
                                {signal.bitValue.bitForceValue, signal.bitValue.bitReleaseValue},
                                signal.packedIndices, dimIndexingMethod, signal.bitValue.bitIndex,
                                bitIndexingMethod));
                    }
                }
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

static int checkNonContinuousValuesForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkNonContinuousValuesForced();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkContinuousValuesReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkContinuousValuesReleased();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkContinuousValuesPartiallyReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkContinuousValuesPartiallyReleased();
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

static int checkNonContinuousValuesPartiallyForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkNonContinuousValuesPartiallyForced();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkContinuousValuesSingleBitReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkContinuousValuesSingleBitReleased();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkNonContinuousSingleBitForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkNonContinuousSingleBitForced();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkSingleBitForcedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkSingleBitForced();
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

static int checkValuesPartiallyReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkValuesPartiallyReleased();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int checkSingleBitReleasedVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = checkSingleBitReleased();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static int forceValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(arg, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = forceValues(static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int partiallyForceValuesVpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value directionValue;
    directionValue.format = vpiIntVal;
    vpi_get_value(arg, &directionValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = partiallyForceValues(static_cast<Direction>(directionValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int forceSingleBitVpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    CHECK_RESULT_NZ(it)

    TestVpiHandle argBitIndexingMethod = vpi_scan(it);
    CHECK_RESULT_NZ(argBitIndexingMethod)
    TestVpiHandle argDimIndexingMethod = vpi_scan(it);
    CHECK_RESULT_NZ(argDimIndexingMethod)
    CHECK_RESULT_Z(vpi_scan(it))

    s_vpi_value bitIndexingMethodValue;
    bitIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(argBitIndexingMethod, &bitIndexingMethodValue);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(argDimIndexingMethod, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = forceSingleBit(static_cast<BitIndexingMethod>(bitIndexingMethodValue.value.integer),
                         static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));

    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int releaseValuesVpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(arg, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = releaseValues(static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int releasePartiallyForcedValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(arg, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = releasePartiallyForcedValues(
        static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int releaseSingleBitForcedValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(arg, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer = releaseSingleBitForcedValues(
        static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int partiallyReleaseValuesVpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    TestVpiHandle arg = vpi_scan(it);

    s_vpi_value directionValue;
    directionValue.format = vpiIntVal;
    vpi_get_value(arg, &directionValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = partiallyReleaseValues(static_cast<Direction>(directionValue.value.integer));
    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

static int releaseSingleBitVpi(PLI_BYTE8*) {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);

    TestVpiHandle it = vpi_iterate(vpiArgument, href);
    CHECK_RESULT_NZ(it)

    TestVpiHandle argBitIndexingMethod = vpi_scan(it);
    CHECK_RESULT_NZ(argBitIndexingMethod)
    TestVpiHandle argDimIndexingMethod = vpi_scan(it);
    CHECK_RESULT_NZ(argDimIndexingMethod)
    CHECK_RESULT_Z(vpi_scan(it))

    s_vpi_value bitIndexingMethodValue;
    bitIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(argBitIndexingMethod, &bitIndexingMethodValue);

    s_vpi_value dimIndexingMethodValue;
    dimIndexingMethodValue.format = vpiIntVal;
    vpi_get_value(argDimIndexingMethod, &dimIndexingMethodValue);

    s_vpi_value vpiValue;
    vpiValue.format = vpiIntVal;
    vpiValue.value.integer
        = releaseSingleBit(static_cast<BitIndexingMethod>(bitIndexingMethodValue.value.integer),
                           static_cast<DimIndexingMethod>(dimIndexingMethodValue.value.integer));

    vpi_put_value(href, &vpiValue, nullptr, vpiNoDelay);

    return 0;
}

std::array<s_vpi_systf_data, 20> vpi_systf_data = {
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$forceValues",
                     (PLI_INT32(*)(PLI_BYTE8*))forceValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releaseValues",
                     (PLI_INT32(*)(PLI_BYTE8*))releaseValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releasePartiallyForcedValues",
                     (PLI_INT32(*)(PLI_BYTE8*))releasePartiallyForcedValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releaseSingleBitForcedValues",
                     (PLI_INT32(*)(PLI_BYTE8*))releaseSingleBitForcedValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesForced",
                     (PLI_INT32(*)(PLI_BYTE8*))checkValuesForcedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkNonContinuousValuesForced",
                     (PLI_INT32(*)(PLI_BYTE8*))checkNonContinuousValuesForcedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkContinuousValuesReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkContinuousValuesReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkContinuousValuesPartiallyReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkContinuousValuesPartiallyReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesPartiallyForced",
                     (PLI_INT32(*)(PLI_BYTE8*))checkValuesPartiallyForcedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkSingleBitForced",
                     (PLI_INT32(*)(PLI_BYTE8*))checkSingleBitForcedVpi, 0, 0, 0},
    s_vpi_systf_data{
        vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkNonContinuousValuesPartiallyForced",
        (PLI_INT32(*)(PLI_BYTE8*))checkNonContinuousValuesPartiallyForcedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkContinuousValuesSingleBitReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkContinuousValuesSingleBitReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkNonContinuousSingleBitForced",
                     (PLI_INT32(*)(PLI_BYTE8*))checkNonContinuousSingleBitForcedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkValuesReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkValuesPartiallyReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkValuesPartiallyReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$checkSingleBitReleased",
                     (PLI_INT32(*)(PLI_BYTE8*))checkSingleBitReleasedVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$partiallyForceValues",
                     (PLI_INT32(*)(PLI_BYTE8*))partiallyForceValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$forceSingleBit",
                     (PLI_INT32(*)(PLI_BYTE8*))forceSingleBitVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$partiallyReleaseValues",
                     (PLI_INT32(*)(PLI_BYTE8*))partiallyReleaseValuesVpi, 0, 0, 0},
    s_vpi_systf_data{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$releaseSingleBit",
                     (PLI_INT32(*)(PLI_BYTE8*))releaseSingleBitVpi, 0, 0, 0}};

// cver entry
extern "C" void vpi_compat_bootstrap(void) {
    for (s_vpi_systf_data& systf : vpi_systf_data) vpi_register_systf(&systf);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
