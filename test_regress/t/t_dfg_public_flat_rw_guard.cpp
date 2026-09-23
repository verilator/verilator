// DESCRIPTION: Verilator: Check public state as well as DFG output values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "TestCheck.h"
#include "Vopt.h"
#include "Vopt___024root.h"
#include "Vref.h"
#include "Vref___024root.h"

#include <cstdlib>

int errors = 0;

void evaluate(Vref& ref, Vopt& opt) {
    ref.eval();
    opt.eval();
    TEST_CHECK_EQ(+ref.constant_out, +opt.constant_out);
    TEST_CHECK_EQ(+ref.feedback_out, +opt.feedback_out);
    TEST_CHECK_EQ(+ref.packed_out, +opt.packed_out);
    TEST_CHECK_EQ(+ref.array_out, +opt.array_out);
    TEST_CHECK_EQ(+ref.rootp->t__DOT__constant_value, +opt.rootp->t__DOT__constant_value);
    TEST_CHECK_EQ(+ref.rootp->t__DOT__feedback_value, +opt.rootp->t__DOT__feedback_value);
    TEST_CHECK_EQ(+ref.rootp->t__DOT__packed_value, +opt.rootp->t__DOT__packed_value);
    TEST_CHECK_EQ(+ref.rootp->t__DOT__array_value[0], +opt.rootp->t__DOT__array_value[0]);
    TEST_CHECK_EQ(+ref.rootp->t__DOT__array_value[1], +opt.rootp->t__DOT__array_value[1]);
    if (errors) std::exit(1);
}

int main(int, char**) {
    VerilatedContext ctx;
    Vref ref{&ctx};
    Vopt opt{&ctx};
    ref.data = opt.data = 0;
    ref.rootp->t__DOT__packed_value = opt.rootp->t__DOT__packed_value = 0;
    ref.rootp->t__DOT__array_value[0] = opt.rootp->t__DOT__array_value[0] = 0;
    ref.rootp->t__DOT__array_value[1] = opt.rootp->t__DOT__array_value[1] = 0;

    for (uint32_t n = 0; n < 64; ++n) {
        ref.x = opt.x = 0;
        ref.z = opt.z = 0;
        ref.rootp->t__DOT__constant_value = opt.rootp->t__DOT__constant_value = 0;
        ref.rootp->t__DOT__feedback_value = opt.rootp->t__DOT__feedback_value = 0;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__constant_value, 0);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__feedback_value, 0);

        // Public writes with unchanged ordinary inputs.
        ref.rootp->t__DOT__constant_value = opt.rootp->t__DOT__constant_value = 1;
        ref.rootp->t__DOT__feedback_value = opt.rootp->t__DOT__feedback_value = 1;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__constant_value, TEST_GLOBAL ? 0 : 1);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__feedback_value, TEST_GLOBAL ? 0 : 1);

        // Changing z causes both processes to overwrite the public values again.
        ref.z = opt.z = 1;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__constant_value, 0);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__feedback_value, 0);

        ref.rootp->t__DOT__constant_value = opt.rootp->t__DOT__constant_value = 1;
        ref.z = opt.z = 0;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__constant_value, 0);

        ref.x = opt.x = 1;
        ref.z = opt.z = 1;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.constant_out, 1);
        TEST_CHECK_EQ(+opt.feedback_out, 1);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__constant_value, 0);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__feedback_value, 1);

        ref.rootp->t__DOT__constant_value = opt.rootp->t__DOT__constant_value = 0;
        ref.rootp->t__DOT__feedback_value = opt.rootp->t__DOT__feedback_value = 0;
        ref.z = opt.z = 0;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.constant_out, 0);
        TEST_CHECK_EQ(+opt.feedback_out, 0);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__feedback_value, 1);
        if (errors) return 1;
        ctx.timeInc(1);
    }

    for (uint32_t n = 0; n < 256; ++n) {
        // Vary the incoming low bit independently of the driven bit.
        const CData incoming = (37 * n + 17 + (n >> 1)) & 0x7f;
        ref.data = opt.data = (n ^ 0x55) & 0x7f;
        ref.rootp->t__DOT__packed_value = opt.rootp->t__DOT__packed_value = incoming;
        ref.rootp->t__DOT__array_value[0] = opt.rootp->t__DOT__array_value[0] = incoming;
        ref.rootp->t__DOT__array_value[1] = opt.rootp->t__DOT__array_value[1] = incoming ^ 0x7f;
        evaluate(ref, opt);
        TEST_CHECK_EQ(+opt.packed_out, (incoming & 0x7e) | (opt.data & 1));
        TEST_CHECK_EQ(+opt.rootp->t__DOT__packed_value, (incoming & 0x7e) | ((~opt.data) & 1));
        TEST_CHECK_EQ(+opt.rootp->t__DOT__array_value[0], (~opt.data) & 0x7f);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__array_value[1], incoming ^ 0x7f);
        TEST_CHECK_EQ(+opt.array_out, incoming ^ 0x7f);

        const CData retained = incoming ^ 0x7e;
        const CData packedBefore = opt.packed_out;
        const CData arrayBefore = opt.array_out;
        ref.rootp->t__DOT__packed_value = opt.rootp->t__DOT__packed_value = retained;
        ref.rootp->t__DOT__array_value[1] = opt.rootp->t__DOT__array_value[1] = retained;
        evaluate(ref, opt);
        // With selective marking, these writes alone do not rerun the processes.
        TEST_CHECK_EQ(+opt.packed_out,
                      TEST_GLOBAL ? ((retained & 0x7e) | (opt.data & 1)) : packedBefore);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__packed_value,
                      TEST_GLOBAL ? ((retained & 0x7e) | ((~opt.data) & 1)) : retained);
        TEST_CHECK_EQ(+opt.rootp->t__DOT__array_value[1], retained);
        TEST_CHECK_EQ(+opt.array_out, TEST_GLOBAL ? retained : arrayBefore);
        evaluate(ref, opt);
        if (errors) return 1;
        ctx.timeInc(1);
    }
    ref.final();
    opt.final();
    std::cout << "*-* All Finished *-*\n";
}
