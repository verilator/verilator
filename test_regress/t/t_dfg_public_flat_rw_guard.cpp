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

struct Fixture final {
    VerilatedContext ctx;
    Vref ref{&ctx};
    Vopt opt{&ctx};
    const char* phasep = "initialization";

#include "signals.h"

    void check(const char* namep, QData got, QData expected) const {
        if (got != expected) std::cout << "%Error: " << phasep << ": " << namep << '\n';
        TEST_CHECK_EQ(got, expected);
    }

    void evaluate(const char* nextPhasep) {
        phasep = nextPhasep;
        ref.eval();
        opt.eval();
#include "checks.h"
        if (errors) std::exit(1);
    }
};

int main(int, char**) {
    Fixture t;
    t.data(0);
    t.packed_value(0);
    t.array_value_2(0);
    t.array_value_3(0);

    for (uint32_t n = 0; n < 64; ++n) {
        t.x(0);
        t.z(0);
        t.constant_value(0);
        t.feedback_value(0);
        t.evaluate("initialize scalars");
        t.expect_constant_value(0);
        t.expect_feedback_value(0);

        // Public writes with unchanged ordinary inputs.
        t.constant_value(1);
        t.feedback_value(1);
        t.evaluate("write public scalars");
        t.expect_constant_value(TEST_GLOBAL ? 0 : 1);
        t.expect_feedback_value(TEST_GLOBAL ? 0 : 1);

        // Changing z causes both processes to overwrite the public values again.
        t.z(1);
        t.evaluate("raise z");
        t.expect_constant_value(0);
        t.expect_feedback_value(0);

        t.constant_value(1);
        t.z(0);
        t.evaluate("write constant and lower z");
        t.expect_constant_value(0);

        t.x(1);
        t.z(1);
        t.evaluate("raise x and z");
        t.expect_constant_out(1);
        t.expect_feedback_out(1);
        t.expect_constant_value(0);
        t.expect_feedback_value(1);

        t.constant_value(0);
        t.feedback_value(0);
        t.z(0);
        t.evaluate("write zero and lower z");
        t.expect_constant_out(0);
        t.expect_feedback_out(0);
        t.expect_feedback_value(1);
        if (errors) return 1;
        t.ctx.timeInc(1);
    }

    for (uint32_t n = 0; n < 256; ++n) {
        // Vary the incoming low bit independently of the driven bit.
        const CData incoming = (37 * n + 17 + (n >> 1)) & 0x7f;
        t.data((n ^ 0x55) & 0x7f);
        t.packed_value(incoming);
        t.array_value_2(incoming);
        t.array_value_3(incoming ^ 0x7f);
        t.evaluate("write retained state and data");
        t.expect_packed_out((incoming & 0x7e) | (t.data() & 1));
        t.expect_packed_value((incoming & 0x7e) | ((~t.data()) & 1));
        t.expect_array_value_2((~t.data()) & 0x7f);
        t.expect_array_value_3(incoming ^ 0x7f);
        t.expect_array_out(incoming ^ 0x7f);

        const CData retained = incoming ^ 0x7e;
        const CData packedBefore = t.packed_out();
        const CData arrayBefore = t.array_out();
        t.packed_value(retained);
        t.array_value_3(retained);
        t.evaluate("write retained state only");
        // With selective marking, these writes alone do not rerun the processes.
        t.expect_packed_out(TEST_GLOBAL ? ((retained & 0x7e) | (t.data() & 1)) : packedBefore);
        t.expect_packed_value(TEST_GLOBAL ? ((retained & 0x7e) | ((~t.data()) & 1)) : retained);
        t.expect_array_value_3(retained);
        t.expect_array_out(TEST_GLOBAL ? retained : arrayBefore);
        t.evaluate("repeat unchanged evaluation");
        if (errors) return 1;
        t.ctx.timeInc(1);
    }
    t.ref.final();
    t.opt.final();
    std::cout << "*-* All Finished *-*\n";
}
