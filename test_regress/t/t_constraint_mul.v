// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

// Test multiplication operator in constraint expressions

module t;
    initial begin
        int a, b, c;
        int x, y, z;

        // Test 1: Simple multiplication constraint
        if (std::randomize(a, b, c) with { a == 5; b == 3; c == a * b; } != 1) $stop;
        if (c != 15) $stop;

        // Test 2: Multiplication with range constraints
        if (std::randomize(x, y, z) with {
            x >= 1; x <= 10;
            y >= 1; y <= 10;
            z == x * y;
        } != 1) $stop;
        if (z != x * y) $stop;

        // Test 3: Multiplication with inside operator
        if (std::randomize(x, y, z) with {
            x inside {[2:5]};
            y inside {[3:6]};
            z == x * y;
        } != 1) $stop;
        if (z != x * y) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
