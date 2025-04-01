// DESCRIPTION: Verilator: Multiple `defines while using +define+
// as a command-line argument as well
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define TEST_MACRO 10
`define TEST_MACRO 100
module test (
);
    initial begin
        $display("TEST_MACRO %d", `TEST_MACRO);
        $finish;
    end

endmodule
