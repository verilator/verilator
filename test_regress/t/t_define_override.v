// DESCRIPTION: Verilator: Multiple `defines while using +define+
// as a command-line argument as well
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define TEST_MACRO 10
`define TEST_MACRO 100

`define STRINGIFY(x) `"x`"

module test ();
  initial begin
    $display("TEST_MACRO %s", `STRINGIFY(`TEST_MACRO));
    $finish;
  end

endmodule
