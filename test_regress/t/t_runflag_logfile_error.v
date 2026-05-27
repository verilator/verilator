// DESCRIPTION: Verilator: Verilog example module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// See also https://verilator.org/guide/latest/examples.html"

module top;
  initial begin
    $error("This is a generated error!");
    $finish;
  end
endmodule
