// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef int T;

module test;

  task t4;
    input [7:0] bad4;
    reg bad4;
    reg bad4;  // <--- Error (duplicate)
  endtask

  task t5;
    input [7:0] bad5;
    input [7:0] bad5;  // <--- Error (duplicate)
    reg bad5;
  endtask

endmodule
