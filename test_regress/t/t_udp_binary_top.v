// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that a standalone primitive can be a top level module

primitive p(output id_2, input id_1);
  table
    1 : 0;
    0 : 1;
  endtable
endprimitive

module t;  // Overridden by --top-module
  initial $stop;
endmodule
