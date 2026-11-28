// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A hook target inside a hierarchical block
module top_module;
  logic clk = 0;
  sub u_sub (.clk);
endmodule

module sub (
    input logic clk
);  /*verilator hier_block*/
  logic [7:0] target;
  always_ff @(posedge clk) target <= target + 1;
endmodule
