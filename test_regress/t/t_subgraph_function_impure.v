// DESCRIPTION: Verilator: Function with side effects requires fallback
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic clk,
  input logic [6:0] d,
  output wire [6:0] q
);
  sg_function_state i0 (.clk(clk), .d(d), .q(q));
endmodule

module sg_function_state (
  input logic clk,
  input logic [6:0] d,
  output logic [6:0] q = 7'd1
);
  /*verilator subgraph_boundary*/
  function automatic logic [6:0] advance(input logic [6:0] old_q,
                                          input logic [6:0] value);
    // verilator no_inline_task
    $display("advance=%0h", old_q);
    return old_q + value + 7'd1;
  endfunction

  always_ff @(posedge clk) q <= advance(q, d);
endmodule
