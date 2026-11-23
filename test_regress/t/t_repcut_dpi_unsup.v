// DESCRIPTION: Verilator: RepCut unsupported foreign scheduling boundaries
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (input bit clk, input int x, output int y);
`ifdef CONTEXT
  import "DPI-C" context function int repcut_external(input int x);
  always @(posedge clk) y <= repcut_external(x);
`elsif SHARED
  import "DPI-C" function int repcut_external(input int x);
  int shared_value;
  always @(posedge clk) shared_value = repcut_external(x);
  always @(posedge clk) y <= shared_value;
`elsif MEMORY
  import "DPI-C" function int repcut_external(input int x);
  int values [0:3];
  always @(posedge clk) begin
    values[x[1:0]] <= repcut_external(x);
    y <= values[x[1:0]];
  end
`else
  import "DPI-C" function int repcut_external(input int x);
  always_comb y = repcut_external(x);
`endif
endmodule
