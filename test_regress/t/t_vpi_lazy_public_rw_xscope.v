// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Multi-instance cross-scope: a same-scope driver reconstructs, a
// cross-scope driver (reading into a child instance) retains instead.

// Non-inlined module shared as one C++ class.
module child (
  input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cy;
  assign cy = din ^ 8'hA5;  // Same-scope driver: reconstructs.
endmodule

// Non-inlined module shared as one C++ class.
module parent (
  input logic [7:0] din
);
  /*verilator no_inline_module*/
  child uc (.din(din));
  logic [7:0] py;
  assign py = uc.cy + 8'h03;  // Cross-scope driver (reads child): retains.
endmodule

module t (
  input logic clk,
  input logic [7:0] din0,
  input logic [7:0] din1,
  output logic [7:0] obs
);

  parent p0 (.din(din0));
  parent p1 (.din(din1));

  logic [7:0] acc;
  always_ff @(posedge clk) begin
    acc <= acc + p0.py + p1.py;
  end
  assign obs = acc;

endmodule
