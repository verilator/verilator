// DESCRIPTION: Verilator: Partition-local temporaries with repeated module instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input [31:0] a[2],
    b[2],
    c[2],
    output [127:0] q[2]
);
  lane u0 (
      clk,
      a[0],
      b[0],
      c[0],
      q[0]
  );
  lane u1 (
      clk,
      a[1],
      b[1],
      c[1],
      q[1]
  );
endmodule

module lane (
    input clk,
    input [31:0] a,
    b,
    c,
    output logic [127:0] q
);
  /* verilator no_inline_module */
  logic [31:0] state = 0;
  logic [31:0] other = 0;
  always @(posedge clk) begin
    state <= a ^ b ^ c;
    other <= state + a;
    // Repeated subexpressions must retain each instance's old state.
    q <= {b, b, ((other ^ (state & c)) ^ state) | ((other ^ (state & c)) + state), c ^ a};
  end
endmodule
