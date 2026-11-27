// DESCRIPTION: Verilator: Shared class fields with different publication owners
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk,
    input [31:0] a[2],
    output [32768:0] q[2],
    output [31:0] auxiliary[2]
);
  lane u0 (
      clk,
      a[0],
      q[0],
      auxiliary[0]
  );
  lane u1 (
      clk,
      a[1],
      q[1],
      auxiliary[1]
  );
endmodule

module lane (
    input clk,
    input [31:0] a,
    output logic [32768:0] q,
    output logic [31:0] auxiliary
);
  /* verilator no_inline_module */
  // Wide state makes publication substantial enough to dispatch to workers.
  logic [32768:0] state = 0;
  always @(posedge clk) begin
    state <= {state[32736:0], a};
    q <= state;
    auxiliary <= a;
  end
endmodule
