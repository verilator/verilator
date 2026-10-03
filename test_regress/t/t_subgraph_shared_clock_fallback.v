// DESCRIPTION: Verilator: Shared child output used as a parent clock falls back
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
  input logic clk
);
  int unsigned cycles = 0;
  wire q0;
  wire q1;
  int unsigned count = 0;

  sg_shared_clock_fallback i0 (.clk(clk), .d(~q0), .q(q0));
  sg_shared_clock_fallback i1 (.clk(clk), .d(q0), .q(q1));

  always_ff @(posedge q1) count <= count + 1;
  always @(posedge clk) begin
    if (cycles == 12) begin
      $write("count=%0d q0=%0d q1=%0d\n", count, q0, q1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
    cycles <= cycles + 1;
  end
endmodule

module sg_shared_clock_fallback (
  input logic clk,
  input logic d,
  output logic q = 0
);
  /*verilator subgraph_boundary*/
  always_ff @(posedge clk) q <= d;
endmodule
