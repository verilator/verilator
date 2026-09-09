// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets in two instances of one module (s0, s1), and in instances of two sibling modules
// (ia, ib), each bound with its own case
module top_module;
  logic       clk = 0;
  logic [7:0] a = 8'd10;
  logic [7:0] q0, q1;
  logic [7:0] qa, qb;

  sub s0 (.a(a), .q(q0));
  sub s1 (.a(a), .q(q1));
  subA ia (.a(a), .q(qa));
  subB ib (.a(a), .q(qb));

  int cyc = 0;
  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| q0: %0d q1: %0d]", cyc, q0, q1);
    $display("$[%0d| qa: %0d qb: %0d]", cyc, qa, qb);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

module sub (
  input  logic [7:0] a,
  output logic [7:0] q
);
  logic [7:0] v;
  always_comb v = a + 8'd2;
  assign q = v;
endmodule

module subA (
  input  logic [7:0] a,
  output logic [7:0] q
);
  logic [7:0] va;
  always_comb va = a + 8'd2;
  assign q = va;
endmodule

module subB (
  input  logic [7:0] a,
  output logic [7:0] q
);
  logic [7:0] vb;
  always_comb vb = a + 8'd3;
  assign q = vb;
endmodule
