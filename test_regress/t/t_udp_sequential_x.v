// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Michael Bikovitsky.
// SPDX-License-Identifier: CC0-1.0

module t (
    input wire clk
);

  wire q1;
  pos i_pos (
      q1,
      clk
  );

  wire q2;
  neg i_neg (
      q2,
      clk
  );

  integer cycle = 0;
  always @(posedge clk) begin
    if (cycle == 10) $finish;
    cycle <= cycle + 1;
  end

  always @(q1 or q2) begin
    // q1 should be assigned to 0 on every posedge and to X otherwise.
    // So when the value of q1 changes, *and* clk is positive, we expect
    // q1 to be 1.
    // Same for q2, but on the negedge.
    if (clk && q1) $stop;
    if (!clk && q2) $stop;
  end

endmodule

primitive pos(q, clk);
  output q;
  reg q;
  input clk;
  table
    (01) : ? : 0;
    // Explicitly set the output to X on clk 0->X edge.
    // This edge can never happen in Verilator.
    // If all edges *from* 0 are treated as rising edges, this will cause
    // the output to be 1, since we use --x-assign 1, and the test will fail.
    // (Actually this depends on the evaluation order of the always blocks
    // that V3Udp.cpp creates, but at the time of writing they seem to be
    // evaluated in the order of the lines in the table.)
    (0x) : ? : x;
  endtable
endprimitive

primitive neg(q, clk);
  output q;
  reg q;
  input clk;
  table
    (10) : ? : 0;
    // Explicitly set the output to X on clk X->0 edge.
    // This edge can never happen in Verilator.
    // If all edges *to* 0 are treated as falling edges, this will cause
    // the output to be 1, since we use --x-assign 1, and the test will fail.
    // (Actually this depends on the evaluation order of the always blocks
    // that V3Udp.cpp creates, but at the time of writing they seem to be
    // evaluated in the order of the lines in the table.)
    (x0) : ? : x;
  endtable
endprimitive
