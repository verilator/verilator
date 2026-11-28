// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets of the top module, one read at every operand position (t) and one through a
// continuous assignment (v), and a target named like a function argument (s.val, not bound)
module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] t = 0;
  logic [7:0] r = 0;
  logic [7:0] mem[4];
  logic [7:0] o_alone, o_left, o_right, o_nested, o_func, o_comb;

  logic [7:0] a = 8'd10;
  logic [7:0] q;
  logic [7:0] v;

  logic [7:0] fa = 8'd3;
  logic [7:0] fq;
  sub s (.a(fa), .q(fq));

  function automatic logic [7:0] sub8(input logic [7:0] a, input logic [7:0] b);
    return a - b;
  endfunction

  initial for (int i = 0; i < 4; i++) mem[i] = 0;

  assign o_alone = t;
  assign o_left = t ^ r;
  assign o_right = r ^ t;
  assign o_nested = (r + 8'd1) ^ (8'h0f & t);
  assign o_func = sub8(r, t);
  always_comb o_comb = r + t;

  always_comb v = a + 8'd2;
  assign q = v;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    t <= 8'h10 + cyc[7:0];
    r <= 8'h3c ^ cyc[7:0];
    mem[t[1:0]] <= 8'ha0 + cyc[7:0];
    fa <= fa + 1;
    $display("[%0d] alone=%02x left=%02x right=%02x nested=%02x func=%02x comb=%02x mem=%02x %02x %02x %02x",
             cyc, o_alone, o_left, o_right, o_nested, o_func, o_comb, mem[0], mem[1], mem[2],
             mem[3]);
    $display("$[%0d| q: %0d]", cyc, q);
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
  logic [7:0] val;

  function automatic [7:0] scale(input [7:0] val);
    scale = val << 1;
  endfunction

  assign val = a + 8'd1;
  assign q   = scale(val);
endmodule
