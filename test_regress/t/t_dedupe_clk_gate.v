// DESCRIPTION: Verilator: Dedupe optimization test.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.

// Contributed 2012 by Varun Koyyalagunta, Centaur Technology.

module t(res,d,clk,en);
  output res;
  input d,en,clk;
  wire q0,q1,q2,q3;

  flop_gated_latch f0(q0,d,clk,en);
  flop_gated_latch f1(q1,d,clk,en);
  flop_gated_flop f2(q2,d,clk,en);
  flop_gated_flop f3(q3,d,clk,en);
  assign res = (q0 + q1) * (q2 - q3);
endmodule

module flop_gated_latch(q,d,clk,en);
  input d, clk, en;
  output q;
  wire gated_clock;
  clock_gate_latch clock_gate(gated_clock, clk, en);
  always @(posedge gated_clock) begin
      q <= d;
  end
endmodule

module flop_gated_flop(q,d,clk,en);
  input d, clk, en;
  output q;
  wire gated_clock;
  clock_gate_flop clock_gate(gated_clock, clk, en);
  always @(posedge gated_clock) begin
      q <= d;
  end
endmodule

module clock_gate_latch (gated_clk, clk, clken);
  output gated_clk;
  input clk, clken;
  reg clken_latched /*verilator clock_enable*/;
  assign gated_clk = clk & clken_latched ;

  wire clkb = ~clk;
  always @(clkb or clken)
    if(clkb) clken_latched = clken;

endmodule

module clock_gate_flop (gated_clk, clk, clken);
  output gated_clk;
  input clk, clken;
  reg clken_r /*verilator clock_enable*/;
  assign gated_clk = clk & clken_r ;

  always @(negedge clk)
    clken_r <= clken;

endmodule
