// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   q0, q1, q2, q3, q4, q5, q6a, q6b,
   // Inputs
   clk, d, rst0_n
   );
   input clk;
   input d;

   // OK -- from primary
   input rst0_n;
   output wire  q0;
   Flop flop0 (.q(q0), .rst_n(rst0_n), .clk(clk), .d(d));

   // OK -- from flop
   reg   rst1_n;
   always @ (posedge clk) rst1_n <= rst0_n;
   output wire  q1;
   Flop flop1 (.q(q1), .rst_n(rst1_n), .clk(clk), .d(d));

   // Bad - logic
   wire  rst2_bad_n = rst0_n | rst1_n;
   output wire  q2;
   Flop flop2 (.q(q2), .rst_n(rst2_bad_n), .clk(clk), .d(d));

   // Bad - logic in submodule
   wire  rst3_bad_n;
   Sub  sub (.z(rst3_bad_n), .a(rst0_n), .b(rst1_n));
   output wire  q3;
   Flop flop3 (.q(q3), .rst_n(rst3_bad_n), .clk(clk), .d(d));

   // OK - bit selection
   reg [3:0] rst4_n;
   always @ (posedge clk) rst4_n <= {4{rst0_n}};
   output wire  q4;
   Flop flop4 (.q(q4), .rst_n(rst4_n[1]), .clk(clk), .d(d));

   // Bad - logic, but waived
   // verilator lint_off CDCRSTLOGIC
   wire  rst5_waive_n = rst0_n & rst1_n;
   // verilator lint_on CDCRSTLOGIC
   output wire  q5;
   Flop flop5 (.q(q5), .rst_n(rst5_waive_n), .clk(clk), .d(d));

   // Bad - for graph test - logic feeds two signals, three destinations
   wire rst6_bad_n = rst0_n ^ rst1_n;
   wire rst6a_bad_n = rst6_bad_n ^ $c1("0");  // $c prevents optimization
   wire rst6b_bad_n = rst6_bad_n ^ $c1("1");
   output wire  q6a;
   output wire  q6b;
   Flop flop6a (.q(q6a), .rst_n(rst6a_bad_n), .clk(clk), .d(d));
   Flop flop6v (.q(q6b), .rst_n(rst6b_bad_n), .clk(clk), .d(d));

   initial begin
      $display("%%Error: Not a runnable test");
      $stop;
   end

endmodule

module Flop (
             input clk,
             input d,
             input rst_n,
             output logic q);

   always @ (posedge clk or negedge rst_n) begin
      if (!rst_n) q <= 1'b0;
      else q <= d;
   end
endmodule

module Sub (input a, b,
            output z);
   assign z = a|b;
endmodule
