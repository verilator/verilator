// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Outputs
   \escaped_normal , double__underscore, \9num , \bra[ket]slash/dash-colon:9backslash\done ,
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=1;

   output  \escaped_normal ;
   wire    \escaped_normal = cyc[0];

   output  double__underscore ;
   wire  double__underscore = cyc[0];

   // C doesn't allow leading non-alpha, so must escape
   output \9num ;
   wire \9num = cyc[0];

   output  \bra[ket]slash/dash-colon:9backslash\done ;
   wire \bra[ket]slash/dash-colon:9backslash\done = cyc[0];
   wire \wire = cyc[0];

   wire \check_alias = cyc[0];
   wire \check:alias = cyc[0];
   wire \check;alias = !cyc[0];

   // These are *different entities*, bug83
   wire [31:0] \a0.cyc = ~a0.cyc;
   wire [31:0] \other.cyc = ~a0.cyc;

   sub a0 (.cyc(cyc));

   sub \mod.with_dot (.cyc(cyc));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (escaped_normal != cyc[0]) $stop;
      if (\escaped_normal != cyc[0]) $stop;
      if (double__underscore != cyc[0]) $stop;
      if (\9num != cyc[0]) $stop;
      if (\bra[ket]slash/dash-colon:9backslash\done != cyc[0]) $stop;
      if (\wire != cyc[0]) $stop;
      if (\check_alias != cyc[0]) $stop;
      if (\check:alias != cyc[0]) $stop;
      if (\check;alias != !cyc[0]) $stop;
      if (\a0.cyc != ~cyc) $stop;
      if (\other.cyc != ~cyc) $stop;
      if (cyc==10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module sub (
	    input [31:0] cyc
	    );
endmodule
