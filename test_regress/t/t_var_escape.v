// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   \escaped_normal , double__underscore, \9num , \bra[ket]slash/dash-colon:9 ,
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

   output  \bra[ket]slash/dash-colon:9 ;
   wire \bra[ket]slash/dash-colon:9 = cyc[0];

   wire \check_alias = cyc[0];
   wire \check:alias = cyc[0];
   wire \check;alias = !cyc[0];

`ifndef verilator
   initial begin
      $dumpfile("obj_dir/t_var_escape/t_var_escape_dump.vcd");
      $dumpvars( 0, t );
      $dumpon;
   end
`endif

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (escaped_normal != cyc[0]) $stop;
      if (\escaped_normal != cyc[0]) $stop;
      if (double__underscore != cyc[0]) $stop;
      if (\9num != cyc[0]) $stop;
      if (\bra[ket]slash/dash-colon:9 != cyc[0]) $stop;
      if (\check_alias != cyc[0]) $stop;
      if (\check:alias != cyc[0]) $stop;
      if (\check;alias != !cyc[0]) $stop;

      if (cyc==10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
