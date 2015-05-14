// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=0;

   wire signed [7:0] sgn_wide;
   wire [7:0] 	     unsgn_wide;
   
   // The instantiation will Z extend, not sign extend
   // verilator lint_off WIDTH
   sub sub (.clk,
	    .sgn(sgn_wide), .unsgn(unsgn_wide),
	    .iss(3'sh7), .isu(3'h7),
	    .ius(3'sh7), .iuu(3'h7));
   // verilator lint_on WIDTH

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("out: 'b%b 'b%b\n", sgn_wide, unsgn_wide);
`endif
      if (sgn_wide[2:0] != 3'sh7) $stop;
      if (unsgn_wide[2:0] != 3'h7) $stop;
      // Simulators differ here.
      if (sgn_wide     !== 8'sbzzzzz111  // z-extension - NC
	  && sgn_wide  !== 8'sb11111111) $stop;  // sign extension - VCS
      if (unsgn_wide   !== 8'sbzzzzz111
	  && unsgn_wide!== 8'sb00000111) $stop;
      cyc <= cyc + 1;
      if (cyc==3) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule

module sub (
	    input clk,
	    output wire signed [2:0] sgn,
	    output wire [2:0] unsgn,
	    input signed [7:0] iss,
	    input signed [7:0] isu,
	    input [7:0] ius,
	    input [7:0] iuu);
   assign sgn = 3'sh7;
   assign unsgn = 3'h7;
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("in: %x %x %x %x\n", iss, isu, ius, iuu);
      if (iss != 8'hff) $stop;
      if (isu != 8'h07) $stop;
      if (ius != 8'hff) $stop;
      if (iuu != 8'h07) $stop;
`endif
   end

endmodule
