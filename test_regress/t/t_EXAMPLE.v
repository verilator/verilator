// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//	$write("*-* All Finished *-*\n");
//	$finish
// on success, or $stop.
//
// **If you do not wish for your code to be released to the public
// please note it here**

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // Some inputs we'll set to random values
   reg [31:0] in_a;
   reg [31:0] in_b;

   // Some arbitrary function for testing
   // We'll test below that for each random in_a and in_b, we get a good out_a.
   wire [31:0] out_x = (in_a ^ in_b);

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
`ifdef TEST_VERBOSE
	 $write("%d %x %x %x\n", cyc, in_a, in_b, out_x);
`endif
	 if (cyc==1) begin
	    // Assign inputs randomly
	    in_a  <= 32'h89a14fab;
	    in_b <= 32'h7ab512fa;
	 end
	 if (cyc==2) begin
	    in_a  <= 32'hf4c11a42;
	    in_b <= 32'h359967c6;
	    // Verify output is correct
            if (out_x != 32'hf3145d51) $stop;
	 end
	 if (cyc==3) begin
	    in_a  <= 32'h58dca151;
	    in_b <= 32'hdc687b27;
            if (out_x != 32'hc1587d84) $stop;
	 end
	 if (cyc==4) begin
	    in_a  <= 32'h09df0bbb;
	    in_b <= 32'h0d0e7231;
            if (out_x != 32'h84b4da76) $stop;
	 end
	 if (cyc==5) begin
            if (out_x != 32'h04d1798a) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
