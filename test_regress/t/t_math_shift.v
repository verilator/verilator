// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   ign,
   // Inputs
   clk
   );

   input clk;
   output [31:0] ign;

   reg [31:0] 		right;
   reg [31:0] 		left;
   reg [63:0] 		qright;
   reg [63:0] 		qleft;
   reg [31:0] 		amt;

   assign ign = {31'h0, clk} >>> 4'bx;  // bug760

   always @* begin
      right = 32'h819b018a >> amt;
      left  = 32'h819b018a << amt;
      qright = 64'hf784bf8f_12734089 >> amt;
      qleft  = 64'hf784bf8f_12734089 >> amt;
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
`ifdef TEST_VERBOSE
	 $write("%d %x %x %x %x\n", cyc, left, right, qleft, qright);
`endif
	 if (cyc==1) begin
	    amt <= 32'd0;
	    if (5'b10110>>2  != 5'b00101) $stop;
	    if (5'b10110>>>2 != 5'b00101) $stop;  // Note it cares about sign-ness
	    if (5'b10110<<2  != 5'b11000) $stop;
	    if (5'b10110<<<2 != 5'b11000) $stop;
	    if (5'sb10110>>2  != 5'sb00101) $stop;
	    if (5'sb10110>>>2 != 5'sb11101) $stop;
	    if (5'sb10110<<2  != 5'sb11000) $stop;
	    if (5'sb10110<<<2 != 5'sb11000) $stop;
	    // Allow >64 bit shifts if the shift amount is a constant
	    if ((64'sh458c2de282e30f8b >> 68'sh4) !== 64'sh0458c2de282e30f8) $stop;
	 end
	 if (cyc==2) begin
	    amt <= 32'd28;
	    if (left  != 32'h819b018a) $stop;
	    if (right != 32'h819b018a) $stop;
	    if (qleft  != 64'hf784bf8f_12734089) $stop;
	    if (qright != 64'hf784bf8f_12734089) $stop;
	 end
	 if (cyc==3) begin
	    amt <= 32'd31;
	    if (left  != 32'ha0000000) $stop;
	    if (right != 32'h8) $stop;
	    if (qleft  != 64'h0000000f784bf8f1) $stop;
	    if (qright != 64'h0000000f784bf8f1) $stop;
	 end
	 if (cyc==4) begin
	    amt <= 32'd32;
	    if (left  != 32'h0) $stop;
	    if (right != 32'h1) $stop;
	    if (qleft  != 64'h00000001ef097f1e) $stop;
	    if (qright != 64'h00000001ef097f1e) $stop;
	 end
	 if (cyc==5) begin
	    amt <= 32'd33;
	    if (left  != 32'h0) $stop;
	    if (right != 32'h0) $stop;
	    if (qleft  != 64'h00000000f784bf8f) $stop;
	    if (qright != 64'h00000000f784bf8f) $stop;
	 end
	 if (cyc==6) begin
	    amt <= 32'd64;
	    if (left  != 32'h0) $stop;
	    if (right != 32'h0) $stop;
	    if (qleft  != 64'h000000007bc25fc7) $stop;
	    if (qright != 64'h000000007bc25fc7) $stop;
	 end
	 if (cyc==7) begin
	    amt <= 32'd128;
	    if (left  != 32'h0) $stop;
	    if (right != 32'h0) $stop;
	    if (qleft  != 64'h0) $stop;
	    if (qright != 64'h0) $stop;
	 end
	 if (cyc==8) begin
	    if (left  != 32'h0) $stop;
	    if (right != 32'h0) $stop;
	    if (qleft  != 64'h0) $stop;
	    if (qright != 64'h0) $stop;
	 end
	 if (cyc==9) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
