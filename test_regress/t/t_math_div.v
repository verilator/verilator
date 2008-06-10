// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2004 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [255:0] 		a;
   reg [60:0] 		divisor;
   reg [60:0] 		qq;
   reg [60:0] 		rq;
   reg signed [60:0] 	qqs;
   reg signed [60:0] 	rqs;

   always @* begin
      qq = a[60:0] / divisor;
      rq = a[60:0] % divisor;
      qqs = $signed(a[60:0]) / $signed(divisor);
      rqs = $signed(a[60:0]) % $signed(divisor);
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
	 cyc <= cyc + 1;
	 //$write("%d: %x %x %x %x\n", cyc, qq, rq, qqs, rqs);
	 if (cyc==1) begin
	    a <= 256'hed388e646c843d35de489bab2413d77045e0eb7642b148537491f3da147e7f26;
	    divisor <= 61'h12371;
	    a[60] <= 1'b0; divisor[60] <= 1'b0;  // Unsigned
	 end
	 if (cyc==2) begin
	    a <= 256'h0e17c88f3d5fe51a982646c8e2bd68c3e236ddfddddbdad20a48e039c9f395b8;
	    divisor <= 61'h1238123771;
	    a[60] <= 1'b0; divisor[60] <= 1'b0;  // Unsigned
	    if (qq!==61'h00000403ad81c0da) $stop;
	    if (rq!==61'h00000000000090ec) $stop;
	    if (qqs!==61'h00000403ad81c0da) $stop;
	    if (rqs!==61'h00000000000090ec) $stop;
	 end
	 if (cyc==3) begin
	    a <= 256'h0e17c88f00d5fe51a982646c8002bd68c3e236ddfd00ddbdad20a48e00f395b8;
	    divisor <= 61'hf1b;
	    a[60] <= 1'b1; divisor[60] <= 1'b0;  // Signed
	    if (qq!==61'h000000000090832e) $stop;
	    if (rq!==61'h0000000334becc6a) $stop;
	    if (qqs!==61'h000000000090832e) $stop;
	    if (rqs!==61'h0000000334becc6a) $stop;
	 end
	 if (cyc==4) begin
	    a[60] <= 1'b0; divisor[60] <= 1'b1;  // Signed
	    if (qq!==61'h0001eda37cca1be8) $stop;
	    if (rq!==61'h0000000000000c40) $stop;
	    if (qqs!==61'h1fffcf5187c76510) $stop;
	    if (rqs!==61'h1ffffffffffffd08) $stop;
	 end
	 if (cyc==5) begin
	    a[60] <= 1'b1; divisor[60] <= 1'b1;  // Signed
	    if (qq!==61'h0000000000000000) $stop;
	    if (rq!==61'h0d20a48e00f395b8) $stop;
	    if (qqs!==61'h0000000000000000) $stop;
	    if (rqs!==61'h0d20a48e00f395b8) $stop;
	 end
	 if (cyc==6) begin
	    if (qq!==61'h0000000000000001) $stop;
	    if (rq!==61'h0d20a48e00f3869d) $stop;
	    if (qqs!==61'h0000000000000000) $stop;
	    if (rqs!==61'h1d20a48e00f395b8) $stop;
	 end
	 // Div by zero
	 if (cyc==9) begin
	    divisor <= 61'd0;
	 end
	 if (cyc==10) begin
`ifdef verilator
	    if (qq !== {61{1'b0}}) $stop;
	    if (rq !== {61{1'b0}}) $stop;
`else
	    if (qq !== {61{1'bx}}) $stop;
	    if (rq !== {61{1'bx}}) $stop;
`endif
	    if ({16{1'bx}} !== 16'd1/16'd0) $stop;  // No div by zero errors
	    if ({16{1'bx}} !== 16'd1%16'd0) $stop;  // No div by zero errors
	 end
	 if (cyc==19) begin
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end
endmodule
