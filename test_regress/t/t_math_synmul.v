// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;

   reg		negate;
   reg		enable;

   wire [31:0]  datA = crc[31:0];
   wire [31:0]  datB = crc[63:32];

   // Predict result
   wire [63:0] 	muled = (negate ? (- {32'h0,datA} * {32'h0,datB})
			 :        (  {32'h0,datA} * {32'h0,datB}));
   reg [63:0] 	muled_d1;
   reg [63:0] 	muled_d2;
   reg [63:0] 	muled_d3;
   reg [63:0] 	muled_d4;
   reg 		enable_d1;
   reg 		enable_d2;
   reg 		enable_d3;
   always @ (posedge clk) enable_d1 <= enable;
   always @ (posedge clk) enable_d2 <= enable_d1;
   always @ (posedge clk) enable_d3 <= enable_d2;
   always @ (posedge clk) if (enable) muled_d1 <= muled;
   always @ (posedge clk) if (enable_d1) muled_d2 <= muled_d1;
   always @ (posedge clk) if (enable_d2) muled_d3 <= muled_d2;
   always @ (posedge clk) if (enable_d3) muled_d4 <= muled_d3;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [64:0]		product_d4;		// From test of t_math_synmul_mul.v
   // End of automatics

   t_math_synmul_mul test (/*AUTOINST*/
			    // Outputs
			    .product_d4		(product_d4[64:0]),
			    // Inputs
			    .clk		(clk),
			    .enable		(enable),
			    .negate		(negate),
			    .datA		(datA[31:0]),
			    .datB		(datB[31:0]));

   integer cycs_enabled;  initial cycs_enabled = 0;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x e=%x n=%x  a*b=%x synmul=%x\n",$time, cyc,
	     crc, enable, negate, muled_d4, product_d4[63:0]);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      negate <= 1'b0;  // Negation not currently supported

      // Always enable in low cycle counts to clear out the pipe
      //enable <= 1'b1;  // 100% activity factor
      enable <= (cyc<10 || cyc[4]);  // 50% activity factor
      //enable <= (cyc<10 || cyc[4]&cyc[3]);  // 25% activity factor

      if (enable) cycs_enabled=cycs_enabled+1;
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
      end
      else begin
	 if (product_d4[63:0] !== muled_d4) begin
	    $write("[%0t] BAD product, got=%x exp=%x\n",$time, product_d4[63:0], muled_d4);
	    $stop;
	 end
	 if (cyc==99) begin
	    if (crc !== 64'hc77bb9b3784ea091) $stop;
	 end
`ifndef SIM_CYCLES
 `define SIM_CYCLES 99
`endif
	 if (cyc==`SIM_CYCLES) begin
	    $write("- Cycles=%0d, Activity factor=%0d%%\n", cyc, ((cycs_enabled*100)/cyc));
	    $write("*-* All Finished *-*\n");
	    $finish;
	 end
      end
   end

endmodule
