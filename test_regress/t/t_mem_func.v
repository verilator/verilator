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
   reg [63:0] 	sum;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [2:0]		q;			// From test of Test.v
   // End of automatics

   Test test (
	      // Outputs
	      .q			(q[2:0]),
	      // Inputs
	      .clk			(clk),
	      .reset_l			(crc[0]),
	      .enable			(crc[2]),
	      .q_var0			(crc[19:10]),
	      .q_var2			(crc[29:20]),
	      .q_var4			(crc[39:30]),
	      .q_var6			(crc[49:40])
	      /*AUTOINST*/);

   // Aggregate outputs into a single result vector
   wire [63:0] result = {61'h0,q};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
`define EXPECTED_SUM 64'h58b162c58d6e35ba
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule


module Test
  (
   input               clk,
   input               reset_l,
   input               enable,

   input       [ 9:0]  q_var0,
   input       [ 9:0]  q_var2,
   input       [ 9:0]  q_var4,
   input       [ 9:0]  q_var6,

   output reg  [2:0]   q
   );

   reg [7:0] 	       p1_r [6:0];

   always @(posedge clk) begin
      if (!reset_l) begin
         p1_r[0]       <= 'b0;
         p1_r[1]       <= 'b0;
         p1_r[2]       <= 'b0;
         p1_r[3]       <= 'b0;
         p1_r[4]       <= 'b0;
         p1_r[5]       <= 'b0;
         p1_r[6]       <= 'b0;
      end
      else if (enable) begin : pass1
         match(q_var0, q_var2, q_var4, q_var6);
      end
   end

   // verilator lint_off WIDTH
   always @(posedge clk) begin : l
      reg [10:0]  bd;
      reg [3:0]   idx;

      q = 0;
      bd = 0;
      for (idx=0; idx<7; idx=idx+1) begin
	 q       = idx+1;
	 bd    = bd + p1_r[idx];
      end
   end


   task match;
      input   [9:0]   p0, p1, p2, p3;
      reg [9:0]       p[3:0];
      begin
	 p[0]  = p0;
	 p[1]  = p1;
	 p[2]  = p2;
	 p[3]  = p3;
	 p1_r[0] = p[0];
	 p1_r[1] = p[1];
      end
   endtask
endmodule
