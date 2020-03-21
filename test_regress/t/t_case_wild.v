// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   reg 	      out1;
   reg [4:0]  out2;
   sub sub (.in(crc[23:0]), .out1(out1), .out2(out2));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%x sum=%x out=%x,%x\n",$time, cyc, crc, sum, out1,out2);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {sum[62:0], sum[63]^sum[2]^sum[0]} ^ {58'h0,out1,out2};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h00000000_00000097;
	 sum <= 64'h0;
      end
      else if (cyc==90) begin
	 if (sum !== 64'hf0afc2bfa78277c5) $stop;
      end
      else if (cyc==91) begin
      end
      else if (cyc==92) begin
      end
      else if (cyc==93) begin
      end
      else if (cyc==94) begin
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module sub (/*AUTOARG*/
   // Outputs
   out1, out2,
   // Inputs
   in
   );

   input      [23:0] in;
   output reg 	     out1;
   output reg [4:0]  out2;

   always @* begin
      // Test empty cases
      casez (in[0])
      endcase
      casez (in)
	24'b0000_0000_0000_0000_0000_0000 : {out1,out2} = {1'b0,5'h00};
	24'b????_????_????_????_????_???1 : {out1,out2} = {1'b1,5'h00};
	24'b????_????_????_????_????_??10 : {out1,out2} = {1'b1,5'h01};
	24'b????_????_????_????_????_?100 : {out1,out2} = {1'b1,5'h02};
	24'b????_????_????_????_????_1000 : {out1,out2} = {1'b1,5'h03};
	24'b????_????_????_????_???1_0000 : {out1,out2} = {1'b1,5'h04};
	24'b????_????_????_????_??10_0000 : {out1,out2} = {1'b1,5'h05};
	24'b????_????_????_????_?100_0000 : {out1,out2} = {1'b1,5'h06};
	24'b????_????_????_????_1000_0000 : {out1,out2} = {1'b1,5'h07};
	// Same pattern, but reversed to test we work OK.
	24'b1000_0000_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h17};
	24'b?100_0000_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h16};
	24'b??10_0000_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h15};
	24'b???1_0000_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h14};
	24'b????_1000_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h13};
	24'b????_?100_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h12};
	24'b????_??10_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h11};
	24'b????_???1_0000_0000_0000_0000 : {out1,out2} = {1'b1,5'h10};
	24'b????_????_1000_0000_0000_0000 : {out1,out2} = {1'b1,5'h0f};
	24'b????_????_?100_0000_0000_0000 : {out1,out2} = {1'b1,5'h0e};
	24'b????_????_??10_0000_0000_0000 : {out1,out2} = {1'b1,5'h0d};
	24'b????_????_???1_0000_0000_0000 : {out1,out2} = {1'b1,5'h0c};
	24'b????_????_????_1000_0000_0000 : {out1,out2} = {1'b1,5'h0b};
	24'b????_????_????_?100_0000_0000 : {out1,out2} = {1'b1,5'h0a};
	24'b????_????_????_??10_0000_0000 : {out1,out2} = {1'b1,5'h09};
	24'b????_????_????_???1_0000_0000 : {out1,out2} = {1'b1,5'h08};
      endcase
   end

endmodule
