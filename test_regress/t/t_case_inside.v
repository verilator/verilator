// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
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
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x sum=%x  in[3:0]=%x  out=%x,%x\n",$time, cyc, crc, sum, crc[3:0], out1,out2);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {sum[62:0], sum[63]^sum[2]^sum[0]} ^ {58'h0,out1,out2};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h00000000_00000097;
	 sum <= 64'h0;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
`define EXPECTED_SUM 64'h10204fa5567c8a4b
	 if (sum !== `EXPECTED_SUM) $stop;
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
      case (in[3:0]) inside
	default:          {out1,out2} = {1'b0,5'h0F};   // Note not last item
	4'h1, 4'h2, 4'h3: {out1,out2} = {1'b1,5'h01};
	4'h4:             {out1,out2} = {1'b1,5'h04};
	[4'h6:4'h5]:        {out1,out2} = {1'b1,5'h05};  // order backwards, will not match
	4'b100?:/*8,9*/   {out1,out2} = {1'b1,5'h08};
	[4'hc:4'hf]:        {out1,out2} = {1'b1,5'h0C};
      endcase
   end

endmodule
