// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Test:
   tri 	t;
   bufif1 (t, crc[1], cyc[1:0]==2'b00);
   bufif1 (t, crc[2], cyc[1:0]==2'b10);

   tri0 t0;
   bufif1 (t0, crc[1], cyc[1:0]==2'b00);
   bufif1 (t0, crc[2], cyc[1:0]==2'b10);

   tri1 t1;
   bufif1 (t1, crc[1], cyc[1:0]==2'b00);
   bufif1 (t1, crc[2], cyc[1:0]==2'b10);

   tri 	t2;
   t_tri2 t_tri2 (.t2, .d(crc[1]), .oe(cyc[1:0]==2'b00));
   bufif1 (t2, crc[2], cyc[1:0]==2'b10);

   tri 	t3;
   t_tri3 t_tri3 (.t3, .d(crc[1]), .oe(cyc[1:0]==2'b00));
   bufif1 (t3, crc[2], cyc[1:0]==2'b10);

   wire [63:0] 	result = {51'h0, t3, 3'h0,t2, 3'h0,t1, 3'h0,t0};

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
	 sum <= 64'h0;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h04f91df71371e950
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module t_tri2 (/*AUTOARG*/
   // Outputs
   t2,
   // Inputs
   d, oe
   );
   output t2;
   input  d;
   input  oe;
   tri1   t2;
   bufif1 (t2, d, oe);
endmodule

module t_tri3 (/*AUTOARG*/
   // Outputs
   t3,
   // Inputs
   d, oe
   );
   output tri1 t3;
   input  d;
   input  oe;
   bufif1 (t3, d, oe);
endmodule
