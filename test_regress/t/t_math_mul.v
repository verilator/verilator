// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2006 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc=0;
   reg [63:0] crc;
   reg [63:0] sum;

   reg [31:0] out1;
   sub sub (.in1(crc[15:0]), .in2(crc[31:16]), .out1(out1));

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%x sum=%x out=%x\n",$time, cyc, crc, sum, out1);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= {sum[62:0], sum[63]^sum[2]^sum[0]} ^ {32'h0,out1};
      if (cyc==1) begin
	 // Setup
	 crc <= 64'h00000000_00000097;
	 sum <= 64'h0;
      end
      else if (cyc==90) begin
	 if (sum != 64'hc1f743ad62c2c04d) $stop;
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
   out1,
   // Inputs
   in1, in2
   );

   input      [15:0] in1;
   input      [15:0] in2;
   output reg [31:0] out1;
   
   always @* begin
      // verilator lint_off WIDTH
      out1 = $signed(in1) * $signed(in2);
      // verilator lint_on WIDTH
   end
   
endmodule
