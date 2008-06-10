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

   integer 		i;
   reg [63:0] 		mem [7:0];

   always @ (posedge clk) begin
      if (cyc==1) begin
	 for (i=0; i<8; i=i+1) begin
	    mem[i] <= 64'h0;
	 end
      end
      else begin
	 mem[0] <= crc;
	 for (i=1; i<8; i=i+1) begin
	    mem[i] <= mem[i-1];
	 end
      end
   end

   wire [63:0] outData = mem[7];

   always @ (posedge clk) begin
      //$write("[%0t] cyc==%0d crc=%b q=%x\n",$time, cyc, crc, outData);
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
      end
      else if (cyc==90) begin
	 if (outData != 64'h1265e3bddcd9bc27) $stop;
      end
      else if (cyc==91) begin
	 if (outData != 64'h24cbc77bb9b3784e) $stop;
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
