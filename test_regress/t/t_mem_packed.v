// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc; initial cyc = 0;
`ifdef iverilog
   reg [7:0] arr [3:0];
`else
   reg [3:0] [7:0] arr;
`endif
   reg [7:0] sum;
   integer    i0;

   initial begin
      for (i0=0; i0<5; i0=i0+1) begin
	 arr[i0] = 1 << i0[1:0];
      end
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
	 // Setup
	 sum <= 0;
      end
      else if (cyc >= 10 && cyc < 14) begin
	 sum <= sum + {4'b0,arr[cyc-10]};
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d sum=%x\n",$time, cyc, sum);
	 if (sum != 8'h0f) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
