// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire  b;
   reg 	 reset;
   integer 	cyc=0;

   Testit testit (/*AUTOINST*/
		  // Outputs
		  .b			(b),
		  // Inputs
		  .clk			(clk),
		  .reset		(reset));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc==0) begin
	 reset <= 1'b0;
      end
      else if (cyc<10) begin
	 reset <= 1'b1;
      end
      else if (cyc<90) begin
	 reset <= 1'b0;
      end
      else if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule

module Testit (clk, reset, b);
   input                  clk;
   input 		  reset;
   output 		  b;

   wire [0:0] 		  c;
   wire 		  my_sig;
   wire [0:0] 		  d;

   genvar 		     i;
   generate
      for(i = 0; i >= 0; i = i-1) begin: fnxtclk1
	 fnxtclk fnxtclk1
	   (.u(c[i]),
	    .reset(reset),
	    .clk(clk),
	    .w(d[i]) );
      end
   endgenerate

   assign b                    = d[0];
   assign c[0]                 = my_sig;
   assign my_sig               = 1'b1;

endmodule

module fnxtclk (u, reset, clk, w );
   input                    u;
   input 		    reset;
   input 		    clk;
   output reg 		    w;

   always @ (posedge clk or posedge reset) begin
      if (reset == 1'b1) begin
         w            <= 1'b0;
      end
      else begin
         w            <= u;
      end
   end

endmodule
