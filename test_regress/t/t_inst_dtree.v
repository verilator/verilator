// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

`ifdef INLINE_A //verilator inline_module
`else  //verilator no_inline_module
`endif

   bmod bsub3 (.clk, .n(3));
   bmod bsub2 (.clk, .n(2));
   bmod bsub1 (.clk, .n(1));
   bmod bsub0 (.clk, .n(0));
endmodule

module bmod
  (input  clk,
   input [31:0] n);

`ifdef INLINE_B //verilator inline_module
`else  //verilator no_inline_module
`endif

   cmod csub (.clk, .n);

endmodule

module cmod
  (input   clk, input [31:0] n);

`ifdef INLINE_C //verilator inline_module
`else  //verilator no_inline_module
`endif

   reg [31:0] clocal;
   always @ (posedge clk) clocal <= n;

   dmod dsub (.clk, .n);
endmodule

module dmod (input clk, input [31:0] n);

`ifdef INLINE_D //verilator inline_module
`else  //verilator no_inline_module
`endif

   reg [31:0] dlocal;
   always @ (posedge clk) dlocal <= n;

   int 	 cyc;
   always @(posedge clk) begin
      cyc <= cyc+1;
   end
   always @(posedge clk) begin
      if (cyc>10) begin
`ifdef TEST_VERBOSE $display("%m: csub.clocal=%0d  dlocal=%0d", csub.clocal, dlocal); `endif
	 if (csub.clocal !== n) $stop;
	 if (dlocal !== n) $stop;
      end
      if (cyc==99) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
