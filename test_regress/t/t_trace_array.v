// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

module t (clk);
   input clk;
   integer 	cyc=0;

   // Trace would overflow at 256KB which is 256 kb dump, 16 kb in a chunk

   typedef struct packed {
      logic [1024*1024:0] d;
   } s1_t; // 128 b

   s1_t biggie;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      biggie [ cyc +: 32 ] <= 32'hfeedface;
      if (cyc == 5) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end
endmodule
