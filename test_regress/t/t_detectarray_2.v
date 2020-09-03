// DESCRIPTION: Verilator: Simple test of unoptflat
//
// This should trigger the DETECTARRAY error like t_detectarray_1.v, but in
// fact it casuses a broken link error. The only difference is that the struct
// is defined using a constant rather than a localparam.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett.
// SPDX-License-Identifier: CC0-1.0

localparam ID_MSB = 1;


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef struct packed {
      logic [1:0] 	id;
   } context_t;

   context_t  tsb;

   assign tsb.id = {tsb.id[0], clk};

   initial begin
      tsb.id = 0;
   end

   always @(posedge clk or negedge clk) begin

`ifdef TEST_VERBOSE
      $write("tsb.id = %x\n", tsb.id);
`endif

      if (tsb.id[1] != 0) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule
