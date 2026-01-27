// DESCRIPTION: Verilator: Simple test of unoptflat
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

localparam ID_MSB = 1;


module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef struct packed {
      logic [ID_MSB:0]  id;
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
