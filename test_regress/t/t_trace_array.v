// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   integer      cyc = 0;

   // Trace would overflow at 256KB which is 256 kb dump, 16 kb in a chunk

   typedef struct packed {
      logic [128*1024:0] d;
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
