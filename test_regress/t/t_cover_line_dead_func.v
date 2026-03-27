// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   integer cyc;
   initial cyc = 0;

   function int used_func(int x);
      if (x > 0) return x + 1;
      else return x - 1;
   endfunction

   function int unused_func(int x);
      if (x > 0) return x * 2;
      else return x * 3;
   endfunction

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         if (used_func(cyc) != 2) $stop;
      end
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
