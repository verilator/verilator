// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   int x;
   int y;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         x <= 1;
      end
      else if (cyc == 1) begin
         y <= (x = 2);
      end else begin
         if (x != 2) $stop;
         if (y != 2) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
