// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc;

   Test1 t1(clk);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      if (cyc >= 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module Test1(
   clk
   );

   input clk;
   reg [3:0] a = 0;

   assert property (@(posedge clk) a++ >= 0);
endmodule
