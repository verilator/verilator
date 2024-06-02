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

   reg [3:0] a, b;

   Test1 t1(clk, a, b);

   initial begin
      a = 0;
      b = 0;
   end

   always @(posedge clk) begin
      a <= a + 1;
      b = b + 1;

      if (b >= 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module Test1(
   clk, a, b
   );

   input clk;
   input [3:0] a, b;

   always @(posedge clk) begin
      if (a < 9) $strobe("%0d == %0d, %0d == %0d", a, b, $past(a), $past(b));
   end

endmodule
