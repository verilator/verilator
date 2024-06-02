// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [31:0] arr [0:7];
   assign arr[0:7] = {
                      {16'hffff, 16'h0000},
                      {16'h0000, 16'h0000},
                      {16'h0a0a, 16'h0000},
                      {16'ha0a0, 16'h0000},
                      {16'hffff, 16'h0000},
                      {16'h0000, 16'h0000},
                      {16'h0a0a, 16'h0000},
                      {16'ha0a0, 16'h0000}
                      };

   int cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 9) begin
         if (arr[0] !== 32'hffff0000) $stop;
         if (arr[7] !== 32'ha0a00000) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
