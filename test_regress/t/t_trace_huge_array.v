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
   int cyc = 0;

   localparam max = 1000;
   logic [31:0] foo [max:0];
   logic [max:0] [15:0] [31:0] bar;

   always_ff @(posedge clk) begin
      cyc <= cyc + 1;
      foo[0] <= cyc;
      for (int i = 1; i <= max; i++) foo[i] <= foo[i-1];
      bar <= (bar << 32) | type(bar)'(cyc);
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
