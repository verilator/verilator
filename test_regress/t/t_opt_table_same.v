// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int   i;
   int   j;

   reg [2:0] cyc;

   initial cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: i = 0;
        3'b001: i = 1;
        3'b010: i = 2;
        3'b100: i = 4;
        3'b101: i = 5;
        default: i = 99;
      endcase
   end

   // Equivalent to above
   always @* begin
      case (cyc)
        3'b101: j = 5;
        3'b100: j = 4;
        3'b010: j = 2;
        3'b001: j = 1;
        3'b000: j = 0;
        default: j = 99;
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = %d %d", cyc, i, j);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
