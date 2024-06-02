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

   reg [2:0] cyc;

   initial  cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: i = 0;
        3'b001: i = -1;
        3'b010: i = 2;
        3'b100: i = -4;
        3'b101: i = 5;
        default: i = -1 << 31;
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = %d", cyc, i);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
