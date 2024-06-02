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

   string s;
   reg [2:0] cyc;

   initial cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: s = "case-0";
        3'b001: s = "case-1";
        3'b010: s = "case-2";
        3'b100: s = "case-4";
        3'b101: s = "case-5";
        default: s = "default";
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = %s", cyc, s);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
