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

   enum  {
          CASE_0 = 0,
          CASE_1 = 1,
          CASE_2 = 2,
          CASE_4 = 4,
          CASE_5 = 5,
          DEFAULT = 99
          } e;

   reg [2:0] cyc;

   initial cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   always @* begin
      case (cyc)
        3'b000: e = CASE_0;
        3'b001: e = CASE_1;
        3'b010: e = CASE_2;
        3'b100: e = CASE_4;
        3'b101: e = CASE_5;
        default: e = DEFAULT;
      endcase
   end

   always @(posedge clk) begin
      $display("cyle %d = %d", cyc, e);
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
