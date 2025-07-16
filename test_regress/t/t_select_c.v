// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // verilator lint_off WIDTH
   // verilator lint_off IMPLICIT
   wire [22:0] w274;
   wire w412;
   wire w413;
   wire w509;

   assign w104 = ! w509;
   assign w201 = w258 > 12'hab7;
   assign w204 = 7'h7f <= w104;
   wire [11:0] w258 = 3'h3 || w274;
   assign w538 = w412 ? out21 : w201;
   wire [16:0] w539 = w413 ? w538 : 17'h00570;
   wire [21:5] out21 = w204;
   assign out51 = w539[0];

   initial begin
      $display("%0d", out51);
   end
endmodule
