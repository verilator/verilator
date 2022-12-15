// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t ();

   initial begin
      forever begin end
      // verilator lint_off UNSIGNED
      for (reg [31:0] i=0; i>=0; i=i+1) begin end
   end
endmodule
