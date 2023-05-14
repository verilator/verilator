// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug1364

module t (/*AUTOARG*/
   // Inputs
   clk, res
   );
   input clk;
   input res;

   int   arr[3];
   initial begin
      arr = '{default: '0,
              1: '0,
              1: '1};  // Bad
      arr = '{'0, '1, '0, '1};  // Bad, too many
      arr = '{'0, '1};  // Bad, too few
   end

endmodule
