// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   o,
   // Inputs
   i
   );

   input i;
   output o;
   sub sub(i, o);
endmodule

module sub(input i, output o);
   assign o = (i===1'bz) ? 1'b0 : i;
endmodule
