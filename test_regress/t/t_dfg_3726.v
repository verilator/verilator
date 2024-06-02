// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   x,
   // Inputs
   i
   );

   input i;
   output x;

   assign x = (i ? 0 : 1) && 1;

endmodule
