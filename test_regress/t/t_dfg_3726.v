// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
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
