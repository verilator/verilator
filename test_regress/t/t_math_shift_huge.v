// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Outputs
   outl, outr,
   // Inputs
   lhs
   );
   input [95:0] lhs;
   output [95:0] outl;
   output [95:0] outr;

   assign outl = lhs << 95'hffff_00000000;
   assign outr = lhs >> 95'hffff_00000000;

endmodule
