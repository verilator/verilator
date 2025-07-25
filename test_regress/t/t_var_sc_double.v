// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by George Polack.
// SPDX-License-Identifier: CC0-1.0

module t (
   // Outputs
   o_z,
   // Inputs
   i_a
   );
   input real  i_a;
   output real o_z;

   assign o_z = i_a;
endmodule
