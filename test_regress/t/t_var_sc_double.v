// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 George Polack
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
