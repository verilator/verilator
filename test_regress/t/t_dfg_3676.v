// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off UNOPTFLAT

module t(
  input  wire [3:0]      i,
  output wire [2:0][3:0] o
);

   wire [2:0][3:0] v;

   // This circular logic used to trip up DFG decomposition

   assign v[0]    = i;
   assign v[1][0] = v[0][1] | v[0][0];

   assign o[1][2] = v[0][2];
   assign o[2][1:0] = {v[1][0] , o[1][0]};

endmodule
