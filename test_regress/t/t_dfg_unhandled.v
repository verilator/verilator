// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t (
          input wire          clk,
          output wire [31:0]  o0
          );

   int file;

   assign o0 = $fgetc(file); // Impure

endmodule
