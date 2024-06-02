// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module v(input logic t);
endmodule

module top(input logic [2:0] c);
  v v1((int'(c) + int'($countones(c))) > 2);
endmodule
