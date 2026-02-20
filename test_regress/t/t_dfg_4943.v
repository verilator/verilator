// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top(input wire i, output wire o);

  // Partially driven, and drives other var with non-DFG refs
  wire logic [1:0] x;

  assign x[0] = i;

  assign o = |x;

  wire logic [1:0] alt = x;

  always @(alt) $display(alt);

endmodule
