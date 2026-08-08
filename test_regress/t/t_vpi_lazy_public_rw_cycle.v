// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Combinational cycles and cyclic aliases: retained (not reconstructed).
module t (
  input logic clk
);

  logic [6:0] boundary;

  // 'd' reconstructed, feeds cycle.
  logic [6:0] d;
  assign d = boundary + 7'h1;

  // Cycle: cyc_a and cyc_b retained.
  logic [6:0] cyc_a;
  logic [6:0] cyc_b;
  assign cyc_a = cyc_b ^ d;
  assign cyc_b = cyc_a ^ d;

  // Downstream reconstructed.
  logic [6:0] cyc_down;
  logic [6:0] cyc_down2;
  assign cyc_down  = cyc_a ^ cyc_b;
  assign cyc_down2 = cyc_down + boundary;

  // Cyclic aliases retained.
  logic [6:0] ali_a;
  logic [6:0] ali_b;
  assign ali_a = ali_b;
  assign ali_b = ali_a;

  logic [6:0] self_loop;
  assign self_loop = self_loop & boundary;

  always_ff @(posedge clk) boundary <= boundary + 7'h1;

endmodule
