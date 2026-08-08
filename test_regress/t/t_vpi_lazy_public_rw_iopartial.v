// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Regression guard for bb0f48a0f: foldContinuousPartials used to assert that
// every Tier-B partial-write target is reconstructable, but an IO port
// assembled from continuous bit-slice writes never is.
module t (
  input logic clk,
  input logic rst,
  output logic [7:0] out
);

  logic [7:0] keep;

  assign out[3:0] = keep[3:0];
  assign out[7:4] = keep[7:4] ^ 4'hf;

  always_ff @(posedge clk) begin
    if (rst) keep <= 8'h0;
    else keep <= keep + 8'h11;
  end

endmodule
