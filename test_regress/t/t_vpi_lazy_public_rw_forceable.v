// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// retainableKind() excludes forceable signals from the lazy reconstruction
// pass, so a comb signal that is also forceable must stay eagerly retained
// (its own pre-existing force/VPI mechanism), never reconstructed.
module t (
  input logic clk,
  input logic rst,
  output logic [6:0] observe
);

  logic [6:0] keep;
  logic [6:0] frc  /* verilator forceable */;

  assign frc = keep + 7'h11;

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      observe <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      observe <= frc;
    end
  end

endmodule
