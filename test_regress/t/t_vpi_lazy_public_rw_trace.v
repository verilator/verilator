// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Reconstruction + alias + register; verify --vpi-lazy-public-rw + --trace.
module t (
  input logic clk,
  input logic rst,
  output logic [6:0] obs
);

  logic [6:0] keep;
  logic [6:0] result;

  // Reconstructed cmb; alias1 aliases keep.
  logic [6:0] cmb;
  assign cmb = keep + 7'h1;

  logic [6:0] alias1;
  assign alias1 = keep;

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      result <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      result <= cmb;
    end
  end

  assign obs = result ^ alias1;

endmodule
