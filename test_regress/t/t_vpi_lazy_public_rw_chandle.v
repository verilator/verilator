// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Chandle write-only signal (opaque, not reconstructable).
module t (
  input logic clk,
  input logic rst,
  output logic [6:0] obs
);

  logic [6:0] cnt;
  chandle handle;

  always_ff @(posedge clk) begin
    if (rst) begin
      cnt <= 7'h0;
      handle <= null;
    end else begin
      cnt <= cnt + 7'h1;
    end
  end

  assign obs = cnt;

endmodule
