// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Pure aliases whose declared range / net-ness differ from their canonical's
// storage (retargeted). The VPI row must report the ALIAS's own metadata.
module t (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  in_a,
  input  logic [7:0]  in_b,
  output logic [7:0]  o
);

  // Sequential canonicals (boundaries, both declared [7:0], reg).
  logic [7:0] src_a;
  logic [7:0] src_b;

  always_ff @(posedge clk) begin
    if (rst) begin
      src_a <= 8'h0;
      src_b <= 8'h0;
    end else begin
      src_a <= in_a;
      src_b <= in_b;
    end
  end

  // Alias with a different declared packed range than its canonical [7:0].
  logic [8:1] a_wide;  assign a_wide = src_a;

  // Net alias of a reg canonical (net-vs-var metadata differs).
  wire  [7:0] a_net;   assign a_net = src_b;

  assign o = a_wide ^ a_net;

endmodule
