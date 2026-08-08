// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Alias submodule (Phase 2: retargeted to canonical storage).
module sub (
  input  logic [6:0] port_in,
  output logic [6:0] port_out
);
  assign port_out = port_in;
endmodule

module t #(
  parameter int INTF_QTY = 3
) (
  input logic clk,
  input logic rst,
  output logic [6:0] observe
);

  logic [6:0] keep;
  logic [6:0] result;
  logic [6:0] dead;

  // Comb chain eliminated then reconstructed.
  logic [6:0] cmb1;
  logic [6:0] cmb2;
  logic [6:0] cmb3;
  assign cmb1 = keep + 7'h7;
  assign cmb2 = cmb1 ^ 7'h2a;
  assign cmb3 = cmb2 + 7'h5;

  // Phase 2 aliases.
  logic [6:0] alias1;
  logic [6:0] alias2;
  logic [6:0] sub_out;
  assign alias1 = keep;
  assign alias2 = alias1;
  sub u_sub (.port_in(keep), .port_out(sub_out));

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      result <= 7'h0;
      dead <= 7'h0;
      observe <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      result <= cmb3;
      dead <= keep + 7'h9;
      observe <= result ^ alias2 ^ sub_out;
    end
  end

endmodule
