// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Reconstruction + alias + register; verify --vpi-lazy + --trace.
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

  // A reconstructed net: its shadow is a module temp, so the row's net-ness is carried over
  wire [6:0] cmb_net;
  assign cmb_net = cmb ^ 7'h55;

  // An alias of a reconstructed canonical shares its descriptor, so the netlist dump has a
  // vpi-lazy-alias entry
  wire [6:0] cmb_ali;
  assign cmb_ali = cmb;

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 7'h0;
      result <= 7'h0;
    end else begin
      keep <= keep + 7'h3;
      result <= cmb;
    end
  end

  assign obs = result ^ alias1 ^ cmb_net ^ cmb_ali;

endmodule
