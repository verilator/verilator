// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Shapes a --vpi-lazy cone rebuild could take a deposit back from: a dependent cone, the rows
// either side of a deposited one inside a single cone, and one row per vpi_put_value store
// path that used to reach storage without claiming the row. IEEE 1800-2023 38.34 wants the
// deposit to stand and what resolves from it to re-resolve, so a rebuild must skip exactly one
// row: the row above the deposited one still has to follow the model.
module t (
  input logic clk,
  input logic rst,
  output logic [7:0] observe
);

  // The one boundary flop: real storage, so a deposit into it is what moves the epoch here
  logic [7:0] keep;

  // One always_comb each, so three cones, and dep_mid's body calls dep_src's reconstruction
  logic [7:0] dep_src;
  always_comb dep_src = keep ^ 8'h11;

  logic [7:0] dep_mid;
  always_comb dep_mid = dep_src + 8'h3;

  logic [7:0] dep_top;
  always_comb dep_top = dep_mid ^ 8'h2c;

  // One cone, three rows: a group holds rows a cone feeds on to, so the sibling of a
  // deposited row is the row above it in the chain
  logic [7:0] pair_a;
  logic [7:0] pair_b;
  logic [7:0] pair_c;
  always_comb begin
    pair_a = keep + 8'h6;
    pair_b = pair_a ^ 8'h1;
    pair_c = pair_b + 8'h1f;
  end

  // vpiBinStrVal target, and a cone that resolves from it
  logic [7:0] bin_row;
  always_comb bin_row = keep ^ 8'h5a;

  logic [7:0] bin_dep;
  always_comb bin_dep = bin_row + 8'h7;

  // vpiRealVal target: VLVT_REAL reconstructs as a basic dtype, and has its own store path
  real r_row;
  always_comb r_row = real'(keep) * 2.0;

  real r_dep;
  always_comb r_dep = r_row + 1.0;

  // vpi_put_value_array target: one continuous assign per element, so the whole array is a
  // single reconstructed row carrying one deposit word
  logic [7:0] arr [0:3];
  for (genvar i = 0; i < 4; ++i) begin : ga
    assign arr[i] = keep ^ (8'h11 * 8'(i));
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      keep <= 8'h0;
      observe <= 8'h0;
    end else begin
      keep <= keep + 8'h3;
      observe <= dep_src ^ dep_mid ^ dep_top ^ pair_a ^ pair_b ^ pair_c
                 ^ bin_row ^ bin_dep ^ arr[0] ^ arr[1] ^ arr[2] ^ arr[3]
                 ^ 8'(int'(r_dep));
    end
  end

endmodule
