// DESCRIPTION: Verilator: RepCut equivalent activation groups
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(
  parameter int SHARED_ROUNDS = 0,
  parameter bit OBSERVE_DPI = 0
) (
  input bit clk, other_clk, reset_n, gate,
  input logic [14:0] x,
  output logic [14:0] q [0:14]
);
  wire [14:0] shared_input = ((q[0] + x) ^ (q[7] >> 1)) + (x * 15'h39);
  for (genvar i = 0; i < SHARED_ROUNDS; ++i) begin : shared_work
    wire [14:0] previous;
    if (i == 0) assign previous = shared_input;
    else assign previous = shared_work[i-1].value;
    wire [14:0] value = ((previous * 15'h39) ^ (previous >> 3)) + q[i % 8];
  end
  wire [14:0] mix;
  if (SHARED_ROUNDS == 0) assign mix = shared_input;
  else assign mix = shared_work[SHARED_ROUNDS-1].value;
  if (OBSERVE_DPI) begin : observers
    import "DPI-C" function void repcut_domains_observe(input int unsigned domain_id,
                                                        input int unsigned value);
    // Both observers must see pre-publication state, including when reset and
    // clock edges coincide. Their independent host records avoid ordering ties.
    always @(posedge clk) repcut_domains_observe(0, 32'(q[0] ^ mix));
    always @(posedge clk or negedge reset_n) repcut_domains_observe(1, 32'(q[7] + mix));
  end
  for (genvar i = 0; i < 8; ++i) begin : copies
    repcut_domain_leaf #(.ID(i)) leaf(clk, reset_n, mix, q[i]);
  end
  for (genvar i = 8; i < 11; ++i) begin : async_copies
    repcut_domain_leaf #(.ID(i), .ASYNC(1)) leaf(clk, reset_n, mix, q[i]);
  end
  logic [14:0] falling;
  // The cheap producer also feeds a domain that does not use the larger cone.
  // Sharing the larger cone must retain its producer's wider domain union.
  always @(negedge clk) falling <= q[0] ^ shared_input;
  assign q[11] = falling;
  repcut_domain_leaf #(.ID(12)) independent(other_clk, reset_n, mix, q[12]);
  wire gated_clk = clk & gate;
  repcut_domain_leaf #(.ID(13)) gated(gated_clk, reset_n, mix, q[13]);
  bit divided_clk;
  always @(posedge clk) divided_clk <= reset_n && !divided_clk;
  repcut_domain_leaf #(.ID(14)) divided(divided_clk, reset_n, mix, q[14]);
endmodule

module repcut_domain_leaf #(
  parameter int ID = 0,
  parameter bit ASYNC = 0
) (
  input bit clk, reset_n,
  input logic [14:0] x,
  output logic [14:0] q
);
  wire clock_alias = clk;
  wire reset_alias = reset_n;
  wire [14:0] value = ((x + q) ^ (q << 3)) + 15'(ID + 1);
  if (ASYNC) begin
    always @(posedge clock_alias or negedge reset_alias) begin
      if (!reset_n) q <= 0;
      else if (x[ID]) q <= value;
      else q <= value ^ (q >> 2);
    end
  end else begin
    always @(posedge clock_alias) begin
      if (!reset_n) q <= 0;
      else if (x[ID]) q <= value;
      else q <= value ^ (q >> 2);
    end
  end
endmodule
