// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Stream-to-packed: RESTRUCTSEL/ARRAYSEL reconstruction.
module t (
  input logic       clk,
  input logic [7:0] in0,
  input logic [7:0] in1,
  input logic [7:0] in2,
  input logic [7:0] in3,
  output logic [7:0] o
);

  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
    logic [7:0] c;
  } us_t;

  us_t        s;
  logic [7:0] arr [0:3];

  always_ff @(posedge clk) begin
    s.a    <= in0;
    s.b    <= in1;
    s.c    <= in2;
    arr[0] <= in0;
    arr[1] <= in1;
    arr[2] <= in2;
    arr[3] <= in3;
  end

  // Stream-to-packed: reconstructed for VPI.
  logic [23:0] flat_gg;    // {>>{s}}: order preserved
  logic [23:0] flat_ll;    // {<<{s}}: bit-reversed
  logic [23:0] flat_lb;    // {<<byte{s}}: byte-reversed
  logic [31:0] flat_arr_gg; // {>>{arr}}: array streamed

  assign flat_gg     = {>>{s}};
  assign flat_ll     = {<<{s}};
  assign flat_lb     = {<<byte{s}};
  assign flat_arr_gg = {>>{arr}};

  assign o = s.a ^ s.b ^ s.c ^ arr[3];

endmodule
