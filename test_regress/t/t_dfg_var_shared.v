// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got='h%0x exp='h%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  timeunit 1ns; timeprecision 1ps;
  localparam realtime STEP = 1ns;
  typedef logic [9:3] word_t;
  word_t a;
  word_t b;
  wire [6:0] cycle_q;

  cyclic_leaf cycle (
      a,
      cycle_q
  );

  wire [48:0] shared_q;
  shared_leaf one_sink (
      a,
      b,
      shared_q
  );
  wire [48:0] retained_q;
  wire [48:0] retained_r;
  wire [6:0] observed_q;
  retained_leaf two_sinks (
      a,
      b,
      retained_q,
      retained_r,
      observed_q
  );

  wire [20:0] middle_q;
  middle_leaf middle_case (
      a,
      b,
      middle_q
  );

  initial begin
    a = 7'h01;
    b = 7'h5d;
    for (int i = 0; i < 256; ++i) begin
      #STEP;
      for (int j = 0; j < 7; ++j) begin
        `checkh(shared_q[j*7+:7], (a & b) & 7'h0f);
        `checkh(retained_q[j*7+:7], (a ^ b) & 7'h0f);
        `checkh(retained_r[j*7+:7], (a ^ b) ^ 7'h55);
      end
      `checkh(observed_q, a ^ b);
      `checkh(cycle_q, a);
      for (int j = 0; j < 3; ++j) begin
        `checkh(middle_q[j*7+:7], (a ^ b) & 7'h0f);
      end
      a = a + 7'h01;
      b = {b[8:3], b[9] ^ b[8]};
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module shared_leaf (
    input [9:3] a,
    input [9:3] b,
    output [48:0] q
);
  timeunit 1ns; timeprecision 1ps;
  wire [9:3] s = a & b;
  for (genvar i = 0; i < 7; ++i) begin : g
    wire [9:3] d = s;
    assign q[i*7+:7] = d & 7'h0f;
  end
endmodule

module retained_leaf (
    input [6:0] a,
    input [6:0] b,
    output [48:0] q,
    output [48:0] r,
    output [6:0] observed
);
  timeunit 1ns; timeprecision 1ps;
  wire [6:0] s = a ^ b;
  assign observed = s;
  for (genvar i = 0; i < 7; ++i) begin : g
    wire [6:0] d = s;
    assign q[i*7+:7] = d & 7'h0f;
    assign r[i*7+:7] = d ^ 7'h55;
  end
endmodule

module cyclic_leaf (
    input [6:0] a,
    output wire [6:0] q
);
  timeunit 1ns; timeprecision 1ps;
  wire [6:0] shared = a & 7'h55;
  wire [6:0] opposite = ~shared;
  assign q = (q & (shared & opposite)) ^ a;
endmodule

module middle_leaf (
    input [6:0] a,
    input [6:0] b,
    output [20:0] q
);
  timeunit 1ns; timeprecision 1ps;
  wire [6:0] shared = a & 7'h55;
  wire [6:0] opposite = ~shared;
  wire [6:0] zero = shared & opposite;
  wire [6:0] x = (a ^ b) | zero;
  wire [6:0] first = x;
  wire [6:0] middle = first;
  wire [6:0] last = x;
  assign q = {(last & 7'h0f), (middle & 7'h0f), (first & 7'h0f)};
endmodule
