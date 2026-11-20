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
  int done = 0;  // Number of cases that have finished

  logic [6:0] cycle_a = 7'h01;
  wire [6:0] cycle_q;
  cyclic_leaf cycle (
      cycle_a,
      cycle_q
  );
  initial begin
    for (int i = 0; i < 256; ++i) begin
      #1;
      `checkh(cycle_q, cycle_a);
      cycle_a = cycle_a + 7'h01;
    end
    ++done;
  end

  logic [6:0] shared_a = 7'h01;
  logic [6:0] shared_b = 7'h5d;
  wire [48:0] shared_q;
  shared_leaf one_sink (
      shared_a,
      shared_b,
      shared_q
  );
  initial begin
    for (int i = 0; i < 256; ++i) begin
      #1;
      for (int j = 0; j < 7; ++j) `checkh(shared_q[j*7+:7], (shared_a & shared_b) & 7'h0f);
      shared_a = shared_a + 7'h01;
      shared_b = shared_b + 7'h13;
    end
    ++done;
  end

  logic [6:0] retained_a = 7'h01;
  logic [6:0] retained_b = 7'h5d;
  wire [48:0] retained_q;
  wire [48:0] retained_r;
  wire [6:0] observed_q;
  retained_leaf two_sinks (
      retained_a,
      retained_b,
      retained_q,
      retained_r,
      observed_q
  );
  initial begin
    for (int i = 0; i < 256; ++i) begin
      #1;
      for (int j = 0; j < 7; ++j) begin
        `checkh(retained_q[j*7+:7], (retained_a ^ retained_b) & 7'h0f);
        `checkh(retained_r[j*7+:7], (retained_a ^ retained_b) ^ 7'h55);
      end
      `checkh(observed_q, retained_a ^ retained_b);
      retained_a = retained_a + 7'h01;
      retained_b = retained_b + 7'h13;
    end
    ++done;
  end

  initial begin
    wait (done == 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module shared_leaf (
    input [6:0] a,
    input [6:0] b,
    output [48:0] q
);
  for (genvar i = 0; i < 7; ++i) begin : g
    wire [6:0] d = a & b;
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
  assign observed = a ^ b;
  for (genvar i = 0; i < 7; ++i) begin : g
    wire [6:0] d = a ^ b;
    assign q[i*7+:7] = d & 7'h0f;
    assign r[i*7+:7] = d ^ 7'h55;
  end
endmodule

module cyclic_leaf (
    input [6:0] a,
    output wire [6:0] q
);
  wire [6:0] shared = a & 7'h55;
  wire [6:0] opposite = ~shared;
  assign q = (q & (shared & opposite)) ^ a;
endmodule
