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
  logic [6:0] a = 7'h01;
  logic [6:0] b = 7'h5d;

  wire [6:0] cycle_q;
  cyclic_leaf cycle (
      a,
      cycle_q
  );
  task check_cycle;
    `checkh(cycle_q, a);
  endtask

  wire [48:0] shared_q;
  shared_leaf one_sink (
      a,
      b,
      shared_q
  );
  task check_shared;
    for (int j = 0; j < 7; ++j) `checkh(shared_q[j*7+:7], (a & b) & 7'h0f);
  endtask

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
  task check_retained;
    for (int j = 0; j < 7; ++j) begin
      `checkh(retained_q[j*7+:7], (a ^ b) & 7'h0f);
      `checkh(retained_r[j*7+:7], (a ^ b) ^ 7'h55);
    end
    `checkh(observed_q, a ^ b);
  endtask

  initial begin
    for (int i = 0; i < 256; ++i) begin
      #1;
      check_cycle();
      check_shared();
      check_retained();
      a = a + 7'h01;
      b = b + 7'h13;
    end
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
