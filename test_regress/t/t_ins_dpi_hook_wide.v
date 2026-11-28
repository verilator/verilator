// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets wider than 32 bits
module top_module;
  logic         clk = 0;
  logic [127:0] a = 128'h2;
  logic [127:0] q, q2;
  logic [47:0]  q48;
  longint       q64;
  int           cyc = 0;

  sub s0 (.a(a), .cyc(cyc), .q(q), .q2(q2), .q48(q48), .q64(q64));

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| q: %h q2: %h]", cyc, q, q2);
    $display("$[%0d| q48: %012x q64: %016x]", cyc, q48, q64);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

module sub (
  input  logic [127:0] a,
  input  int           cyc,
  output logic [127:0] q,
  output logic [127:0] q2,
  output logic [47:0]  q48,
  output longint       q64
);
  logic [127:0] v;
  logic [127:0] v2;
  logic [47:0]  v48;
  longint       v64;
  always_comb v = a;
  always_comb v2 = ~a;
  assign v48 = 48'h1234_0000_0000 + 48'(cyc);
  assign v64 = 64'h0123_4567_0000_0000 + 64'(cyc);
  assign q = v;
  assign q2 = v2;
  assign q48 = v48;
  assign q64 = v64;
endmodule
