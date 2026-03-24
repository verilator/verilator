// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(
    input clk
);
  int cyc;

  sub #(10) arr[2](.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    // Test $dumpvars with an out-of-range array index via cpptop.
    $dumpvars(1, cpptop.t.arr[999].deep);
  end
endmodule

module sub #(
    parameter int ADD
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;

  deep #(ADD + 1) deep(.*);
endmodule

module deep #(
    parameter int ADD
)(
    input int cyc
);
  int inner;
  always_comb inner = cyc + ADD;
endmodule
