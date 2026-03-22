// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Marco Bartoli.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(
    input clk
);
  int cyc;
  int counter;

  sub #(10) sub_a(.*);
  sub #(20) sub_b(.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    counter <= counter + 2;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    // Test $dumpvars with specific wire names
    $dumpvars(0, cyc, counter);
  end
endmodule

module sub #(
    parameter int ADD
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;
endmodule
