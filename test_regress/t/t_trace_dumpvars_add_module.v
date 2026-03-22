// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Marco Bartoli.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(
);
  logic clk;
  int cyc;

  sub #(10) sub_a(.*);
  sub #(20) sub_b(.*);

  initial begin
    clk = 0;
    forever #1 clk = !clk;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 1) begin
      $dumpfile({`STRINGIFY(`TEST_OBJ_DIR), "/simx1.vcd"});
      $dumpvars(0, sub_b);
    end
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    $dumpfile({`STRINGIFY(`TEST_OBJ_DIR), "/simx0.vcd"});
    $dumpvars(1, sub_a);
  end
endmodule

module sub #(
    parameter int ADD
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;

  deep #(ADD + 1) deep_i(.*);
endmodule

module deep #(
    parameter int ADD
)(
    input int cyc
);
  int inner;
  always_comb inner = cyc + ADD;
endmodule
