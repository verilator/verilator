// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t(
  input clk
);

  int cyc = 1;

  Factorial factorial(
    .clk(clk),
    .i(cyc)
  );

  initial begin
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars;
  end

  always @(posedge clk) begin
    cyc <= cyc+1;
    if (cyc == 5) begin
      $finish;
    end
  end
endmodule

module Factorial(
  input clk,
  input int i
);
  int fact = 1;
  always @(posedge clk) begin
    fact <= fact * i;
  end
endmodule
