// DESCRIPTION: Verilator: FSM coverage ignores a register written as a concatenation
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  logic [1:0] hi;
  logic [1:0] lo;
  logic [3:0] next;
  logic rst;
  int cyc;

  assign next = {hi, lo} + 4'd1;

  always_ff @(posedge clk) {hi, lo} <= rst ? 4'd0 : next;

  initial cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    rst <= (cyc == 0);
    if (cyc == 5) begin
      if ({hi, lo} != 4'd3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
