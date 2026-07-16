// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Property-case branches of different lengths fail on the same tick

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  int failures = 0;
  logic [1:0] selector;

  always_comb begin
    if (cyc == 2) selector = 0;
    else if (cyc == 3) selector = 1;
    else selector = 2;
  end

  assert property (@(posedge clk) case (selector) 0: 1'b1 ##2 1'b0; 1: 1'b1 ##1 1'b0; default: 1'b1;
  endcase)
  else failures++;

  always @(posedge clk) cyc <= cyc + 1;

  always @(negedge clk) begin
    if (cyc == 7) begin
      `checkd(failures, 2);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
