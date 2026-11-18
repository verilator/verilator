// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  wire a = cyc % 10 == 1;
  wire c = cyc % 10 == 4;

  // Test: each attempt passes once, vacuous attempts included
  int pass_bare = 0;
  int pass_nonoverlap = 0;
  int pass_seq_ant = 0;
  assert property (@(posedge clk) s_eventually c) ++pass_bare;
  assert property (@(posedge clk) a |=> s_eventually c) ++pass_nonoverlap;
  assert property (@(posedge clk) a ##1 cyc % 10 == 2 |-> s_eventually c) ++pass_seq_ant;

  always @(posedge clk) ++cyc;

  always @(negedge clk) begin
    if (cyc == 95) begin
      `checkd(pass_bare, 95);
      `checkd(pass_nonoverlap, 95);
      `checkd(pass_seq_ant, 95);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
