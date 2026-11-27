// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Dotted clocking event without parentheses (IEEE 1800-2023 A.6.5)
module t;
  typedef struct packed {logic clk;} clk_t;
  clk_t sc = 0;
  always #5 sc.clk = ~sc.clk;
  logic a = 0;
  int fails_paren = 0;
  int fails_hier = 0;

  ap_paren :
  assert property (@(sc.clk) a |-> !a)
  else fails_paren = fails_paren + 1;
  ap_hier :
  assert property (@sc.clk a |-> !a)
  else fails_hier = fails_hier + 1;

  initial begin
    #5 a = 1;
    #10 a = 0;
    #10 $finish;
  end

  final begin
    `checkd(fails_paren, fails_hier);
    `checkd(fails_hier > 0, 1);
    $write("*-* All Finished *-*\n");
  end
endmodule
