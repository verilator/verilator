// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%p exp='h%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  bit clk, disabled;
  always #1 clk = !clk;
  bit ready = 1;
  int passes;
  int readyPasses;
  bit a = 1;

  assert property (@(posedge clk) disable iff (disabled) eventually[0: 2] a);
  always @(posedge clk) assert property (disable iff (disabled) eventually[0: 2] a);
  assert property (@(posedge clk) disable iff (disabled) eventually[0: 2] (a ##1 a));
  assert property (@(posedge clk) disable iff (disabled) s_eventually (a ##1 a));
  assert property (@(posedge clk) disable iff (disabled) s_eventually[2: 2] a);
  assert property (@(posedge clk) disable iff (disabled) s_eventually[1: $] a);
  assert property (@(posedge clk) disable iff (disabled)
                   (eventually[0: 1] a) implies (eventually[0: 1] a));

  assert property (@(posedge clk) disable iff (disabled) s_eventually (eventually[0:0] 1'b1))
    ++passes;
    else $display("Unexpected nested eventual failure");
  assert property (@(posedge clk) disable iff (disabled) (ready intersect ready) |-> s_eventually[0:1] ready)
    else $fatal;
  assert property (@(posedge clk) disable iff (disabled) s_eventually (eventually[0:0] ready))
    ++readyPasses;
    else $fatal;

  int repeatFails;
  // The one-cycle repetition matches on the first edge; its consequent is false.
  assert property (@(posedge clk) disable iff (disabled) a[*1:2] |-> not eventually[0:0] 1'b1)
    else ++repeatFails;

  initial begin
    disabled = 0;
    @(negedge clk);
    disabled = 1;
    repeat (2) @(negedge clk);
    `checkh(repeatFails, 1);
    `checkh(readyPasses, 1);
    `checkh(passes, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
