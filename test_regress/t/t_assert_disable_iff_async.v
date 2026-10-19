// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A disable condition pulsing between clock ticks aborts pending attempts,
// and its value is not sampled (IEEE 1800-2023 16.12).
module t;
  bit clk, reset, glitch;
  bit [6:0] mode;
  int fail[5];
  time fail_time[5];
  bit clk2, reset2;
  int fail2;
  bit start, a, hi = 1, reset3, hold;
  int fail3[3];
  time fail3_time[3];
  int cover3[4];
  time cover3_time;

  always #5 clk = !clk;

  assert property (@(posedge clk) disable iff (reset) ##2 0)
  else begin
    fail[0]++;
    fail_time[0] = $time;
  end
  assert property (@(posedge clk) disable iff (reset) 1 |-> ##2 0)
  else begin
    fail[1]++;
    fail_time[1] = $time;
  end
  assert property (@(posedge clk) disable iff (reset) 1 |=> ##1 0)
  else begin
    fail[2]++;
    fail_time[2] = $time;
  end
  assert property (@(posedge clk) disable iff (glitch) ##2 0)
  else begin
    fail[3]++;
    fail_time[3] = $time;
  end
  // Another process drops the disable in the same time step it rises.
  always @(posedge glitch) glitch = 0;
  // A vector disable is true when any bit is set, not only bit 0.
  assert property (@(posedge clk) disable iff (|mode) ##2 0)
  else begin
    fail[4]++;
    fail_time[4] = $time;
  end
  assert property (@(posedge clk2) disable iff (reset2) 0 ##1 1)
  else fail2++;

  assert property (@(posedge clk) disable iff (reset3) start |-> ##[1:3] 0)
  else begin
    fail3[0]++;
    fail3_time[0] = $time;
  end
  assert property (@(posedge clk) disable iff (reset3) start |-> (hi throughout (##3 0)))
  else begin
    fail3[1]++;
    fail3_time[1] = $time;
  end
  // A $sampled disable is only checked at clock ticks, so hold it across one.
  assert property (@(posedge clk) disable iff ($sampled(hold)) start |-> ##3 0)
  else begin
    fail3[2]++;
    fail3_time[2] = $time;
  end
  cover property (@(posedge clk) disable iff (reset3) start ##3 1) begin
    cover3[0]++;
    cover3_time = $time;
  end
  // The second attempt's left-hand side fails, so it must not complete using
  // the left-hand match latched by the aborted first attempt.
  cover property (@(posedge clk) disable iff (reset3) start ##0 ((##1 a) and(##3 1))) cover3[1]++;
  cover property (@(posedge clk) disable iff (reset3) start ##0 ((##1 a ##2 1) intersect (##3 1)))
    cover3[2]++;
  cover property (@(posedge clk) disable iff ($sampled(hold)) start ##0 ((##1 a) and(##3 1)))
    cover3[3]++;

  initial begin
    // Pulse the disables between two assertion clock ticks, while the attempt
    // started at the first tick is still pending.
    @(negedge clk);
    reset = 1;
    glitch = 1;
    mode = 7'h40;
    #1;
    reset = 0;
    mode = 0;
    // The aborted attempt would have failed at the third tick.
    @(negedge clk);
    @(negedge clk);
    for (int i = 0; i < 5; ++i) `checkd(fail[i], 0);
    // The attempt started at the second tick fails at the fourth tick.
    @(negedge clk);
    for (int i = 0; i < 5; ++i) begin
      `checkd(fail[i], 1);
      `checkd(fail_time[i], 35);
    end
    clk2 = 1;
    #1;
    `checkd(fail2, 1);
    clk2 = 0;
    // The disable rises in the same time step as the clock edge.
    #1;
    reset2 = 1;
    clk2 = 1;
    #1;
    `checkd(fail2, 1);
    // Start one attempt, then abort it after the left-hand sides of the
    // and/intersect covers have matched.
    @(negedge clk);
    start = 1;
    @(negedge clk);
    start = 0;
    a = 1;
    @(negedge clk);
    a = 0;
    hold = 1;
    reset3 = 1;
    #1;
    reset3 = 0;
    @(negedge clk);
    hold = 0;
    // The aborted attempt would have completed at its fourth tick.
    @(negedge clk);
    for (int i = 0; i < 3; ++i) `checkd(fail3[i], 0);
    for (int i = 0; i < 4; ++i) `checkd(cover3[i], 0);
    // An attempt started after the abort completes at its fourth tick.
    start = 1;
    @(negedge clk);
    start = 0;
    @(negedge clk);
    @(negedge clk);
    @(negedge clk);
    for (int i = 0; i < 3; ++i) begin
      `checkd(fail3[i], 1);
      `checkd(fail3_time[i], 125);
    end
    `checkd(cover3[0], 1);
    `checkd(cover3_time, 125);
    for (int i = 1; i < 4; ++i) `checkd(cover3[i], 0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
