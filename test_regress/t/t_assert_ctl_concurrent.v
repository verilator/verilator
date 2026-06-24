// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;

  bit clock = 1'b0;
  bit start = 1'b0;
  bit done = 1'b0;
  int concurrent_fails = 0;

  initial begin
    $asserton;

    @(negedge clock);
    start = 1'b1;
    done = 1'b0;

    @(negedge clock);
    start = 1'b0;
    $assertkill;
    $asserton;

    @(posedge clock);
    #1;
    if (concurrent_fails != 0) $stop;

    @(negedge clock);
    start = 1'b1;
    done = 1'b0;

    @(negedge clock);
    start = 1'b0;

    @(posedge clock);
    #1;
    if (concurrent_fails != 1) $stop;

    $assertcontrol(5, 1, 1);
    $asserton;

    $display("%t: finish", $time);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always #5 clock = ~clock;

  assert_test :
  assert property (@(posedge clock) start |-> ##1 done)
  else concurrent_fails++;

endmodule
