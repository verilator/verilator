// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module top;
  logic v;
  int num;
  time t;

  initial begin
    num = 1;
    #1;
    if (v) $stop;
    num = 21;
    t = $time;
    // Zero delay should postpone the execution and resume it after
    // evaluating combinational logic which would update `v`. However,
    // currently we can't postpone the resumption in the current timeframe
    // past the combinatorial logic evaluation as that is intertwined with
    // NBA evaluation and partitioned for multithreading. This causes `v`
    // to not have its value updated despite being checked after #0 delay.
    #0;
    if (!v) $stop;
    if (t != $time) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always_comb v = (num == 21);
endmodule
