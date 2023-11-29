// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  logic v;
  int num;

  initial begin
    num = 1;
    #1;
    if (v) $stop;
    num = 21;
    // Zero delay should postpone the execution and resume it after
    // evaluating combinational logic which would update `v`. However,
    // currently we can't postpone the resumption in the current timeframe
    // past the combinatorial logic evaluation as that is intertwined with
    // NBA evaluation and partitioned for multithreading. This causes `v`
    // to not have its value updated despite being checked after #0 delay.
    #0 if (v) $finish;
    $stop;
  end

  always_comb v = (num == 21);
endmodule
