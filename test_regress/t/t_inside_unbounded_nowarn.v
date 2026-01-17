// DESCRIPTION: Verilator: Test for [$:$] with warning suppressed
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

module t_inside_unbounded_nowarn;
  initial begin
    int value;
    value = 50;
    // [$:$] is always true - warning suppressed with -Wno-INSIDETRUE
    if (!(value inside {[$:$]})) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
