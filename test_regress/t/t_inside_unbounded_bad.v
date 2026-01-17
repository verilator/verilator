// DESCRIPTION: Verilator: Test for unsupported [$:$] in inside range
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

module t_inside_unbounded_bad;
  initial begin
    int value;
    value = 50;
    // [$:$] should warn - always true
    if (value inside {[$:$]}) $display("PASS");
    $finish;
  end
endmodule
