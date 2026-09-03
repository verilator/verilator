// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Keeps the generic constraint-expression fallback message reachable by a
// non-real construct, now that real values get their own diagnostic.
class C;
  rand int x;
  constraint c { !$isunbounded(x); }
endclass

module t;
  initial begin
    C obj;
    obj = new;
    if (obj.randomize() == 0) $stop;
  end
endmodule
