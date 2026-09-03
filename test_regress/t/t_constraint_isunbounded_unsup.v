// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Keeps the generic fallback message reachable. Real values now get
// their own diagnostic and no longer trigger it.
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
