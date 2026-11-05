// DESCRIPTION: Verilator: Nonblocking event triggers without --timing
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  event e;
  function void trig();
    ->>e;
  endfunction
endclass

module t;
  Cls c = new;
  event ea[2];
  int idx;
  event e;
  initial begin
    c.trig();
    ->>c.e;
    ->>ea[idx];
    ->>e;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
