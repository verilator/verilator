// DESCRIPTION: Verilator: Nonblocking event triggers requiring --timing
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
  initial begin
    c.trig();
    ->>c.e;
    ->>ea[idx];
  end
endmodule
