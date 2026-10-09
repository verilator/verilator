// DESCRIPTION: Verilator: segfault in V3Width processFTaskRefArgs
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Base;
endclass

class Caller;
  function void f(input string s);
    $display("%s", s);
  endfunction
endclass

module t;
  initial begin
    automatic Caller c = new;
    automatic Base seq = new;
    // Passing a class handle where a 'string' port is expected:
    c.f(seq);
  end
endmodule
