// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  function int do_randomize();
    int flocal, success;
    success = std::randomize(flocal);
    if (success !== 1) $stop;
    do_randomize = flocal;
  endfunction
endclass

module t;
  int r1, r2, r3;
  initial begin
    Cls c;
    c = new;
    r1 = c.do_randomize();
    r2 = c.do_randomize();
    r3 = c.do_randomize();
    $display("%x %x %x", r1, r2, r3);
    if (r1 == r2 && r2 == r3) $stop;  // Not impossible but 2^63 odds of failure
    $finish;
  end
endmodule
