// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// An illegal bin of a 'with' filter is hit when its guard, evaluated once, is true

module t;
  bit [2:0] value;
  int calls;

  // True on the first call only
  function automatic bit first_call();
    ++calls;
    return calls == 1;
  endfunction

  covergroup cg;
    cp: coverpoint value {
      bins valid = {[0 : 3]};
      illegal_bins bad = {[4 : 7]} with (item != 5) iff (first_call());
    }
  endgroup

  cg inst = new;

  initial begin
    value = 4;
    inst.sample();  // <--- Bad: illegal
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
