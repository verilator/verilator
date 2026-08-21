// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {rand bit [31:0] x;} Bar;

class Foo;
  rand Bar bar0[];
  rand Bar bar1[$];
  constraint c0 {
    foreach (bar0[i]) {
      if (i > 0) bar0[i].x > bar0[i-1].x;
    }
  }
  constraint c1 {
    foreach (bar1[i]) {
      if (i > 0) bar1[i].x > bar1[i-1].x;
    }
  }
  function new();
    bar0 = new[1];
    bar1.push_back('{0});
  endfunction
endclass

module t;
  initial begin
    static Foo foo = new;
    int randomize_result;
    `checkd(foo.bar0.size(), 1);
    `checkd(foo.bar1.size(), 1);
    `checkd(foo.bar0[0].x, 0);
    `checkd(foo.bar1[0].x, 0);
    repeat (100) begin
      randomize_result = foo.randomize();
      `checkd(randomize_result, 1);
      `checkd(foo.bar0.size(), 1);
      `checkd(foo.bar1.size(), 1);
      // Noting prevents x == 0 but it is pretty safe to assume that it won't be a zero (1/2^32)
      `checkd(foo.bar0[0].x != 0, 1);
      `checkd(foo.bar1[0].x != 0, 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
