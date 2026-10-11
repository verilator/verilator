// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  class C;
  endclass

  bit [1:0] a;
  bit [1:0] b;
  C object;
  int array_value[2];

  covergroup cg;
    aa: coverpoint a;
    bb: coverpoint b;
    xx: cross aa, bb{
      bins handle = xx with (object);  // <--- Bad: not integral
      bins array = xx with (array_value);  // <--- Bad: not integral
      bins real_value = xx with (0.5);
    }
  endgroup

  cg inst = new;
endmodule
