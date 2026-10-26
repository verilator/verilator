// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Invalid types of coverpoint and cross bin 'with' filters (IEEE 1800-2023 19.5.1.1)

module t;
  real r;
  bit [3:0] a;
  string s = "x";
  covergroup cg;
    // Not allowed for a real coverpoint, nor other non-integral ones
    rr: coverpoint r {
      bins b = {[0 : 3]} with (item > 1);
    }
    ss: coverpoint s {
      bins b = {"a"} with (1);
    }
    // The result must be assignment compatible with an integral type
    aa: coverpoint a {
      bins b[] = {[0 : 3]} with (s);
    }
  endgroup
  class C;
  endclass
  C object;
  int array_value[2];
  // Likewise a cross bin's
  covergroup cg_cross;
    aa: coverpoint a;
    bb: coverpoint a;
    xx: cross aa, bb{
      bins handle = xx with (object);  // <--- Bad: not integral
      bins array = xx with (array_value);  // <--- Bad: not integral
      bins real_value = xx with (0.5);
    }
  endgroup
  cg inst = new;
  cg_cross cross_inst = new;
  initial $finish;
endmodule
