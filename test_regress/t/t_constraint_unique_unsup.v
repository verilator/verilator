// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

class C;
  rand bit [3:0] q[$];
  rand bit [3:0] arr[4];
  rand bit [3:0] x;
  rand bit sel;

  constraint sz {q.size() == 3;}
  // A container sized at run time has no element count to guard on
  constraint cond_dyn {
    if (sel) {
      unique {q};
    }
  }
  // A scalar cannot be made distinct from the elements of an array
  constraint scalar_vs_array {unique {x, arr};}
endclass

module t;
  initial begin
    automatic C c = new;
    void'(c.randomize());
  end
endmodule
