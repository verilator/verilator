// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// Test automatic bins of an enum coverpoint: one bin per enumeration value

typedef enum logic [2:0] {
  A = 3'd5,
  B = 3'd1,
  C = 3'd7
} e_t;

class Item;
  e_t e;
  function e_t get_e();
    return e;
  endfunction
endclass

module t;
  e_t v;

  covergroup cg with function sample(Item item);
    cp_var: coverpoint v;
    cp_call: coverpoint item.get_e();
    cp_max: coverpoint v {option.auto_bin_max = 2;}
    cx: cross cp_var, cp_call;
  endgroup

  cg cg_i = new;

  initial begin
    Item item;
    item = new;
    v = B;
    item.e = C;
    cg_i.sample(item);
    v = C;
    item.e = C;
    cg_i.sample(item);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
