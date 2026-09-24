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

typedef enum logic [59:0] {
  E01 = 60'h1,
  ELARGE = 60'h1234_4567_abcd
} wide_t;

class Item;
  e_t e;
  function e_t get_e();
    return e;
  endfunction
endclass

module t;
  e_t v;
  wide_t w;

  covergroup cg with function sample(Item item);
    cp_var: coverpoint v;
    cp_call: coverpoint item.get_e();
    cp_max: coverpoint v {option.auto_bin_max = 2;}
    cx: cross cp_var, cp_call;
    cp_wide: coverpoint w;
  endgroup

  cg cg_i = new;

  initial begin
    Item item;
    item = new;
    v = B;
    item.e = C;
    w = ELARGE;
    cg_i.sample(item);
    v = C;
    item.e = C;
    w = wide_t'(60'h1_0000_0001);  // not an enum value; aliases E01 in the low 32 bits
    cg_i.sample(item);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
