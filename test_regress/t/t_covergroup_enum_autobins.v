// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 David Harris
// SPDX-License-Identifier: CC0-1.0

// Test automatic bins of an enum coverpoint: one bin per enumeration value

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum logic [2:0] {
  A = 3'd5,
  B = 3'd1,
  C = 3'd7
} e_t;

typedef enum logic [59:0] {
  E01 = 60'h1,
  ELARGE = 60'h1234_4567_abcd
} wide_t;

typedef enum bit [2:0] {
  E2_A = 3'd2,
  E2_B = 3'd6
} e2_t;

class Item;
  e_t e;
  function e_t get_e();
    return e;
  endfunction
endclass

module t;
  e_t v;
  wide_t w;
  logic select;

  covergroup cg with function sample(Item item);
    cp_var: coverpoint v;
    cp_call: coverpoint item.get_e();
    cp_max: coverpoint v {option.auto_bin_max = 2;}
    cx: cross cp_var, cp_call;
    cp_wide: coverpoint w;
  endgroup

  covergroup cg_cond;
    cp_cond: coverpoint (select ? E2_A : E2_B);
  endgroup

  cg cg_i = new;
  cg_cond cg_cond_i = new;

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

    select = 1;
    cg_cond_i.sample();
    `checkr(cg_cond_i.get_inst_coverage(), 50.0);
    select = 0;
    cg_cond_i.sample();
    `checkr(cg_cond_i.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
