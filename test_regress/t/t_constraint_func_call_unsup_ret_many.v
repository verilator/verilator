// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand bit [7:0] x;
  rand bit [7:0] y;

  function bit [7:0] ret_many_func(bit [7:0] m);
    ret_many_func = m + 1;
    ret_many_func = m + 2;
    ret_many_func = m + 3;
    return ret_many_func;
  endfunction

  constraint c {x <= ret_many_func(y);}
endclass

module t;
  Cls obj;

  initial begin
    obj = new;
    void'(obj.randomize());
  end
endmodule
