// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand bit [7:0] x;
  rand bit [7:0] y;

  function bit [7:0] control_func(bit [7:0] m);
    bit [7:0] tmp;
    if (m > 0) tmp = m + 1;
    else tmp = m + 2;
    return tmp;
  endfunction

  function bit [7:0] static_func(bit [7:0] m);
    static bit [7:0] tmp = 1;
    return tmp + m;
  endfunction

  function bit [7:0] static_reset_func(bit [7:0] m);
    static bit [7:0] tmp;
    return tmp + m;
  endfunction

  constraint c {x <= control_func(y);}
  constraint d {x <= static_func(y);}
  constraint e {x <= static_reset_func(y);}
endclass

module t;
  Cls obj;

  initial begin
    obj = new;
    void'(obj.randomize());
  end
endmodule
