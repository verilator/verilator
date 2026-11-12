// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Christopher Onyiuke
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand bit [7:0] x;
  rand bit [7:0] y;

  function bit [7:0] local_ref_func(bit [7:0] m);
    bit [7:0] tmp;
    tmp = m + 1;
    return tmp + tmp;  // return expr references local 'tmp' -> would dangle
  endfunction

  constraint c {x <= local_ref_func(y);}
endclass

module t;
  Cls obj;

  initial begin
    obj = new;
    void'(obj.randomize());
  end
endmodule