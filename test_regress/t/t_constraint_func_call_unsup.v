// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Cls;
  rand bit [7:0] x;
  rand bit [7:0] y;

  function bit [7:0] complex_func(bit [7:0] m);
    if (m > 128)
      return m;
    else
      return m + 1;
  endfunction

  constraint c { x <= complex_func(y); }
endclass

module t;
  Cls obj;

  initial begin
    obj = new;
    void'(obj.randomize());
  end
endmodule
