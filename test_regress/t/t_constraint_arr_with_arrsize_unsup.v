// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Sub;
  rand int arr[];

  function new();
    arr = new[10];
  endfunction
endclass

class Indep;
  rand int val;
  Sub s[];

  function new();
    s = new[10];
  endfunction
endclass

class Cls;
  function int randomize_gpr(Indep i);
    return (i.randomize() with {
      if (i.s[0].arr.size > 0) {
        i.val inside {i.s[0].arr};
      }
    });
  endfunction
endclass

module t;
  Cls c;
  Indep i;

  initial begin
    c = new;
    i = new;

    c.randomize_gpr(i);
  end
endmodule
