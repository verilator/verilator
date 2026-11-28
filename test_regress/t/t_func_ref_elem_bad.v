// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef int aa_t[int];
typedef int wc_t[*];
typedef int q_t[$];

class Cls;
  function void bump(ref int x);
    x++;
  endfunction
  function aa_t get_aa();
    aa_t r;
    return r;
  endfunction
  function wc_t get_wc();
    wc_t r;
    return r;
  endfunction
  function q_t get_q();
    q_t r;
    return r;
  endfunction
  function int get_v();
    return 0;
  endfunction
endclass

module t;
  Cls cls;
  initial begin
    cls = new;
    cls.bump(cls.get_aa()[1]);
    cls.bump(cls.get_wc()[1]);
    cls.bump(cls.get_q()[0]);
    cls.bump(cls.get_v());
  end
endmodule
