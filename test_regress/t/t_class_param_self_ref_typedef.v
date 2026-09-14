// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 8.25.1: inside a parameterized class, a bare class name used
// without #() denotes the current specialization. A typedef reached through
// such a self reference must resolve against the specialization's type
// parameters, not the template's defaults. Covers both a typedef declared in
// the class itself and one inherited from a base class.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package pkg;
  class item_base #(type DATA = int);
    DATA value;
  endclass

  class holder #(type FIN = int);
    typedef item_base#(FIN) my_item_t;

    virtual function holder::my_item_t get_bare();
      my_item_t item;
      return item;
    endfunction
  endclass

  // Same, but the typedef is inherited from a base class instead.
  class base_holder #(type FIN = int);
    typedef item_base#(FIN) my_item_t;
  endclass

  class derived #(type FIN = int) extends base_holder#(FIN);
    virtual function derived::my_item_t get_bare();
      my_item_t item;
      return item;
    endfunction
  endclass
endpackage

module t;
  import pkg::*;

  // Non-default parameters, so the specialization differs from the template
  // default and the bug is observable.
  holder#(byte) h;
  derived#(shortint) d;

  initial begin
    automatic holder#(byte)::my_item_t got;
    automatic derived#(shortint)::my_item_t got_inherited;
    h = new;
    got = h.get_bare();
    `checkd($bits(got.value), 8);
    d = new;
    got_inherited = d.get_bare();
    `checkd($bits(got_inherited.value), 16);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
