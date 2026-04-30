// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv, expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  class Cls;
    typedef enum {
      A = 10,
      B = 20,
      C = 30
    } en_t;
    en_t en;
  endclass

  class WideCls;
    typedef enum logic [95:0] {
      A = 96'h1,
      B = 96'h2
    } en_t;
    en_t en;
  endclass

  initial begin
    Cls c;
    WideCls w;
    string s;
    if (c.A != 10) $stop;
    c = new;
    c.en = c.B;
    if (c.en != 20) $stop;
    s = $sformatf("%p", c);
    `checks(s, "'{en:'h14}");

    w = new;
    w.en = w.B;
    s = $sformatf("%p", w);
    `checks(s, "'{en:'h2}");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
