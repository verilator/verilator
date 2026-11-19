// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand(cl, field, cond) \
begin \
   automatic longint prev_result; \
   automatic int ok; \
   if (!bit'(cl.randomize())) `stop; \
   prev_result = longint'(field); \
   if (!(cond)) `stop; \
   repeat(20) begin \
      longint result; \
      if (!bit'(cl.randomize())) `stop; \
      result = longint'(field); \
      if (!(cond)) `stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) `stop; \
end
// verilog_format: on

class Item;
  rand int x;
  rand int w[*];
endclass

class Cls;
  rand int w[*];
  rand int u[2][*];
  rand Item items[1];
  constraint c {foreach (items[i]) items[i].x == 1;}
  function new();
    items[0] = new;
  endfunction
endclass

module t;
  initial begin
    automatic Cls c = new;
    automatic int ok;

    c.w[3] = 0;
    c.u[1][5] = 0;
    c.items[0].w[3] = 0;

    `check_rand(c, c.w[3], c.w.num() == 1);
    `check_rand(c, c.u[1][5], c.u[0].num() == 0 && c.u[1].num() == 1);
    ok = c.randomize();
    `checkd(ok, 1);
    `checkd(c.items[0].x, 1);
    `checkd(c.items[0].w.num(), 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
