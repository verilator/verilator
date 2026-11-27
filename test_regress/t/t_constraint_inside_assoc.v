// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
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

class Cls;
  rand int x;
  rand int y;
  rand int vals[int];
  int names[string];
  int wild[*];
  constraint c_vals {
    foreach (vals[i]) vals[i] == i;
    x inside {vals};
  }
  constraint c_names {x inside {names};}
  constraint c_wild {y inside {wild};}

  function new();
    for (int i = 0; i < 16; i++) vals[i] = 0;
    names = '{default: 2};
    for (int i = 1; i < 14; i += 2) names[$sformatf("k%0d", i)] = i;
    for (int i = 1; i <= 4; i++) wild[i * 3] = i * 8;
  endfunction
endclass

module t;
  initial begin
    automatic Cls c = new;

    `check_rand(c, c.x, c.x % 2 == 1 && c.x >= 1 && c.x <= 13 && c.vals[c.x] == c.x);
    `check_rand(c, c.y, c.y % 8 == 0 && c.y >= 8 && c.y <= 32);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
