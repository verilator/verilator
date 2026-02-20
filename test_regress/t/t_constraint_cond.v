// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   automatic longint prev_result; \
   automatic int ok; \
   if (!bit'(cl.randomize())) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Cls;
  int d;
  rand int  y;
  rand bit  i;

  constraint q {
    if (i) {
      ((d == 0) ? y == 0 : 1'b1);
    }
  }
endclass

module t;
  Cls cls = new;
  initial begin
    `check_rand(cls, cls.y, cls.i == 0 || cls.y == 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
