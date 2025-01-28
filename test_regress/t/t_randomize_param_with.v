// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, constr, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   if (!bit'(cl.randomize() with { constr; })) $stop; \
   prev_result = longint'(field); \
   if (!(cond)) $stop; \
   repeat(9) begin \
      longint result; \
      if (!bit'(cl.randomize() with { constr; })) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class Cls #(int LIMIT = 3);
   rand int x;
   int      y = -100;
   constraint x_limit { x <= LIMIT; };
endclass

module t;
   initial begin
      Cls#() cd = new;
      Cls#(5) c5 = new;

      `check_rand(cd, cd.x, x > 0, cd.x > 0 && cd.x <= 3);
      `check_rand(cd, cd.x, x > y, cd.x > -100 && cd.x <= 3);
      if (cd.randomize() with {x > 3;} == 1) $stop;

      `check_rand(c5, c5.x, x > 0, c5.x > 0 && c5.x <= 5);
      `check_rand(c5, c5.x, x > y, c5.x > -100 && c5.x <= 5);
      if (c5.randomize() with {x >= 5;} == 0) $stop;
      if (c5.x != 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
