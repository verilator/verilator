// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
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

class C;
   rand int x;
   int q[$] = {0, 0, 0, 0, 0};
   constraint fore {
      x < 7;
      foreach(q[i])
         x > i;
      foreach(q[i])  // loop again with the same index name
         x > i;
   };
endclass

class D;
   rand bit posit;
   rand int x;
   int o[$];  // empty
   int p[$] = {1};
   int q[$] = {0, 0, 0, 0, 0};
   constraint fore {
      if (posit == 1) {
         foreach(o[i]) o[i] > 0;
      }
      if (posit == 1) {
         foreach(p[i]) p[i] > 0;
      }
      if (posit == 1) {
         x < 7;
         foreach(q[i])
            x > i;
      } else {
         x > -3;
         foreach(q[i])
            x < i;
      }
   };
endclass

module t;
   initial begin
      C c = new;
      D d = new;
      `check_rand(c, c.x, 4 < c.x && c.x < 7);
      `check_rand(d, d.posit, (d.posit ? 4 : -3) < d.x && d.x < (d.posit ? 7 : 0));
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
