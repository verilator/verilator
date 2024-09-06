// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field, cond) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      if (!bit'(cl.randomize())) $stop; \
      result = longint'(field); \
      if (!(cond)) $stop; \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class C;
   int que[$] = '{3, 4, 5};
   int arr[3] = '{5, 6, 7};
   rand int x, y;
   constraint distrib {
       x dist {que};
       y dist {arr};
   };
endclass

module t;
   initial begin
      C c = new;
      `check_rand(c, c.x, 3 <= c.x && c.x <= 5);
      `check_rand(c, c.y, 5 <= c.y && c.y <= 7);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
