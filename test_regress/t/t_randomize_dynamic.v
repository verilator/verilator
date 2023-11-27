// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

int N = 10;

class Cls;
   rand bit [127:0] dyn[];
   function new;
      dyn = new[N];
   endfunction
endclass

module t;
   initial begin
      Cls c = new;
      for (int i = 0; i < N; i++) begin
         `check_rand(c, c.dyn[i]);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
