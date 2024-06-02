// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef enum int {
   RANDOMIZED = 20
} enumed_t;

class Cls;
   int       pre;
   rand enumed_t r;
   int       post;

   function void pre_randomize;
      if (pre != 0) $stop;
      $display("%d", r);
      if (r != enumed_t'(0)) $stop;
      if (post != 0) $stop;
      pre = 10;
   endfunction

   function void post_randomize;
      if (pre != 10) $stop;
      if (r != RANDOMIZED) $stop;
      if (post != 0) $stop;
      post = 30;
   endfunction
endclass

module t (/*AUTOARG*/);

   initial begin
      Cls c;
      int rand_result;

      c = new;
      rand_result = c.randomize();
      if (rand_result != 1) $stop;
      if (c.pre != 10) $stop;
      if (c.r != RANDOMIZED) $stop;
      if (c.post != 30) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
