// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   int sig;

   task foo;
      // verilator no_inline_task
      sig = '1;
   endtask

   initial begin
      foo();
   end

endmodule
