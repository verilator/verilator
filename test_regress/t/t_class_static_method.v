// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;

   static task static_task(int x);
      $write("Called static task: %d\n", x);
   endtask

   static function int static_function(int x);
      $write("Called static function: %d\n", x);
      return 42;
   endfunction

endclass : Cls

module t (/*AUTOARG*/);

   initial begin
      int x;
      Cls::static_task(16);
      x = Cls::static_function(23);
      $write("Static function result: %d\n", x);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
