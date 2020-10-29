// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   static task static_task();
      $write("Called static task\n");
   endtask

   static function void static_function();
      $write("Called static function\n");
   endfunction
endclass : Cls

module t (/*AUTOARG*/);

   initial begin
      Cls::static_task();
      Cls::static_function();
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
