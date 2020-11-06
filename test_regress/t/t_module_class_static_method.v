// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//

module t (/*AUTOARG*/);

   class Cls;

      static function int static_task();
         return 42;
      endfunction

   endclass : Cls

   initial begin
      if (Cls::static_task() != 42) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
