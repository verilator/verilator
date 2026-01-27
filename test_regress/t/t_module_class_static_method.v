// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

module t;

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
