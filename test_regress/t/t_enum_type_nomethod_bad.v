// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   typedef enum [3:0] {
                       E01 = 1
                       } my_t;

   my_t e;

   initial begin
      e.bad_no_such_method();
      $stop;
   end

endmodule
