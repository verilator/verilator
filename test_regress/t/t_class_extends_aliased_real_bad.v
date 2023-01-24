// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   class bar #(type T) extends T;
   endclass

   typedef real real_t;

   bar #(real_t) bar_real_t;

   initial begin
      $stop;
   end
endmodule
