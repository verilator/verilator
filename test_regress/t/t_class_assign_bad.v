// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass : Cls

module t (/*AUTOARG*/);
   Cls c;

   task t(Cls c); endtask

   initial begin
      c = 0;
      c = 1;
      t(0);
      t(1);
   end
endmodule
