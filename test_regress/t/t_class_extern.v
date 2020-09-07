// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  extern task extcls();
  extern function int extone();
endclass

function int Cls::extone();
   return 1;
endfunction

task Cls::extcls();
   $write("*-* All Finished *-*\n");
   $finish;
endtask

module t (/*AUTOARG*/);
   initial begin
      Cls c = new;
      if (c.extone() != 1) $stop;
      c.extcls();
   end
endmodule
