// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
  extern function void extfunc();
endclass

function void Cls::extfunc();
   $write("*-* All Finished *-*\n");
   $finish;
endfunction

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c.extfunc();
   end
endmodule
