// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
   function int rand_mode(bit onoff);
      return 1;
   endfunction
   function int constraint_mode(bit onoff);
      return 1;
   endfunction
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
   end
endmodule
