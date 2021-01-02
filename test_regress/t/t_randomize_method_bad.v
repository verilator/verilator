// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls1;
   function int randomize;
      return 1;
   endfunction
endclass

class Cls2;
   function void randomize(int x);
   endfunction
endclass

module t (/*AUTOARG*/);
endmodule
