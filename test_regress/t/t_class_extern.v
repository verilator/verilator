// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls #(type REQ=int);
  extern virtual function void extfunc();
endclass

function void Cls::extfunc();
   REQ t;  // Declared in class when externed, so must be found there
endfunction

module f;
   function void normal();
   endfunction
endmodule
