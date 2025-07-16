// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


package Pkg;
endpackage

class C;
endclass

module t;
   C c;
   initial begin
      c = Pkg::new;  // Bad
   end
endmodule
