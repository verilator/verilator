// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off MULTITOP

module M;
class Cls;
   function string name;
      return $sformatf("m %m");
   endfunction
endclass
endmodule

module t (/*AUTOARG*/);
   string s;

   initial begin
      M::Cls p;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
