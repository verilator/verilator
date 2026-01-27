// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off MULTITOP

module M;
class Cls;
   function string name;
      return $sformatf("m %m");
   endfunction
endclass
endmodule

module t;
   string s;

   initial begin
      M::Cls p;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
