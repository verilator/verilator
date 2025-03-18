// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
endinterface

class C;
   virtual A vif[6];
endclass

module tb_top();
   A a[6](), b[6]();
   C c, d;

   initial begin
      virtual A aa = a[0];

      c = new();
      c.vif = a;

      d = new();
      d.vif[0] = a[0];
      d.vif[1] = a[1];

      b = a;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
