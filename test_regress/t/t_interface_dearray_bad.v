// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
endinterface

typedef virtual A a_t;
typedef a_t a_array_t[6];

class C;
   a_array_t vif;
endclass

module tb_top();
   A a[6](), b[7](), f[6]();
   C c, d, e;
   a_array_t g;

   initial begin
      a = f;

      c = new();
      c.vif = b;

      d = new();

      for (int i = 0; i < 6; ++i) begin
         d.vif[i] = a[i];
      end

      e = new();
      e.vif = b[0:5];

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
