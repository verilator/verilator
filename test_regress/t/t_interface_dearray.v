// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface A;
endinterface

typedef virtual A a_t;
typedef a_t a_array_t[6];

class B;
  function new(virtual A va);
  endfunction
endclass

class C;
   a_array_t vif;

   function void set(int index, a_t iface);
      vif[index] = iface;
   endfunction
endclass

module tb_top();
   A a[6]();
   C c, d, e;
   a_array_t g;

   initial begin
      static a_t aa = a[0];

      B b = new(a[0]);

      c = new();
      c.vif = a;

      d = new();
      d.set(0, a[0]);
      d.vif[1] = a[1];

      g[0] = a[0];
      g = a;

      d.vif[0] = g[0];
      d.vif = g;

      e = new();

      for (int i = 0; i < 6; ++i) begin
         e.vif[i] = g[i];
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
