// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005 by Thomas Dzetkulic.
// SPDX-License-Identifier: CC0-1.0

module fnor2(f, a, b);
   parameter W = 1;

   output [W-1:0]f;
   input [W-1:0] a, b;

   supply0       gnd;
   supply1       vcc;

   generate
      genvar     i;
      for (i = 0; i < W; i = i + 1) begin
         wire w;
         pmos(f[i], w, a[i]);
         pmos(w, vcc, b[i]);
         nmos(f[i], gnd, a[i]);
         nmos(f[i], gnd, b[i]);
      end
   endgenerate
endmodule

module t(f, a, b);
   output [1:0] f;
   input [1:0]  a, b;

   fnor2 #(2) n(f, a, b);
endmodule
