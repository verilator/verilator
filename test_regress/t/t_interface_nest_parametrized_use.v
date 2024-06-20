// DESCRIPTION: Verilator: SystemVerilog nested interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Baruch Sterin.
// SPDX-License-Identifier: CC0-1.0

interface A #(WIDTH);
   logic [WIDTH-1:0] x;
endinterface

interface B;
   A #(32) a();
endinterface

module M(A a);
endmodule

module top;
   B b();
   M m(b.a);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
