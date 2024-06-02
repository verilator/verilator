// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

module t;
   wire a, b;
   udp i_udp (a, b);
endmodule

primitive udp #(
    parameter A = 1
) (o, a);
   output o;
   input  a;
   table
      //o a
      0 :  1;
      1 :  0;
   endtable
endprimitive
