// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   typedef enum logic [1:0] { ZERO, ONE } enum_t;

   typedef struct packed { bit a; } struct_packed_t;
   typedef union packed { bit a; } union_packed_t;

   //IEEE 1800-2023 7.2.1
   // These are all legal
   typedef struct packed {
      enum_t e;
      shortint si;
      int      it;
      longint  li;
      byte     by;
      bit      bi;
      logic    lo;
      reg      rg;
      integer  in;
      time     tim;
      struct_packed_t sp;
      union_packed_t up;
      bit [1:0][2:0] bit_array;
   } legal_t;
   legal_t legal;

   initial begin
      legal.e = ONE;
      legal.si = 1;
      legal.it = 2;
      legal.li = 3;
      legal.by = 4;
      legal.bi = 1'b1;
      legal.lo = 1'b1;
      legal.rg = 1'b1;
      legal.in = 6;
      legal.tim = 7;
      legal.sp.a = 1'b1;
      legal.up.a = 1'b1;
      legal.bit_array[1][1] = 1'b1;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
