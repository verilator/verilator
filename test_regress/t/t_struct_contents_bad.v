// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   typedef enum logic [1:0] { ZERO, ONE } enum_t;

   typedef struct { bit a; } struct_unpacked_t;
   typedef union { bit a; } union_unpacked_t;

class Cls;
   bit a;
endclass

   // IEEE 1800-2023 7.2.1
   typedef struct packed {
      real        r;  // BAD
      // verilator lint_off SHORTREAL
      shortreal   sr; // BAD
      realtime    rt; // BAD
      chandle     ch; // BAD
      string      s; // BAD
      event       e; // BAD
      struct_unpacked_t sp;  // BAD
      union_unpacked_t up;   // BAD
      int uarray[2];   // BAD
      Cls c;  // BAd
   } illegal_t;

   initial begin
      $stop;
   end

endmodule
