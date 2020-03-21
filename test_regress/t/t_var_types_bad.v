// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   // IEEE: integer_atom_type
   byte         d_byte;
   shortint     d_shortint;
   int          d_int;
   longint      d_longint;
   integer      d_integer;
   time         d_time;
   chandle      d_chandle;

   // IEEE: integer_atom_type
   bit          d_bit;
   logic        d_logic;
   reg          d_reg;

   bit [0:0]    d_bit1;
   logic [0:0]  d_logic1;
   reg [0:0]    d_reg1;

   bit          d_bitz;
   logic        d_logicz;
   reg          d_regz;

   // IEEE: non_integer_type
   //UNSUP shortreal    d_shortreal;
   real         d_real;
   realtime     d_realtime;

   initial begin
      // below errors might cause spurious warnings
      // verilator lint_off WIDTH
      d_bitz[0] = 1'b1;         // Illegal range
      d_logicz[0] = 1'b1;       // Illegal range
      d_regz[0] = 1'b1;         // Illegal range

`ifndef VERILATOR //UNSUPPORTED, it's just a 64 bit int right now
      d_chandle[0] = 1'b1;      // Illegal
`endif
      d_real[0] = 1'b1;         // Illegal
      d_realtime[0] = 1'b1;     // Illegal
      // verilator lint_on WIDTH

      d_byte[0] = 1'b1;         // OK
      d_shortint[0] = 1'b1;     // OK
      d_int[0] = 1'b1;          // OK
      d_longint[0] = 1'b1;      // OK
      d_integer[0] = 1'b1;      // OK
      d_time[0] = 1'b1;         // OK

      d_bit1[0] = 1'b1;         // OK
      d_logic1[0] = 1'b1;       // OK
      d_reg1[0] = 1'b1;         // OK
   end
endmodule
