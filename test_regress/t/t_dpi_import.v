// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VCS
 `define NO_SHORTREAL
 `define NO_TIME
`endif
`ifdef NC
 `define NO_SHORTREAL
 `define NO_TIME
`endif
`ifdef VERILATOR  // Unsupported
 `define NO_SHORTREAL
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   typedef struct packed { bit [47:0] lo; bit [47:0] hi; } str_t;
   typedef struct packed { int a; int b; } substr_t;

   // Allowed import return types:
   //         void, byte, shortint, int, longint, real, shortreal, chandle, and string
   //         Scalar bit and logic
   //
   // Allowed argument types:
   //         Same as above plus packed arrays

   import "DPI-C" pure function bit          dpii_f_bit      (input bit          i);
   import "DPI-C" pure function bit [8-1:0]  dpii_f_bit8     (input bit [8-1:0]  i);
   import "DPI-C" pure function bit [9-1:0]  dpii_f_bit9     (input bit [9-1:0]  i);
   import "DPI-C" pure function bit [16-1:0] dpii_f_bit16    (input bit [16-1:0] i);
   import "DPI-C" pure function bit [17-1:0] dpii_f_bit17    (input bit [17-1:0] i);
   import "DPI-C" pure function bit [32-1:0] dpii_f_bit32    (input bit [32-1:0] i);
   // Illegal to return > 32 bits, so we use longint
   import "DPI-C" pure function longint      dpii_f_bit33    (input bit [33-1:0] i);
   import "DPI-C" pure function longint      dpii_f_bit64    (input bit [64-1:0] i);
   import "DPI-C" pure function int          dpii_f_int      (input int          i);
   import "DPI-C" pure function byte         dpii_f_byte     (input byte         i);
   import "DPI-C" pure function shortint     dpii_f_shortint (input shortint     i);
   import "DPI-C" pure function longint      dpii_f_longint  (input longint      i);
   import "DPI-C" pure function chandle      dpii_f_chandle  (input chandle      i);
   import "DPI-C" pure function string       dpii_f_string   (input string       i);
   import "DPI-C" pure function real         dpii_f_real     (input real         i);
`ifndef NO_SHORTREAL
   import "DPI-C" pure function shortreal    dpii_f_shortreal(input shortreal    i);
`endif

   import "DPI-C" pure function void dpii_v_bit      (input bit       i, output bit       o);
   import "DPI-C" pure function void dpii_v_int      (input int       i, output int       o);
   import "DPI-C" pure function void dpii_v_byte     (input byte      i, output byte      o);
   import "DPI-C" pure function void dpii_v_shortint (input shortint  i, output shortint  o);
   import "DPI-C" pure function void dpii_v_longint  (input longint   i, output longint   o);
   import "DPI-C" pure function void dpii_v_struct   (input str_t     i, output str_t     o);
   import "DPI-C" pure function void dpii_v_substruct(input substr_t  i, output int       o);
   import "DPI-C" pure function void dpii_v_chandle  (input chandle   i, output chandle   o);
   import "DPI-C" pure function void dpii_v_string   (input string    i, inout  string    o);
   import "DPI-C" pure function void dpii_v_real     (input real      i, output real      o);

   import "DPI-C" pure function void dpii_v_uint     (input int unsigned i,      output int unsigned o);
   import "DPI-C" pure function void dpii_v_ushort   (input shortint unsigned i, output shortint unsigned o);
   import "DPI-C" pure function void dpii_v_ulong    (input longint unsigned i,  output longint unsigned o);
`ifndef NO_SHORTREAL
   import "DPI-C" pure function void dpii_v_shortreal(input shortreal i, output shortreal o);
`endif
   import "DPI-C" pure function void dpii_v_bit64    (input bit [64-1:0] i, output bit [64-1:0] o);
   import "DPI-C" pure function void dpii_v_bit95    (input bit [95-1:0] i, output bit [95-1:0] o);
   import "DPI-C" pure function void dpii_v_bit96    (input bit [96-1:0] i, output bit [96-1:0] o);

   import "DPI-C" pure function void dpii_v_reg      (input reg i, output reg o);
   import "DPI-C" pure function void dpii_v_reg15    (input reg [14:0] i, output reg [14:0] o);
   import "DPI-C" pure function void dpii_v_reg95    (input reg [94:0] i, output reg [94:0] o);
   import "DPI-C" pure function void dpii_v_integer  (input integer   i, output integer   o);
`ifndef NO_TIME
   import "DPI-C" pure function void dpii_v_time     (input time      i, output time      o);
`endif

   import "DPI-C" pure function int dpii_f_strlen (input string i);

   import "DPI-C" function void dpii_f_void ();

   // Try a task
   import "DPI-C" task dpii_t_void ();
   import "DPI-C" context task dpii_t_void_context ();

   import "DPI-C" task dpii_t_int (input int       i, output int       o);

   // Try non-pure, aliasing with name
   import "DPI-C" dpii_fa_bit =  function int oth_f_int1(input int i);
   import "DPI-C" dpii_fa_bit =  function int oth_f_int2(input int i);

   bit          i_b,    o_b;
   bit [7:0]    i_b8;
   bit [8:0]    i_b9;
   bit [15:0]   i_b16;
   bit [16:0]   i_b17;
   bit [31:0]   i_b32;
   bit [32:0]   i_b33,  o_b33;
   bit [63:0]   i_b64,  o_b64;
   bit [94:0]   i_b95,  o_b95;
   bit [95:0]   i_b96,  o_b96;

   int          i_i,    o_i;
   byte         i_y,    o_y;
   shortint     i_s,    o_s;
   longint      i_l,    o_l;
   str_t        i_t,    o_t;
   substr_t     i_ss;
   int          o_ss;
   int unsigned         i_iu,   o_iu;
   shortint unsigned    i_su,   o_su;
   longint unsigned     i_lu,   o_lu;
   // verilator lint_off UNDRIVEN
   chandle      i_c,    o_c;
   string       i_n,    o_n;
   // verilator lint_on UNDRIVEN
   real         i_d,    o_d;
`ifndef NO_SHORTREAL
   shortreal    i_f,    o_f;
`endif

   reg          i_r, o_r;
   reg [14:0]   i_r15, o_r15;
   reg [94:0]   i_r95, o_r95;
   integer      i_in,   o_in;
   time         i_tm,   o_tm;

   bit [94:0] wide;

   bit [6*8:1] string6;

   initial begin
      wide = 95'h15caff7a73c48afee4ffcb57;

      i_b  = 1'b1;
      i_b8  = {1'b1,wide[8-2:0]};
      i_b9  = {1'b1,wide[9-2:0]};
      i_b16 = {1'b1,wide[16-2:0]};
      i_b17 = {1'b1,wide[17-2:0]};
      i_b32 = {1'b1,wide[32-2:0]};
      i_b33 = {1'b1,wide[33-2:0]};
      i_b64 = {1'b1,wide[64-2:0]};
      i_b95 = {1'b1,wide[95-2:0]};
      i_b96 = {1'b1,wide[96-2:0]};

      i_i = {1'b1,wide[32-2:0]};
      i_iu= {1'b1,wide[32-2:0]};
      i_y = {1'b1,wide[8-2:0]};
      i_s = {1'b1,wide[16-2:0]};
      i_su= {1'b1,wide[16-2:0]};
      i_l = {1'b1,wide[64-2:0]};
      i_lu= {1'b1,wide[64-2:0]};
      i_t = {1'b1,wide[95-1:0]};
      i_d = 32.1;

      i_ss.a = 32'h054321ab;
      i_ss.b = 32'h05a43b21;

`ifndef NO_SHORTREAL
      i_f = 30.2;
`endif

      i_r = '0;
      i_r15 = wide[14:0];
      i_r95 = wide[94:0];
      i_in = -1234;
      i_tm = 62;

      if (dpii_f_bit     (i_b) !== ~i_b) $stop;
      if (dpii_f_bit8    (i_b8) !== ~i_b8) $stop;
      if (dpii_f_bit9    (i_b9) !== ~i_b9) $stop;
      if (dpii_f_bit16   (i_b16) !== ~i_b16) $stop;
      if (dpii_f_bit17   (i_b17) !== ~i_b17) $stop;
      if (dpii_f_bit32   (i_b32) !== ~i_b32) $stop;

      // These return different sizes, so we need to truncate
      // verilator lint_off WIDTH
      o_b33 = dpii_f_bit33   (i_b33);
      o_b64 = dpii_f_bit64   (i_b64);
      // verilator lint_on WIDTH
      if (o_b33 !== ~i_b33) $stop;
      if (o_b64 !== ~i_b64) $stop;

      if (dpii_f_bit      (i_b) !== ~i_b) $stop;
      if (dpii_f_int      (i_i) !== ~i_i) $stop;
      if (dpii_f_byte     (i_y) !== ~i_y) $stop;
      if (dpii_f_shortint (i_s) !== ~i_s) $stop;
      if (dpii_f_longint  (i_l) !== ~i_l) $stop;
      if (dpii_f_chandle  (i_c) !== i_c) $stop;
      if (dpii_f_string   (i_n) != i_n) $stop;
      if (dpii_f_real     (i_d) != i_d+1.5) $stop;
`ifndef NO_SHORTREAL
      if (dpii_f_shortreal(i_f) != i_f+1.5) $stop;
`endif

      dpii_v_bit      (i_b,o_b); if (o_b !== ~i_b) $stop;
      dpii_v_int      (i_i,o_i); if (o_i !== ~i_i) $stop;
      dpii_v_byte     (i_y,o_y); if (o_y !== ~i_y) $stop;
      dpii_v_shortint (i_s,o_s); if (o_s !== ~i_s) $stop;
      dpii_v_longint  (i_l,o_l); if (o_l !== ~i_l) $stop;
      dpii_v_uint     (i_iu,o_iu); if (o_iu !== ~i_iu) $stop;
      dpii_v_ushort   (i_su,o_su); if (o_su !== ~i_su) $stop;
      dpii_v_ulong    (i_lu,o_lu); if (o_lu !== ~i_lu) $stop;
      dpii_v_struct   (i_t,o_t); if (o_t !== ~i_t) $stop;
      dpii_v_substruct(i_ss,o_ss); if (o_ss !== i_ss.a - i_ss.b) $stop;
      dpii_v_chandle  (i_c,o_c); if (o_c !== i_c) $stop;
      dpii_v_string   (i_n,o_n); if (o_n != i_n) $stop;
      dpii_v_real     (i_d,o_d); if (o_d != i_d+1.5) $stop;
`ifndef NO_SHORTREAL
      dpii_v_shortreal(i_f,o_f); if (o_f != i_f+1.5) $stop;
`endif
      dpii_v_bit64    (i_b64,o_b64); if (o_b64 !== ~i_b64) $stop;
      dpii_v_bit95    (i_b95,o_b95); if (o_b95 !== ~i_b95) $stop;
      dpii_v_bit96    (i_b96,o_b96); if (o_b96 !== ~i_b96) $stop;

      dpii_v_reg      (i_r,o_r); if (o_r !== ~i_r) $stop;
      dpii_v_reg15    (i_r15,o_r15); if (o_r15 !== ~i_r15) $stop;
      dpii_v_reg95    (i_r95,o_r95); if (o_r95 !== ~i_r95) $stop;
      dpii_v_integer  (i_in,o_in); if (o_in != ~i_in) $stop;
`ifndef NO_TIME
      dpii_v_time     (i_tm,o_tm); if (o_tm != ~i_tm) $stop;
`endif

      if (dpii_f_strlen ("")!=0) $stop;
      if (dpii_f_strlen ("s")!=1) $stop;
      if (dpii_f_strlen ("st")!=2) $stop;
      if (dpii_f_strlen ("str")!=3) $stop;
      if (dpii_f_strlen ("stri")!=4) $stop;
      if (dpii_f_strlen ("string_l")!=8) $stop;
      if (dpii_f_strlen ("string_len")!=10) $stop;
      string6 = "hello6";
`ifdef VERILATOR
      string6 = $c48(string6); // Don't optimize away - want to see the constant conversion function
`endif
      if (dpii_f_strlen (string6) != 6) $stop;

      dpii_f_void();
      dpii_t_void();
      dpii_t_void_context();

      i_i = 32'h456789ab;
      dpii_t_int     (i_i,o_i); if (o_b !== ~i_b) $stop;

      // Check alias
      if (oth_f_int1(32'd123) !== ~32'd123) $stop;
      if (oth_f_int2(32'd124) !== ~32'd124) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

   always @ (posedge clk) begin
      i_b <= ~i_b;
      // This once mis-threw a BLKSEQ warning
      dpii_v_bit (i_b,o_b); if (o_b !== ~i_b) $stop;
   end

endmodule
